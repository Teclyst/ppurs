open Ast
open Typing
open Format
open X86_64
open Primitives

type local_env = int Smap.t

let popn n =
  addq (imm n) !%rsp
let pushn n =
  subq (imm n) !%rsp

(* New Asts, with local variables replaced by their positions *)

type ccase =
  | CCcstr of phistory * (int * ccase) list * ccase
  | CCimm of phistory * (int * ccase) list * ccase
  | CCstr of phistory * (int * ccase) list * ccase
  | CCret of cexpr

and cexpr =
  | CEcons of constant
  | CElvar of int
  | CEval of ident * (cexpr list) * (instance_deriv list)
  | CEmeth of int * (cexpr list) * (instance_deriv list)
  | CEcstr of int * (cexpr list)
  | CEif of cexpr * cexpr * cexpr
  | CEdo of cexpr list
  | CElocbind of cbinding list * cexpr
  | CEcasebind of int * phistory * cexpr
  | CEcase of cexpr * ccase

and cbinding =
  | CBbind of int * cexpr

and cdecl =
  | CDdefn of ident * (int list) * cexpr * int
  | CDinst of int * (cdecl list)
    
type cprogram = cdecl list


(* Constructor id table *)

let () =
  id_ref := 0

let c_str =
  ref 0

let cstr_ids =
  ref Smap.empty

let str_csts_ids =
  ref Smap.empty

let methods =
  ref Smap.empty

(* Ast converting functions *)

let rec alloc_case (env : local_env) fpcur (cases : tcase) =
  match cases with
    | TCret e ->
      let ce, s = alloc_expr env fpcur e in
      CCret ce, s
    | TCbool (h, vals, otherwise) ->
      let cvals, s =
        List.fold_right
          (fun (b, cases) (cvals, s) ->
            let ccases, s' = alloc_case env fpcur cases in
            (((match b with
              | false ->
                0
              | true ->
                1),
            ccases) :: cvals,
            max s s'))
          vals
          ([], 0) in
      let cotherwise, os = alloc_case env fpcur otherwise in
      CCimm (h, cvals, cotherwise), max s os
    | TCint (h, vals, otherwise) ->
      let cvals, s =
        List.fold_right
          (fun (i, cases) (cvals, s) ->
            let ccases, s' = alloc_case env fpcur cases in
            ((i, ccases) :: cvals, max s s'))
          vals
          ([], 0) in
      let cotherwise, os = alloc_case env fpcur otherwise in
      CCimm (h, cvals, cotherwise), max s os
    | TCstr (h, vals, otherwise) ->
      let cvals, s =
        List.fold_right
          (fun (str, cases) (cvals, s) ->
            let ccases, s' = alloc_case env fpcur cases in
            (((try Smap.find str !str_csts_ids
            with Not_found ->
              str_csts_ids := Smap.add str !c_str !str_csts_ids;
            incr c_str;
            !c_str - 1),
            ccases) :: cvals,
            max s s'))
          vals
          ([], 0) in
      let cotherwise, os = alloc_case env fpcur otherwise in
      CCstr (h, cvals, cotherwise), max s os
    | TCcstr (h, cstrs, otherwise) ->
      let ccstrs, s =
        List.fold_right
          (fun (cid, cases) (ccstrs, s) ->
            let ccases, s' = alloc_case env fpcur cases in
            ((Smap.find cid !cstr_ids, ccases) :: ccstrs, max s s'))
          cstrs
          ([], 0) in
      let cotherwise, os = alloc_case env fpcur otherwise in
      CCcstr (h, ccstrs, cotherwise), max s os

and alloc_expr (env : local_env) fpcur (e : typ_texpr) =
  match e.expr with
    | TEcons c ->
      CEcons c,
      fpcur
    | TEvar (v, derivs) ->
      (try CElvar (Smap.find v env)
      with Not_found ->
        try
          CEmeth
            (Smap.find v !methods,
            [],
            List.filter_map
              (fun x ->
                !x)
              derivs)
        with Not_found ->
          CEval
            (v,
            [],
            List.filter_map
              (fun x ->
                !x)
              derivs)),
      fpcur
    | TEapp (f, args, derivs) ->
      let cargs, s =
      List.fold_right
        (fun arg (cargs, s) ->
          let carg, s' = alloc_expr env fpcur arg in
          carg :: cargs, max s s')
        args
        ([],
        fpcur) in
      (try
        CEmeth
          (Smap.find f !methods,
          cargs,
          List.filter_map
            (fun x ->
              !x)
            derivs)
      with Not_found ->
        CEval
          (f,
          cargs,
          List.filter_map
            (fun x ->
              !x)
            derivs)),
      s
    | TEcstr (c, args) ->
      let cargs, s =
      List.fold_right
        (fun arg (cargs, s) ->
          let carg, s' = alloc_expr env fpcur arg in
          carg :: cargs, max s s')
        args
        ([],
        fpcur) in
      CEcstr (Smap.find c !cstr_ids, cargs),
      s
    | TEif (b, e1, e2) ->
      let cb, sb = alloc_expr env fpcur b
      and ce1, s1 = alloc_expr env fpcur e1
      and ce2, s2 = alloc_expr env fpcur e2 in
      CEif (cb, ce1, ce2),
      max sb (max s1 s2)
    | TEdo es ->
      let ces, s =
        List.fold_right
          (fun e (ces, s) ->
            let ce, s' = alloc_expr env fpcur e in
            ce :: ces, max s s')
        es
        ([], 0) in
        CEdo ces,
      s
    | TElocbind (binds, e) ->
      let env, fpcur, cbinds, s =
        List.fold_left
          (fun (env, fpcur, cbinds, s) bind ->
            let env, cbind, s' = alloc_binding env fpcur bind in
            env, (fpcur + 8), cbind :: cbinds, max s s')
          (env, fpcur, [], 0)
          binds in
      let ce, s' = alloc_expr env fpcur e in
      CElocbind (List.rev cbinds, ce),
      max s s'
    | TEcasebind (var, h, e) ->
      let ce, s = alloc_expr (Smap.add var (- fpcur) env) (fpcur + 8) e in
      CEcasebind (- fpcur, h, ce),
        s
    | TEcase (e, case) ->
      let ce, s = alloc_expr env fpcur e in
      let ccase, s' = alloc_case env fpcur case in
      CEcase (ce, ccase),
      max s s'     

and alloc_binding env fpcur bind =
  let TBbind (var, e) = bind in
  let env = Smap.add var (- fpcur) env in
  let ce, s = alloc_expr env (fpcur + 8) e in
  env, CBbind (- fpcur, ce), s

let rec alloc_decl d =
  match d with
    | TDdefn (fid, args, e) ->
      let cargs =
        List.mapi
          (fun i (arg : typ_arg) ->
            16 + 8 * i)
          args in
      let env =
        List.fold_left2
          (fun env (arg : typ_arg) carg ->
            Smap.add arg.var carg env)
          Smap.empty
          args
          cargs in
      let ce, s = alloc_expr env 8 e in
      CDdefn (fid, cargs, ce, s)
    | TDinst (id, inst, defns) ->
      CDinst (id, List.map alloc_decl defns)

let alloc_program p =
  List.map alloc_decl p


(* Compiling *)

let compile_cons c =
  match c with
    | Cbool b ->
      (match b with
        | true ->
          pushq (imm 255)
        | _ ->
          pushq (imm 0))
    | Cint i ->
      pushq (imm i)
    | Cstr s ->
      let n = String.length s in
      movq (imm (n + 1)) !%rdi ++
      call ".aligned_malloc" ++
      pushq !%rax ++
      (let (_, txt) =
        String.fold_right
          (fun c (i, txt) ->
            let asc = Char.code c in
            (i - 1, movb (imm asc) (ind ~ofs:i rax) ++ txt ))
          s
          (n - 1, movb (imm 0) (ind ~ofs:n rax)) in
      txt)

let add_string_constants ids =
  Smap.fold
    (fun str id data ->
      data ++
      label (".str_cst_" ^ (string_of_int id)) ++
      string str)
    ids
    nop

let c_ite =
  ref 0

let c_conj =
  ref 0

let c_disj =
  ref 0

let c_cases =
  ref 0

let vars_in_cur =
  ref 0

let is_in_inst =
  ref false

let compile_history h =
  List.fold_right
    (fun i txt ->
      txt ++
      movq (ind ~ofs:(8 * i) rax) !%rax)
    h
    nop

let rec compile_deriv deriv =
  match deriv with
    | Loc i ->
      (match !is_in_inst with
        | false ->
          movq (ind ~ofs:(16 + !vars_in_cur * 8 + i * 8) rbp) !%rax
        | _ ->
          movq (ind ~ofs:(16 + !vars_in_cur * 8) rbp) !%rax ++
          movq (ind ~ofs:(i * 8) rax) !%rax)
    | Schem (i, impls) ->
      movq (imm (List.length impls + 1)) !%rdi ++
      call ".aligned_malloc" ++
      movq !%rax !%rbx ++
      leaq (lab (".inst_" ^ string_of_int i)) rax ++
      movq !%rax (ind rbx) ++
      let (_, push_impls) =
        List.fold_left
          (fun (i, txt) deriv ->
            i + 1,
            txt ++
            pushq !%rbx ++
            compile_deriv deriv ++
            popq rbx ++
            movq !%rax (ind ~ofs:(8 * i) rbx))
          (1, nop)
          impls in
      push_impls ++
      movq !%rbx !%rax

let rec compile_expr e =
  match e with
    | CEcons c ->
      compile_cons c
    | CElvar pos ->
      pushq (ind ~ofs:pos rbp)
    | CEval (f, [b1; b2], []) when f = "conj" ->
      compile_expr b1 ++
      popq rax ++
      cmpq (imm 0) !%rax ++
      je (".conj_false_" ^ string_of_int (!c_conj)) ++
      compile_expr b2 ++
      jmp (".conj_continue_" ^ string_of_int (!c_conj)) ++
      label (".conj_false_" ^ string_of_int (!c_conj)) ++
      pushq !%rax ++
      label (".conj_continue_" ^ string_of_int (!c_conj)) ++
      (incr c_conj; nop)
    | CEval (f, [b1; b2], []) when f = "disj" ->
      compile_expr b1 ++
      popq rax ++
      cmpq (imm 0) !%rax ++
      jne (".disj_true_" ^ string_of_int (!c_disj)) ++
      compile_expr b2 ++
      jmp (".disj_continue_" ^ string_of_int (!c_disj)) ++
      label (".disj_true_" ^ string_of_int (!c_disj)) ++
      pushq !%rax ++
      label (".disj_continue_" ^ string_of_int (!c_disj)) ++
      (incr c_disj; nop)
    | CEval (f, args, derivs) ->
      List.fold_left
        (fun txt deriv ->
          compile_deriv deriv ++
          pushq !%rax ++
          txt)
        nop
        derivs ++
      List.fold_left
        (fun txt e ->
          compile_expr e ++
          txt)
        nop
        args ++
      call f ++
      popn (8 * (List.length args + List.length derivs)) ++
      pushq !%rax
    | CEmeth (id, args, inst) ->
      (match inst with
        | [ inst ] ->
            compile_deriv inst ++
            pushq !%rax ++
            List.fold_left
              (fun txt e ->
                compile_expr e ++
                txt)
              nop
              args ++
            movq (ind ~ofs:(8 * List.length args) rsp) !%rax ++
            movq (ind rax) !%rax ++
            call_star (ind ~ofs:(8 * id) rax) ++
            popn (8 * (List.length args + 1)) ++
            pushq !%rax
        | _ ->
          failwith "Shouldn't have happened.")
    | CEcstr (c, args) ->
      let n = List.length args in
      movq (imm (n + 1)) !%rdi ++
      call ".aligned_malloc" ++
      pushq !%rax ++
      (let (_, txt) =
        List.fold_left
          (fun (i, txt) arg ->
            (i + 8,
            txt ++
            pushq !%rax ++
            compile_expr arg ++
            popq rbx ++
            popq rax ++
            movq !%rbx (ind ~ofs:i rax)))
          (8, movq (imm c) (ind rax))
          args in
      txt)
    | CEif (b, e1, e2) ->
      let k = !c_ite in incr c_ite;
      compile_expr b ++
      popq rax ++
      cmpq (imm 0) !%rax ++
      je (".ite_else_" ^ string_of_int k) ++
      compile_expr e1 ++
      jmp (".ite_continue_" ^ string_of_int k) ++
      label (".ite_else_" ^ string_of_int k) ++
      compile_expr e2 ++
      label (".ite_continue_" ^ string_of_int k)
    | CEdo es ->
      List.fold_left
        (fun txt e ->
          txt ++ compile_expr e)
        nop
        es
    | CElocbind (binds, e) ->
      List.fold_left
        (fun txt bind ->
          txt ++ compile_bind bind)
        nop
        binds ++
        compile_expr e
    | CEcasebind (i, h, e) ->
      movq !%r10 !%rax ++
      compile_history h ++
      movq !%rax (ind ~ofs:i rbp) ++
      compile_expr e
    | CEcase (e, case) ->
      compile_expr e ++
      popq r10 ++
      compile_case case

and compile_bind bind =
  match bind with
    | CBbind (i, e) ->
      compile_expr e ++
      popq rax ++
      movq !%rax (ind ~ofs:i rbp)

and compile_case case =
  match case with
    | CCret e ->
      compile_expr e
    | CCstr (h, cases, otherwise) ->
      let n = List.length cases in
      let k = !c_cases in
      c_cases := !c_cases + n + 1;
      let (_, checks) =
        List.fold_left
          (fun (i, txt) (cid, _) ->
            i + 1, 
            txt ++
            movq (ilab (".str_cst_" ^ (string_of_int i))) !%rbx ++
            call ".cmp_str_loop" ++
            je (".case_" ^ string_of_int (k + i)))
          (0,
          movq !%r10 !%rax ++
          compile_history h)
          cases in
      checks ++
      compile_case otherwise ++
      jmp (".continue_case_" ^ string_of_int k) ++
      let (_, jmps) =
        List.fold_left
          (fun (i, txt) (_, case) ->
            i + 1, 
            txt ++
            label (".case_" ^ string_of_int (k + i)) ++
            compile_case case ++
            jmp (".continue_case_" ^ string_of_int k)
            )
          (0, 
          nop)
          cases in
      jmps ++
      label (".continue_case_" ^ string_of_int k)
    | CCimm (h, cases, otherwise) ->
      let n = List.length cases in
      let k = !c_cases in
      c_cases := !c_cases + n + 1;
      let (_, checks) =
        List.fold_left
          (fun (i, txt) (cid, _) ->
            i + 1, 
            txt ++
            cmpq (imm cid) !%rax ++
            je (".case_" ^ string_of_int (k + i)))
          (0, 
          movq !%r10 !%rax ++
          compile_history h)
          cases in
      checks ++
      compile_case otherwise ++
      jmp (".continue_case_" ^ string_of_int k) ++
      let (_, jmps) =
        List.fold_left
          (fun (i, txt) (_, case) ->
            i + 1, 
            txt ++
            label (".case_" ^ string_of_int (k + i)) ++
            compile_case case ++
            jmp (".continue_case_" ^ string_of_int k)
            )
          (0, 
          nop)
          cases in
      jmps ++
      label (".continue_case_" ^ string_of_int k)
    | CCcstr (h, cases, otherwise) ->
      let n = List.length cases in
      let k = !c_cases in
      c_cases := !c_cases + n + 1;
      let (_, checks) =
        List.fold_left
          (fun (i, txt) (cid, _) ->
            i + 1, 
            txt ++
            cmpq (imm cid) !%rax ++
            je (".case_" ^ string_of_int (k + i)))
          (0,
          match cases with
            | [] ->
              nop
            | _ ->
              movq !%r10 !%rax ++
              compile_history h ++
              movq (ind rax) !%rax)
          cases in
      checks ++
      compile_case otherwise ++
      jmp (".continue_case_" ^ string_of_int k) ++
      let (_, jmps) =
        List.fold_left
          (fun (i, txt) (_, case) ->
            i + 1, 
            txt ++
            label (".case_" ^ string_of_int (k + i)) ++
            compile_case case ++
            jmp (".continue_case_" ^ string_of_int k)
            )
          (0, 
          nop)
          cases in
      jmps ++
      label (".continue_case_" ^ string_of_int k)

let compile_dec d =
  match d with
  | CDdefn (fid, args, e, fsize) when fid = "main" ->
    vars_in_cur := 0;
    label fid ++
    pushq !%rbp ++
    movq !%rsp !%rbp ++
    pushn fsize ++
    compile_expr e ++
    popq rax ++
    popn fsize ++
    xorq !%rax !%rax ++
    leave ++
    ret
  | CDdefn (fid, args, e, fsize) ->
    vars_in_cur := List.length args;
    label fid ++
    pushq !%rbp ++
    movq !%rsp !%rbp ++
    pushn fsize ++
    compile_expr e ++
    popq rax ++
    popn fsize ++
    leave ++
    ret
  | CDinst (id, defns) ->
    is_in_inst := true;
    List.fold_left
      (fun txt defn ->
        match defn with
          | CDdefn (mid, args, e, fsize) ->
            vars_in_cur := List.length args;
            txt ++
            label (".meth_" ^ (string_of_int id) ^ "_" ^ (string_of_int (Smap.find mid !methods))) ++
            pushq !%rbp ++
            movq !%rsp !%rbp ++
            pushn fsize ++
            compile_expr e ++
            popq rax ++
            popn fsize ++
            leave ++
            ret
          | _ ->
            failwith "Shouldn't have happened")
      nop
      defns

let adds_inst_to_data d =
  match d with
    | CDinst (id, defns) ->
      label (".inst_" ^ string_of_int id) ++
      address
        (List.mapi
          (fun i _ -> ".meth_" ^ string_of_int id ^ "_" ^ string_of_int i)
          defns)
    | _ ->
      nop

let compile_program p ofile =
  cstr_ids :=
    Smap.map
      (fun  _ -> new_id ())
      (Smap.filter 
        (fun _ el ->
          match el with
            | C _ -> true
            | _ -> false)
        !gvenv);
  Smap.iter
    (fun _ el ->
      match el with
        | TTC tc ->
          List.iteri
            (fun i mid ->
              methods := Smap.add mid i !methods)
            tc.methods
        | _ ->
          ())
    !gtenv;
  let p = alloc_program p in
  let code =
    List.fold_left
      (fun txt d ->
        txt ++ compile_dec d)
      nop
      p in
  let p =
    { text =
        globl "main" ++
        code ++
        inline primitives;
    data =
      inline primitive_data ++
      add_string_constants !str_csts_ids ++
      List.fold_left
        (fun txt d ->
          txt ++
          adds_inst_to_data d)
        nop
        p }
  in
  let f = open_out ofile in
  let fmt = formatter_of_out_channel f in
  X86_64.print_program fmt p;
  fprintf fmt "@?";
  close_out f