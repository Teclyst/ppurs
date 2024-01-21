open Ast

module Smap = Map.Make(String)

module Imap = Map.Make(Int)

exception Typing_error of string * loc

let dummy_pos =
  { lnum = 0;
    cnum = 0 }


(*Ast rewriting functions*)

let compactifies p =
  let rec builds_block tdecl acc id l =
    match tdecl.decl with
      | Dtdecl (_, _, _, _, t) ->
        (match l with
          | ({ loc = _ ;
              decl = Ddefn (id', _, _) } as defn)
            :: l' when id = id' ->
            builds_block tdecl (defn :: acc) id l'
          | _ ->
            (match List.length acc with
              | n when n = 0 ->
                raise (Typing_error ("Type declaration for " ^ id ^ " should be succeded by its definition.", tdecl.loc))
              | _ ->
                { loc = tdecl.loc;
                  decl = Dcmpted (tdecl, (List.rev acc)) }, l))
      | _ ->
        failwith "Shouldn't have happened.1" in
  let rec cuts l =
    match l with
      | ({ loc = loc ;
          decl = Ddefn (id, _, e) }) :: _ ->
        raise (Typing_error ("Definition for " ^ id ^ " should be preceded by its type declaration.", loc))
      | ({ loc = _ ;
          decl = Dtdecl (id, _, _, _, _) } as tdecl)
        :: l' ->
        let b, l'' = builds_block tdecl [] id l' in
        b :: cuts l''
      | [] -> []
      | decl :: l' -> decl :: cuts l' in
  cuts p

(* Rewrites a program to group definitions per declaration *)

let compactifies_inst defns =
  let rec builds_block acc id loc defns =
    match defns with
        | ({ loc = _ ;
            decl = Ddefn (id', _, _)  } as defn)
          :: defns' when id = id' ->
          builds_block (defn :: acc) id loc defns'
        | _ ->
          { loc = loc;
            decl = Dcmpted 
              ({ loc = dummy_pos;
                decl = Dtdecl
                  (id,
                  [],
                  [],
                  [],
                  { loc = dummy_pos;
                    purstype = PTvar "dummy"})},
                  (List.rev acc)) },
            defns in
  let rec cuts defns =
    match defns with
      | ({ loc = loc ;
          decl = Ddefn (id, _, _) })
        :: _ ->
        let b, defns' = builds_block [] id loc defns in
        b :: cuts defns'
      | [] ->
        []
      | _ ->
        failwith "Shouldn't have happened.2" in
  cuts defns

(* Rewrites an instance declaration to group definitions per method *)

exception Found of int

let find_nonvar defn =
  match defn.decl with
    | Ddefn (_, ps, e) ->
      List.iteri
        (fun i p ->
          match p.pattern with
            | Pvar _ ->
              ()
            | _ ->
              raise (Found i))
        ps;
    | _ ->
      failwith "Shouldn't have happened.3"

(* Used to find if a function definition involves a non generic argument *)

let rec sub_vars_in_expr mapping e =
  match e.expr with
    | Econs _ ->
      e
    | Evar v ->
      (try
        { loc = e.loc;
          expr = Evar (Smap.find v mapping) }
      with Not_found ->
        e)
    | Etyped (e', p) ->
      { loc = e.loc;
        expr = Etyped (sub_vars_in_expr mapping e', p) }
    | Eapp (fid, args) ->
      { loc = e.loc;
        expr = Eapp (fid, List.map (sub_vars_in_expr mapping) args) }
    | Ecstr (cid, args) ->
      { loc = e.loc;
        expr = Ecstr (cid, List.map (sub_vars_in_expr mapping) args) }
    | Eif (eif, ethen, eelse) ->
      { loc = e.loc;
        expr = Eif (sub_vars_in_expr mapping eif, sub_vars_in_expr mapping ethen, sub_vars_in_expr mapping eelse) }
    | Edo es ->
      { loc = e.loc;
        expr = Edo (List.map (sub_vars_in_expr mapping) es) }
    | Elocbind (bs, e') ->
      { loc = e.loc;
        expr = Elocbind (List.map (sub_vars_in_locbind mapping) bs, sub_vars_in_expr mapping e') }
    | Ecase (e', brnchs) ->
      { loc = e.loc;
        expr = Ecase
          (sub_vars_in_expr mapping e',
          List.map
            (fun (p, e) ->
              (sub_vars_in_pattern mapping p, sub_vars_in_expr mapping e)) brnchs) }

and sub_vars_in_locbind mapping (Bbind (var, e)) =
  try Bbind (Smap.find var mapping, sub_vars_in_expr mapping e)
  with Not_found ->
    Bbind (var, sub_vars_in_expr mapping e)

and sub_vars_in_pattern mapping p =
  match p.pattern with
    | Pcons _ ->
      p
    | Pvar v ->
      (try
        { loc = p.loc;
          pattern = Pvar (Smap.find v mapping) }
      with Not_found ->
        p)
    | Pcstr (cid, args) ->
      { loc = p.loc;
        pattern = Pcstr (cid, List.map (sub_vars_in_pattern mapping) args) }

(* Rewrites an AST by renaming a set of variables (used to convert a series of definitions to a case expression) *)

let treat_defn n i defn =
  match defn.decl with
  | Ddefn (id, ps, e) ->
    let mapping = ref Smap.empty
    and (ipat : loc_pattern option ref) = ref None in
    (if List.length ps != n
      then let m = List.length ps in
        raise (Typing_error ("Value " ^ id ^ " expects " ^ string_of_int n ^ " argument" ^ (if n > 1 then "s" else "") ^ ", but " ^ string_of_int m ^ (if m > 1 then " were" else " was") ^ " given.", defn.loc)));
    List.iteri
      (fun j p ->
        match p.pattern, j with
          | Pvar v, _ when i = j ->
            mapping := Smap.add v (string_of_int j) !mapping;
            ipat := Some p
          | _ when i = j ->
            ipat := Some p
          | Pvar v, _ ->
            mapping := Smap.add v (string_of_int j) !mapping
          | _ -> 
            raise (Typing_error ("Non variable patterns should not occur in more than one column.", p.loc)))
      ps;
    (match !ipat with
      | Some p ->
        (p, sub_vars_in_expr !mapping e)
      | _ ->
        failwith "Shouldn't have happened.")
  | _ ->
    failwith "Shouldn't have happened."

(* Given a column i and a definition defn, returns the pattern at column i and the expression of defn, where occurrences of the other (variable) patterns are replaced by their column converted to string *)

let check_if_vars_differ defn =
  match defn.decl with
    | Ddefn (_, pvars, _) ->
      let alrseen = ref Smap.empty in
      let rec aux p =
        match p.pattern with
          | Pvar v when v <> "_" ->
            (try let () = Smap.find v !alrseen in
              raise (Typing_error ("Variable " ^ v ^ " appears more than once.", p.loc))
            with Not_found ->
              alrseen := Smap.add v () !alrseen)
          | Pvar v ->
            ()
          | Pcstr (_, args) ->
            List.iter aux args
          | _ ->
            () in
      List.iter
        aux
        pvars
    | _ ->
      failwith "Shouldn't have happened."

let compactify_fun_dec n defns =
  let fst = List.hd defns in
  (match fst.decl with
    | Ddefn (id, ps, e) ->
      List.iter check_if_vars_differ defns;
      let i =
        (try List.iter find_nonvar defns;
          -1
        with Found i ->
          i) in
      let i = max 0 i in
      (match n with
        | 0 when List.length defns > 1 ->
          raise (Typing_error ("Multiple value declarations exist for " ^ id ^ ".", fst.loc))
        | 0 ->
          fst
        | _ -> 
          { loc = fst.loc ;
            decl = Ddefn (id,
            List.mapi
              (fun j (p : loc_pattern) ->
              { loc = p.loc;
                pattern = Pvar (string_of_int j) }) ps,
            { loc = e.loc;
              expr = 
                Ecase
                  ({ loc = e.loc;
                    expr = Evar (string_of_int i) },
                  List.map (treat_defn n i) defns ) }) })
    | _ ->
      failwith "Shouldn't have happened.")

(* Converts a group of definitions to a single definition with a case expression *)      


(*Type definitions for types*)

type typ =
  | Tvar of ident
  | Tform of form
  | Tcstr of ident * (typ list)
    
and form =
  { id: int;
    mutable def: typ option }

exception UnificationFailure of typ * typ


(*Auxiliary functions for type handling*)

let id_ref = ref 0

let new_id () =
  let id = !id_ref in
  incr id_ref;
  id

let rec head ut =
  match ut with
    | Tform x ->
      (match x.def with
        | Some ut' ->
          head ut'
        | _ -> ut)
    | _ -> ut

let rec clean_up t =
  match head t with
    | Tcstr (c, args) ->
      Tcstr (c, List.map clean_up args)
    | t' ->
      t'

let str_of_typ t =
    let rec aux init t =
      match head t with
        | Tvar v ->
          v
        | Tform f ->
          "x" ^ string_of_int f.id
        | Tcstr (cid, args) when List.length args = 0 || init ->
          String.concat " " (cid :: List.map (aux false) args)
        | Tcstr (cid, args) ->
          "(" ^ String.concat " " (cid :: List.map (aux false) args) ^ ")" in
    aux true t

let rec unify t1 t2 =
  match head t1, head t2 with
    | Tvar v1, Tvar v2 when v1 = v2 ->
      ()
    | Tcstr (c1, args1), Tcstr (c2, args2) when c1 = c2 ->
      List.iter2 unify args1 args2
    | Tform f, t | t, Tform f ->
      (match f.def with
        | Some _ ->
          failwith "Shouldn't have happened."
        | None ->
          f.def <- Some t)
    | _ -> raise (UnificationFailure (t1, t2))

let unify_typ_lists t1s t2s =
  List.iter2 unify t1s t2s

let rec is_subst t1 t2 =
  match head t1, t2 with
    | Tvar v1, Tvar v2 when v1 = v2 ->
      true
    | Tcstr (c1, args1), Tcstr (c2, args2) when c1 = c2 ->
      is_subst_typ_lists args1 args2
    | t, Tform f ->
      (match f.def with
        | Some t' ->
          t = t'
        | None ->
          f.def <- Some t;
          true)
    | _ -> false

(* is_subst assumes that t2 is cleaned up *)

and is_subst_typ_lists t1s t2s =
  List.for_all2 is_subst t1s t2s

let rec type_copy_aux mapping t =
  let t' = head t in
  match t' with
    | Tcstr (c, args) ->
      Tcstr (c, List.map (type_copy_aux mapping) args)
    | Tform f ->
      (try Tform (Imap.find f.id !mapping)
      with Not_found ->
        let f' = { id = new_id ();
        def = None } in
        mapping := Imap.add f.id f' !mapping;
        Tform f')
    | _ -> t'

let copy_typ t =
  type_copy_aux (ref Imap.empty) t

let copy_typ_list ts =
  let mapping = ref Imap.empty in
  List.map (type_copy_aux mapping) ts

let rec generalise mapping t =
  match t with
    | Tvar v ->
      Tform (Smap.find v mapping)
    | Tcstr (c, args) ->
      Tcstr (c, List.map (generalise mapping) args)
    | _ -> t

(* Given a typ, and a mapping of its type variables to typs, replace these type variables within t according to the mapping *)


(*Type definitions for typing environments*)

type tdata =
  { ar : int;
    forms : typ list;
    cstrs : unit Smap.t }

type inst =
  { id : ident;
    args : typ list}

type var =
  { typ : typ;
    insts : inst list }

and func =
  { args : typ list;
    ret : typ;
    insts : inst list }

type inst_scheme =
  { ded : typ list;
    impl : inst list;
    is_loc : bool;
    id : int }     

type tpclass =
  { ar : int;
    forms : typ list;
    methods : ident list;
    insts : inst_scheme list}

type cstr =
  { args : typ list;
    typ : typ }
  
type tenv_element =
  | TV
  | TD of tdata
  | TTC of tpclass

type venv_element =
  | V of var
  | F of func
  | C of cstr


let rec extract_variables (tenv, mapping) pt =
  match pt.purstype with
    | PTvar v ->
      Smap.add v TV tenv,
      (try let _ = Smap.find v mapping in mapping
      with Not_found ->
        Smap.add v { id = new_id (); def = None } mapping)
    | PTcstr (_, args) ->
      List.fold_left extract_variables (tenv, mapping) args

let extract_variables_inst tenv inst =
  let Iinst(_, args) = inst.instance in
  List.fold_left extract_variables tenv args

(*Global typing environments*)  

let _Unit = Tcstr ("Unit", [])
and _Boolean = Tcstr ("Boolean", [])
and _Int = Tcstr ("Int", [])

and _String = Tcstr ("String", [])

let def_form =
  { id = 0;
    def = None }

let gtenv =
  let gte = Smap.empty in
  ref (Smap.add_seq 
      (List.to_seq 
        [ ("Unit", TD
            { ar = 0;
              forms = [];
              cstrs = Smap.empty});
          ("Boolean", TD
            { ar = 0;
              forms = [];
              cstrs = Smap.empty});
          ("Int", TD
            { ar = 0;
              forms = [];
              cstrs = Smap.empty});
          ("String", TD
            { ar = 0;
              forms = [];
              cstrs = Smap.empty});
          ("Effect", TD
            { ar = 1;
              forms = [ Tform def_form ];
              cstrs = Smap.empty});
          ("Eq", TTC
            { ar = 1;
              methods = [ "eq" ];
              forms = [ Tform def_form ]; 
              insts = 
                [ { ded = [ _Unit ];
                    impl = [];
                    is_loc = false;
                    id = 0 };
                  { ded = [ _Boolean ];
                    impl = [];
                    is_loc = false;
                    id = 1 };
                  { ded = [ _Int ];
                    impl = [];
                    is_loc = false;
                    id = 2 };
                  { ded = [ _String ];
                    impl = [];
                    is_loc = false;
                    id = 3 } ] });
            ("Show", TTC
            { ar = 1;
              methods = [ "show" ];
              forms = [ Tform def_form ]; 
              insts = 
                [ { ded = [ _Boolean ];
                    impl = [];
                    is_loc = false;
                    id = 4 };
                  { ded = [ _Int ];
                    impl = [];
                    is_loc = false;
                    id = 5 } ] }) ])
      gte)

let gvenv =
  let gve = Smap.empty in
  ref (Smap.add_seq 
      (List.to_seq 
        [ ("unit", V 
            { typ = _Unit;
              insts = [] });
          ("log", F 
            { args = [_String];
              ret = Tcstr ("Effect", [ _Unit ]);
              insts = [] });
          ("not", F 
            { args = [ _Boolean ];
              ret = _Boolean;
              insts = [] });
          ("conj", F 
            { args = [ _Boolean; _Boolean ];
              ret = _Boolean;
              insts = [] });
          ("disj", F 
            { args = [ _Boolean; _Boolean ];
              ret = _Boolean;
              insts = [] });
          ("negate", F 
            { args = [ _Int ];
              ret = _Int;
              insts = [] }); 
          ("add", F 
            { args = [ _Int; _Int ];
              ret = _Int;
              insts = [] });
          ("sub", F 
            { args = [ _Int; _Int ];
              ret = _Int;
              insts = [] });
          ("mul", F 
            { args = [ _Int; _Int ];
              ret = _Int;
              insts = [] });
          ("div", F 
            { args = [ _Int; _Int ];
              ret = _Int;
              insts = [] });
          ("append", F 
            { args = [ _String; _String ];
              ret = _String;
              insts = [] });
          ("mod", F 
            { args = [ _Int; _Int ];
              ret = _Int;
              insts = [] });
          ("lessThanOrEq", F 
            { args = [ _Int; _Int ];
              ret = _Boolean;
              insts = [] });
          ("greaterThanOrEq", F 
            { args = [ _Int; _Int ];
              ret = _Boolean;
              insts = [] });
          ("lessThan", F 
            { args = [ _Int; _Int ];
              ret = _Boolean;
              insts = [] });
          ("greaterThan", F 
            { args = [ _Int; _Int ];
              ret = _Boolean;
              insts = [] });
          ("eq", F 
            { args = [Tform def_form; Tform def_form];
              ret = _Boolean;
              insts = 
                [ { id = "Eq";
                    args = [Tform def_form] } ] });
          ("notEq", F 
            { args = [Tform def_form; Tform def_form];
              ret = _Boolean;
              insts = 
                [ { id = "Eq";
                    args = [ Tform def_form ] } ] });
          ("show", F 
            { args = 
              [ Tform def_form ];
              ret = _String;
              insts = [ { id = "Show";
              args = [ Tform def_form ] } ] });
          ("pure", F 
            { args = 
              [ Tform def_form ];
              ret = Tcstr ("Effect", 
                [ Tform def_form ]);
              insts = [] }) ])
      gve)      


(*Type definitions for type-annoted asts*)      

type phistory =
  int list

type instance_deriv =
  | Loc of int
  | Schem of int * (instance_deriv list)

type tinstance =
  | TIinst of ident * (typ list)

type typ_tpattern =
  { pattern : tpattern;
    typ : typ }

and tpattern =
  | TPcons of constant
  | TPvar of ident
  | TPcstr of ident * (typ_tpattern list)

type typ_arg =
  { var : ident;
    typ : typ}

type typ_texpr =
  { expr : texpr;
    typ : typ }

and texpr =
  | TEcons of constant
  | TEvar of ident * (instance_deriv option ref list)
  | TEapp of ident * (typ_texpr list) * (instance_deriv option ref list)
  | TEcstr of ident * (typ_texpr list)
  | TEif of typ_texpr * typ_texpr * typ_texpr
  | TEdo of typ_texpr list
  | TElocbind of tbinding list * typ_texpr
  | TEcasebind of ident * phistory * typ_texpr
  | TEcase of typ_texpr * tcase

and tbinding =
  | TBbind of ident * typ_texpr

and tcase =
  | TCret of typ_texpr
  | TCcstr of phistory * (ident * tcase) list * tcase
  | TCbool of phistory * (bool * tcase) list * tcase
  | TCint of phistory * (int * tcase) list * tcase
  | TCstr of phistory * (string * tcase) list * tcase

and tdecl =
  | TDdefn of ident * (typ_arg list) * typ_texpr
  | TDinst of int * tinstance * (tdecl list)
    
type tprogram = tdecl list

(* Instance resolution checks *)

let str_of_inst (inst : inst) =
  let rec aux t =
    match head t with
      | Tvar v ->
        v
      | Tform f ->
        "x" ^ string_of_int f.id
      | Tcstr (cid, args) when List.length args = 0 ->
        cid
      | Tcstr (cid, args) ->
        "(" ^ String.concat " " (cid :: List.map aux args) ^ ")" in
  String.concat " " (inst.id :: List.map aux inst.args)
  
let copy_var (v : var) =
  let mapping = ref Imap.empty in
  { typ = type_copy_aux mapping v.typ;
    insts =
      List.map
        (fun (inst : inst) ->
          { id = inst.id;
            args = List.map (type_copy_aux mapping) inst.args })
        v.insts }

let copy_func (f : func) =        
  let mapping = ref Imap.empty in
  { ret = type_copy_aux mapping f.ret;
    args = List.map (type_copy_aux mapping) f.args;
    insts =
      List.map
        (fun (inst : inst) ->
          { id = inst.id;
            args = List.map (type_copy_aux mapping) inst.args })
        f.insts }

let copy_inst_scheme inst_s =
  let mapping = ref Imap.empty in
  { ded = List.map (type_copy_aux mapping) inst_s.ded;
    impl =
      List.map
        (fun (inst : inst) ->
          { id = inst.id;
            args = List.map (type_copy_aux mapping) inst.args })
        inst_s.impl;
    is_loc = inst_s.is_loc;
    id = inst_s.id }

let copy_cstrs (data : tdata) =
  let mapping = ref Imap.empty in
  List.map (type_copy_aux mapping) data.forms,
  Smap.mapi
    (fun id () ->
      (match Smap.find id !gvenv with
        | C c ->
          { args = List.map (type_copy_aux mapping) c.args;
            typ = type_copy_aux mapping c.typ }
        | _ ->
          failwith "Shouldn't have happened."))
    data.cstrs

let copy_methods tpclass =
  let mapping = ref Imap.empty in
  (List.map (type_copy_aux mapping) tpclass.forms,
  List.fold_left
    (fun methods id ->
      Smap.add
        id
        (match Smap.find id !gvenv with
          | V v ->
            Some 
              (V
                { typ = type_copy_aux mapping v.typ;
                  insts =
                    List.map
                      (fun (inst : inst) ->
                        { id = inst.id;
                          args = List.map (type_copy_aux mapping) inst.args })
                      v.insts })
          | F f ->
            Some
              (F
                { ret = type_copy_aux mapping f.ret;
                  args = List.map (type_copy_aux mapping) f.args;
                  insts =
                    List.map
                      (fun (inst : inst) ->
                        { id = inst.id;
                          args = List.map (type_copy_aux mapping) inst.args })
                      f.insts })
          | _ ->
            failwith "Shouldn't have happened.")
          methods)
    Smap.empty  
    tpclass.methods)

(* These functions are used to obtain copies of elements of typing environments, with different formal type variables *)    

let rec solve tenv (inst : inst) =
  match Smap.find inst.id tenv with
    | TTC tc ->
      List.fold_left
        (fun deriv inst_s ->
          match deriv with
            | None ->
              let inst_s = copy_inst_scheme inst_s in
              (match is_subst_typ_lists inst.args inst_s.ded with
                | true ->
                  let impl_derivs =
                    List.map (solve tenv) inst_s.impl in
                  (match
                    List.exists
                      (fun deriv ->
                        deriv = None)
                      impl_derivs with
                    | true ->
                      None
                    | _ ->
                      (match inst_s.is_loc with
                        | true ->
                          Some
                            (Loc inst_s.id)
                        | _ ->
                          Some
                            (Schem
                              (inst_s.id,
                              List.map
                                (fun deriv_opt ->
                                  match deriv_opt with
                                    | Some deriv ->
                                      deriv
                                    | _ ->
                                      failwith "Shouldn't have happened.")
                                impl_derivs))))
                | _ ->
                  None)
            | _ ->
              deriv)
        None
        tc.insts
    | _ ->
      failwith ("Shouldn't have happened.")

(* Checks if an instance is solved *)      

let (to_be_checked : (inst * loc * (instance_deriv option ref)) Stack.t) = Stack.create ()

(* Stack of instances whose solvabilty is to be checked once their types are determined *)


(*Pattern matching exhaustivity check*)

type pmatrix = ((typ_tpattern * phistory) list * typ_texpr) list

exception Non_exhaust of loc_pattern list

let convert_to_pmatrix (brnchs : (typ_tpattern * typ_texpr) list) =
  (List.map
    (fun (p, e) ->
      ([ (p, []) ], e))
    brnchs : pmatrix)

(* Converts the branches of a case expression to the corresponding pattern matrix *)

let wildcard_list n =
  (List.init
    n
    (fun _ ->
      { loc = dummy_pos;
        pattern = Pvar "_" }))

let slice i l =
  let rec aux i acc l =
    match i, l with
      | 0, _ ->
        (List.rev acc), l
      | _, h :: t ->
        aux (i - 1) (h :: acc) t
      | _ ->
        failwith "List is too short." in
  aux i [] l

let dummy_typ =
  Tvar "_"

let rec pmatrix_to_tcase (pmat : pmatrix) =
  match pmat with
    | [] ->
      failwith "Shouldn't have happened."
    | (pr, e) :: _ ->
      (match pr with
        | [] ->
          TCret e
        | (p, h) :: pr'  ->
          (match head p.typ with
            | t when t = _Int ->
              (let i = ref 0 in
              match
                List.exists
                  (fun (p, _) ->
                    match p.pattern with
                      | TPvar _ ->
                        true
                      | TPcons (Cint k) ->
                        i := max !i k;
                        false
                      | _ ->
                        false)
                  (List.map
                    (fun (pr, e) -> List.hd pr)
                    pmat) with
                | false ->
                  raise
                    (Non_exhaust
                      ({ loc = dummy_pos;
                        pattern = Pcons (Cint (!i + 1))}
                      :: wildcard_list (List.length pr - 1)))
                | _ ->
                  let sub_pmats =
                    List.fold_right
                      (fun (pr, e) (sub_pmats : pmatrix Smap.t) ->
                        match pr with
                          | ({ pattern = TPvar x;
                              typ = _ }
                            , _)
                            :: pr' when x = "_" ->
                              Smap.map
                                (fun pmat ->
                                  (pr', e) :: pmat)
                                sub_pmats
                          | ({ pattern = TPvar x;
                              typ = _ }, h)
                            :: pr' ->
                              Smap.map
                                (fun pmat ->
                                  (pr',
                                  { typ = e.typ;
                                    expr = TEcasebind (x, h, e)})
                                  :: pmat)
                                sub_pmats
                          | ({ pattern = TPcons (Cint i);
                              typ = _ }, _)
                            :: pr' ->
                              Smap.update
                                (string_of_int i)
                                (fun opt ->
                                  match opt with
                                    | None ->
                                      failwith "Shouldn't have happened (key should have been bound already)"
                                    | Some pmat ->
                                      Some ((pr', e) :: pmat))
                                sub_pmats
                          | _ ->
                            failwith "Shouldn't have happened. (Nothing else than ints should appear here)")
                      pmat
                      (List.fold_left
                        (fun sub_pmats (pr, e) ->
                          match pr with
                            | ({ pattern = TPcons (Cint i);
                                typ = _ }
                              , _)
                              :: _ ->
                                Smap.add (string_of_int i) [] sub_pmats
                            | _ ->
                              sub_pmats)
                        (Smap.add "_" [] Smap.empty)
                        pmat) in
                  let cases =
                    Smap.mapi
                      (fun id sub_pmat ->
                        try pmatrix_to_tcase sub_pmat
                        with Non_exhaust ps ->
                          raise
                            (Non_exhaust
                              ({ pattern = Pvar id;
                                loc = dummy_pos }
                              :: ps)))
                      sub_pmats in
                  let otherwise = Smap.find "_" cases in
                  TCint 
                    (h,
                    List.map
                      (fun (s, c) ->
                        (int_of_string s, c))
                      (Smap.to_list (Smap.remove "_" cases)),
                    otherwise))
                | t when t = _String ->
                  (let i = ref 0 in
                  match
                    List.exists
                      (fun (p, _) ->
                        match p.pattern with
                          | TPvar _ ->
                            true
                          | TPcons (Cstr s) ->
                            i := max !i (String.length s);
                            false
                          | _ ->
                            false)
                      (List.map
                        (fun (pr, e) -> List.hd pr)
                        pmat) with
                    | false ->
                      raise
                        (Non_exhaust
                          ({ loc = dummy_pos;
                            pattern = Pcons (Cstr (String.make (!i + 1) '_')) }
                          :: wildcard_list (List.length pr - 1)))
                    | _ ->
                      let sub_pmats =
                        List.fold_right
                          (fun (pr, e) (sub_pmats : pmatrix Smap.t) ->
                            match pr with
                              | ({ pattern = TPvar x;
                                  typ = _ }
                                , _)
                                :: pr' when x = "_" ->
                                  Smap.map
                                    (fun pmat ->
                                      (pr', e) :: pmat)
                                    sub_pmats
                              | ({ pattern = TPvar x;
                                  typ = _ }, h)
                                :: pr' ->
                                  Smap.map
                                    (fun pmat ->
                                      (pr',
                                      { typ = e.typ;
                                        expr = TEcasebind (x, h, e)})
                                      :: pmat)
                                    sub_pmats
                              | ({ pattern = TPcons (Cstr s);
                                  typ = _ }, _)
                                :: pr' ->
                                  Smap.update
                                    ("\"" ^ s ^ "\"")
                                    (fun opt ->
                                      match opt with
                                        | None ->
                                          failwith "Shouldn't have happened (key should have been bound already)"
                                        | Some pmat ->
                                          Some ((pr', e) :: pmat))
                                    sub_pmats
                              | _ ->
                                failwith "Shouldn't have happened. (Nothing else than strings should appear here)")
                          pmat
                          (List.fold_left
                            (fun sub_pmats (pr, e) ->
                              match pr with
                                | ({ pattern = TPcons (Cstr s);
                                    typ = _ }
                                  , _)
                                  :: _ ->
                                    Smap.add ("\"" ^ s ^ "\"") [] sub_pmats
                                | _ ->
                                  sub_pmats)
                            (Smap.add "_" [] Smap.empty)
                            pmat) in
                      let cases =
                        Smap.mapi
                          (fun id sub_pmat ->
                            try pmatrix_to_tcase sub_pmat
                            with Non_exhaust ps ->
                              raise
                                (Non_exhaust
                                  ({ pattern = Pvar id;
                                    loc = dummy_pos }
                                  :: ps)))
                          sub_pmats in
                      let otherwise = Smap.find "_" cases in
                      TCstr (h, Smap.to_list (Smap.remove "_" cases), otherwise))
                    | t when t = _Boolean ->
                      let sub_pmats =
                        List.fold_right
                          (fun (pr, e) (sub_pmats : pmatrix Smap.t) ->
                            match pr with
                              | ({ pattern = TPvar x;
                                  typ = _ }
                                , _)
                                :: pr' when x = "_" ->
                                  Smap.map
                                    (fun pmat ->
                                      (pr', e) :: pmat)
                                    sub_pmats
                              | ({ pattern = TPvar x;
                                  typ = _ }, h)
                                :: pr' ->
                                  Smap.map
                                    (fun pmat ->
                                      (pr',
                                      { typ = e.typ;
                                        expr = TEcasebind (x, h, e) })
                                      :: pmat)
                                    sub_pmats
                              | ({ pattern = TPcons (Cbool b);
                                  typ = _ }, _)
                                :: pr' ->
                                  Smap.update
                                    (string_of_bool b)
                                    (fun opt ->
                                      match opt with
                                        | None ->
                                          failwith "Shouldn't have happened (key should have been bound already)"
                                        | Some pmat ->
                                          Some ((pr', e) :: pmat))
                                    sub_pmats
                              | _ ->
                                failwith "Shouldn't have happened. (Nothing else than bools should appear here)")
                          pmat
                          (List.fold_left
                            (fun sub_pmats (pr, e) ->
                              match pr with
                                | ({ pattern = TPcons (Cbool b);
                                    typ = _ }
                                  , _)
                                  :: _ ->
                                    Smap.add (string_of_bool b) [] sub_pmats
                                | _ ->
                                  sub_pmats)
                            (Smap.add "_" [] Smap.empty)
                            pmat) in
                      let cases =
                        (Smap.mapi
                          (fun id sub_pmat ->
                            try pmatrix_to_tcase sub_pmat
                            with Non_exhaust ps ->
                              raise
                                (Non_exhaust
                                  ({ pattern = Pvar id;
                                    loc = dummy_pos }
                                  :: ps)))
                          (Smap.update
                            "_"
                            (fun opt ->
                              match opt with
                                | None ->
                                  failwith "Shouldn't have happened here"
                                | Some [] ->
                                  None
                                | _ ->
                                  opt)
                            sub_pmats)) in
                      let is_there_gen = 
                        (try let _ = Smap.find "_" cases in
                        true with
                        Not_found ->
                          false) in
                      let are_all_constrs_there = 
                        (try let _ = Smap.find "true" cases in
                        true with
                        Not_found ->
                          match is_there_gen with
                            | true ->
                              false
                            | _ ->
                              raise
                                (Non_exhaust
                                  ({ loc = dummy_pos;
                                    pattern = Pcons (Cbool true) }
                                  :: wildcard_list (List.length pr - 1)))) &&
                        try let _ = Smap.find "false" cases in
                          true with
                        Not_found ->
                          match is_there_gen with
                            | true ->
                              false
                            | _ ->
                              raise
                                (Non_exhaust
                                  ({ loc = dummy_pos;
                                    pattern = Pcons (Cbool false) }
                                  :: wildcard_list (List.length pr - 1))) in
                      let cases =
                        match are_all_constrs_there with
                          | true ->
                            Smap.add "_" (Smap.find "false" cases) (Smap.remove "false" cases)
                          | _ ->
                            cases in
                      let otherwise = Smap.find "_" cases in
                      TCbool 
                        (h,
                        List.map
                          (fun (s, c) ->
                            (bool_of_string s, c))
                          (Smap.to_list (Smap.remove "_" cases)),
                        otherwise)
                | Tcstr (c, targs) ->
                  (match Smap.find c !gtenv with
                    | TD data ->
                      let form_args, cstrs = copy_cstrs data in
                      unify_typ_lists form_args targs;
                      let sub_pmats =
                        List.fold_right
                          (fun (pr, e) (sub_pmats : pmatrix Smap.t) ->
                            match pr with
                              | ({ pattern = TPvar x;
                                  typ = _ }, h)
                                :: pr' when x = "_" ->
                                  Smap.mapi
                                    (fun cid pmat ->
                                      match cid with
                                        | "_" ->
                                          (pr', e) :: pmat
                                        | _ ->
                                          let c = Smap.find cid cstrs in 
                                            (List.map
                                              (fun t ->
                                                ({ pattern = TPvar "_";
                                                  typ = t },
                                                []))
                                              c.args @
                                              pr',
                                              e)
                                            :: pmat)
                                    sub_pmats
                              | ({ pattern = TPvar x;
                                  typ = _ }, h)
                                :: pr' ->
                                  Smap.mapi
                                    (fun cid pmat ->
                                      match cid with
                                        | "_" ->
                                          (pr',
                                          { typ = e.typ;
                                            expr = TEcasebind (x, h, e)})
                                          :: pmat
                                        | _ ->
                                          let c = Smap.find cid cstrs in 
                                            (List.mapi
                                              (fun i t ->
                                                ({ pattern = TPvar "_";
                                                  typ = t },
                                                (i + 1) :: h ))
                                              c.args @
                                              pr',
                                            { typ = e.typ;
                                              expr = TEcasebind (x, h, e)})
                                            :: pmat)
                                    sub_pmats
                              | ({ pattern = TPcstr (cid, args);
                                  typ = _ }, _)
                                :: pr' ->
                                  let hargs =
                                    List.mapi
                                      (fun i arg -> (arg, ((i + 1) :: h : phistory)))
                                      args in
                                  Smap.update
                                    cid
                                    (fun opt ->
                                      match opt with
                                        | None ->
                                          Some ((hargs @ pr', e) :: [])
                                        | Some pmat ->
                                          Some ((hargs @ pr', e) :: pmat))
                                    sub_pmats
                              | _ ->
                                failwith "Shouldn't have happened. (Nothing else than constructed types should appear here)")
                      pmat
                      (List.fold_left
                        (fun sub_pmats (pr, e) ->
                          match pr with
                            | ({ pattern = TPcstr (cid, _);
                                typ = _ }
                              , _)
                              :: _ ->
                                Smap.add (cid) [] sub_pmats
                            | _ ->
                              sub_pmats)
                        (Smap.add "_" [] Smap.empty)
                        pmat) in
                  let cases =
                    (Smap.mapi
                      (fun cid sub_pmat ->
                        match cid with
                          | _ when cid = "_" ->
                            (try pmatrix_to_tcase sub_pmat
                            with Non_exhaust ps ->
                              raise
                                (Non_exhaust
                                  ({ pattern = Pvar cid;
                                    loc = dummy_pos }
                                  :: ps)))
                          | _ ->
                            let c = Smap.find cid cstrs in
                            let n = List.length c.args in
                            try pmatrix_to_tcase sub_pmat
                            with Non_exhaust ps ->
                              let args, rem = slice n ps in
                              raise
                                (Non_exhaust
                                  ({ pattern = Pcstr (cid, args);
                                    loc = dummy_pos }
                                  :: rem)))
                      (Smap.update
                        "_"
                        (fun opt ->
                          match opt with
                            | None ->
                              failwith "Shouldn't have happened there"
                            | Some [] ->
                              None
                            | _ ->
                              opt)
                        sub_pmats)) in
                  let is_there_gen = 
                    (try let _ = Smap.find "_" cases in
                    true with
                    Not_found ->
                      false) in
                  let are_all_constrs_there =
                    Smap.for_all
                      (match is_there_gen with
                        | true ->
                          fun cid _ ->
                            (try let _ = Smap.find cid cases in true with
                            Not_found ->
                              false)
                        | _ ->
                          fun cid _ ->
                            let c = Smap.find cid cstrs in
                            let n = List.length c.args in
                            (try let _ = Smap.find cid cases in true with
                            Not_found ->
                              raise
                                (Non_exhaust
                                  ({ loc = dummy_pos;
                                    pattern = Pcstr (cid, wildcard_list n) }
                                  :: wildcard_list (List.length pr - 1)))))
                        cstrs in
                  (match are_all_constrs_there with
                    | true ->
                      let cases_list = Smap.to_list
                        (let cases' = Smap.remove "_" cases in
                        match Smap.is_empty cases' with
                          | true ->
                            cases
                          | _ ->
                            cases') in
                      let _, otherwise = List.hd cases_list in
                      TCcstr (h, List.tl cases_list, otherwise)
                    | _ ->
                      let otherwise = Smap.find "_" cases in
                      TCcstr (h, Smap.to_list (Smap.remove "_" cases), otherwise))
                | _ ->
                  failwith "Shouldn't have happened")
          | _ ->
            let sub_pmat =
              List.map
                (fun (pr, e) ->
                  match pr with
                    | ({ pattern = TPvar x;
                        typ = _ },
                      h) ::
                      _
                      when x = "_" ->
                      pr', e
                    | ({ pattern = TPvar x;
                        typ = _ },
                      h) ::
                      _ ->
                      pr',
                      { typ = e.typ;
                        expr = TEcasebind (x, h, e) }
                    | _ ->
                      failwith "Shouldn't have happened (a formal type should have neither constructors nor constants)")
                pmat in
              pmatrix_to_tcase sub_pmat))

(* Checks pattern matching exhaustivity *)
                  

(*Typing functions*)

let c_insts_s =
  ref 6

let new_inst_id () =
  let id = !c_insts_s in
  incr c_insts_s;
  id  

let rec type_purestype tenv (venv : venv_element Smap.t) pt =
  match pt.purstype with
    | PTvar v ->
      (try match Smap.find v tenv with
        | TV ->
          Tvar v
        | _ ->
          raise (Typing_error ("Unknown type variable " ^ v ^ ".", pt.loc))
      with
        | Not_found -> raise (Typing_error ("Unknown type variable " ^ v ^ ".", pt.loc)))
    | PTcstr (c, args) ->
      (try match Smap.find c tenv with
        | TD t ->
          (match t.ar = List.length args with
            | true ->
              Tcstr (c, List.map (type_purestype tenv venv) args)
            | _ ->
              let m = List.length args in
              raise (Typing_error ("Type constructor " ^ c ^ " expects " ^ string_of_int t.ar ^ " argument" ^ (if t.ar > 1 then "s" else "") ^ ", but " ^ string_of_int m ^ (if m > 1 then " were" else " was") ^ " given.", pt.loc)))
        | _ ->
          raise (Typing_error ("Unknown type constructor " ^ c ^ ".", pt.loc))
      with
        | Not_found -> raise (Typing_error ("Unknown type constructor " ^ c ^ ".", pt.loc)))

let type_cons c = 
  match c with
    | Cbool _ -> 
      _Boolean
    | Cint _ -> 
      _Int
    | Cstr _ -> 
      Tcstr ("String", [])

let rec type_pattern (tenv : tenv_element Smap.t) venv alrdecl (p : loc_pattern) =
  match p.pattern with
    | Pcons c ->
      { pattern = TPcons c;
        typ = type_cons c },
      alrdecl
    | Pvar v when v <> "_" ->
      (try let _ = Smap.find v alrdecl in
        raise (Typing_error ("Variable " ^ v ^ " appears more than once.", p.loc))
      with Not_found ->
        let f' = { id = new_id (); def = None } in
        { pattern = TPvar v;
          typ = Tform f' },
        Smap.add v (Tform f') alrdecl)
      | Pvar v ->
        let f' = { id = new_id (); def = None } in
        { pattern = TPvar "_";
          typ = Tform f' },
        alrdecl
    | Pcstr (cid, args) ->
      (try (match Smap.find cid venv with
        | C c -> 
          let targs, alrdecl =
            List.fold_right
              (fun p (tps, alrdecl) ->
                let tp, alrdecl = type_pattern tenv venv alrdecl p in
                tp :: tps, alrdecl)
              args
              ([], alrdecl)
          and l = copy_typ_list (c.typ :: c.args) in
          let ct = List.hd l
          and cargs = List.tl l in
          (try unify_typ_lists cargs (List.map (fun (p : typ_tpattern) -> p.typ) targs);
            { pattern = TPcstr (cid, targs);
              typ = ct }, alrdecl
          with UnificationFailure (t1, t2) ->
            raise (Typing_error ("Unification failure: could not unify type " ^ str_of_typ t1 ^ " and type " ^ str_of_typ t2 ^ ".", p.loc)))
        | _ ->
          raise (Typing_error ("Unknown constructor " ^ cid ^ ".", p.loc)))
      with Not_found ->
        raise (Typing_error ("Unknown constructor " ^ cid ^ ".", p.loc)))
    
let rec type_expr tenv venv (e : loc_expr) = 
  match e.expr with
    | Econs c ->
      { expr = TEcons c;
        typ = type_cons c }
    | Evar v ->
      (try
        (match Smap.find v venv with
          | V x ->
            let x = copy_var x in
            let derivations =
            List.map
              (fun inst ->
                let (deriv : instance_deriv option ref) = ref None in
                Stack.push (inst, e.loc, deriv) to_be_checked;
                deriv)
              x.insts in
            { expr = TEvar (v, derivations);
              typ = x.typ }
          | F f ->
              let n = List.length f.args in
              raise (Typing_error ("Value " ^ v ^ " expects " ^ string_of_int n ^ " argument" ^ (if n > 1 then "s" else "") ^ ", but 0 was given.", e.loc))
          | _ ->
            failwith "Shouldn't have happened.")
      with Not_found ->
        raise (Typing_error ("Unknown value " ^ v ^ ".", e.loc)))
    | Ecstr (cid, args) ->
      (try
        (match Smap.find cid venv with
          | C c -> 
            let targs = List.map (type_expr tenv venv) args 
            and l = copy_typ_list (c.typ :: c.args) in
            let ct = List.hd l
            and cargs = List.tl l in
            (try unify_typ_lists cargs (List.map (fun e -> e.typ) targs);
              { expr = TEcstr (cid, targs);
                typ = ct }
            with 
              | UnificationFailure (t1, t2) ->
                raise (Typing_error ("Unification failure: could not unify type " ^ str_of_typ t1 ^ " and type " ^ str_of_typ t2 ^ ".", e.loc))
              | Invalid_argument _ ->
                let m = List.length args
                and n = List.length c.args in
                raise (Typing_error ("Constructor " ^ cid ^ " expects " ^ string_of_int n ^ " argument" ^ (if n > 1 then "s" else "") ^ ", but " ^ string_of_int m ^ (if m > 1 then " were" else " was") ^ " given.", e.loc)))
          | _ ->
            raise (Typing_error ("Unknown constructor " ^ cid ^ ".", e.loc)))
          with Not_found ->
            raise (Typing_error ("Unknown constructor " ^ cid ^ ".", e.loc)))
    | Eapp (fid, args) ->
      (try (match Smap.find fid venv with
        | F f ->
          let targs = List.map (type_expr tenv venv) args
          and f = copy_func f in
          let derivs =
          List.map 
            (fun inst ->
              let (deriv : instance_deriv option ref) = ref None in
              Stack.push (inst, e.loc, deriv) to_be_checked;
              deriv)
            f.insts in
          (try unify_typ_lists f.args (List.map (fun e -> e.typ) targs);
            { expr = TEapp (fid, targs, derivs);
              typ = f.ret }
          with 
            | UnificationFailure (t1, t2) ->
              raise (Typing_error ("Unification failure: could not unify type " ^ str_of_typ t1 ^ " with type " ^ str_of_typ t2 ^ ".", e.loc))
            | Invalid_argument _ ->
              let m = List.length args
              and n = List.length f.args in
              raise (Typing_error ("Value " ^ fid ^ " expects " ^ string_of_int n ^ " argument" ^ (if n > 1 then "s" else "") ^ ", but " ^ string_of_int m ^ (if m > 1 then " were" else " was") ^ " given.", e.loc)))
        | _ ->
          let m = List.length args in
          raise (Typing_error ("Value " ^ fid ^ " expects 0 argument, but " ^ string_of_int m ^ (if m > 1 then " were" else " was") ^ " given.", e.loc)))
      with Not_found ->
        raise (Typing_error ("Unknown value " ^ fid ^ ".", e.loc)))
    | Elocbind (binds, e) ->
      let tbinds, venv =
        (List.fold_left
          (fun (tbinds, venv) bind ->
            let tbind, venv = type_binding tenv venv bind in
          (tbind :: tbinds, venv))
        ([], venv)
        binds) in
      let te = type_expr tenv venv e in
      { expr = TElocbind (List.rev tbinds, te);
        typ = te.typ }
    | Eif (b, e1, e2) ->
      let tb = type_expr tenv venv b
      and te1 = type_expr tenv venv e1
      and te2 = type_expr tenv venv e2 in
      (try unify tb.typ _Boolean;
        unify te1.typ te2.typ;
          { expr = TEif (tb, te1, te2);
            typ = te1.typ }
      with UnificationFailure (t1, t2) ->
        raise (Typing_error ("Could not match type " ^ str_of_typ t1 ^ " with type " ^ str_of_typ t2 ^ ".", e.loc)))
    | Etyped (e, pt) ->
      let te = type_expr tenv venv e
      and ti = type_purestype tenv venv pt in
      (try unify te.typ ti;
        { expr = te.expr;
          typ = ti }
      with UnificationFailure (t1, t2) ->
        raise (Typing_error ("Could not match type " ^ str_of_typ t1 ^ " with type " ^ str_of_typ t2 ^ ".", e.loc)))
    | Edo es ->
      let tes = List.map (type_expr tenv venv) es in
      List.iter
        (fun te ->
          try unify te.typ (Tcstr ("Effect", [ Tcstr ("Unit", []) ])) with
            | UnificationFailure (t1, t2) -> raise (Typing_error ("Could not match type " ^ str_of_typ t1 ^ " with type " ^ str_of_typ t2 ^ ".", e.loc)))
        tes;
        { expr = TEdo tes;
          typ = Tcstr ("Effect", [ Tcstr ("Unit", []) ]) }
    | Ecase (matchede, brnchs) ->
      let tmatchede = type_expr tenv venv matchede in
      let tpats =
        List.map
          (fun (p, _) ->
            type_pattern tenv venv Smap.empty p)
          brnchs in
      List.iter
        (fun ((tp : typ_tpattern), _) -> 
          unify tmatchede.typ tp.typ)
        tpats;
      let varmappings =
        List.map
          (fun (_, varmapping) ->
            Smap.map
              (fun t ->
                V 
                  { typ = clean_up t;
                    insts = [] })
              varmapping)
        tpats in
      let tes = List.map2
        (fun (_, e) varmapping ->
          type_expr
            tenv
            (Smap.union
              (fun _  _ x -> Some x)
              venv
              varmapping)
            e)
        brnchs
        varmappings in
      let te = List.hd tes
      and tbrnchs =
        List.map2 
          (fun (tp, _) te ->
            (tp, te))
            tpats
            tes in
      List.iter
        (fun te' ->
          unify te.typ te'.typ)
        (List.tl tes);
      try { expr = TEcase (tmatchede, pmatrix_to_tcase (convert_to_pmatrix tbrnchs));
            typ = te.typ }
      with Non_exhaust ps ->
        (match ps with
          | p :: [] ->
            raise (Typing_error ("A case expression could not be determined to cover all inputs: " ^ Pretty.str_of_pattern p ^ " is not covered.", e.loc))
          | _ ->
            failwith "Shouldn't have happened.")
      
and type_binding (tenv : tenv_element Smap.t) venv b =
  let Bbind (var, e) = b in
  let te = (type_expr tenv venv e) in
  (TBbind (var, te),
  Smap.add
    var
    (V
      { typ = te.typ; 
        insts = []})
    venv)

let type_defn tenv trettype targtypes defn =
  match defn.decl with
    | Ddefn (fid, args, ret) ->
      (try let venv =
        List.fold_left2
          (fun venv (p : loc_pattern) t ->
            match p.pattern with
              | Pvar v ->
                Smap.add
                  v
                  (V
                    { typ = t;
                      insts = [] })
                  venv
              | _ ->
                failwith "Shouldn't have happened.")
          !gvenv
          args
          targtypes in
      let tret = type_expr tenv venv ret in
      (try unify tret.typ trettype
      with UnificationFailure (t1, t2) ->
        raise (Typing_error ("Could not match type " ^ str_of_typ t1 ^ " with type " ^ str_of_typ t2 ^ ".", defn.loc)));
      Stack.iter
        (fun (inst, loc, deriv_ref) ->
          match solve tenv inst with
            | Some deriv ->
              deriv_ref := Some deriv
            | _ ->
              raise (Typing_error ("No type class instance was found for " ^ str_of_inst inst ^ ".", loc)))
        to_be_checked;
      Stack.clear to_be_checked;
      TDdefn
        (fid,
        List.map2
          (fun (p : loc_pattern) t ->
            match p.pattern with
              | Pvar v ->
                { var = v;
                  typ = t }
              | _ ->
                failwith "Shouldn't have happened.")
          args
          targtypes,
          tret)
    with Invalid_argument _ ->
      let m = List.length args
      and n = List.length targtypes in
      raise (Typing_error ("Value " ^ fid ^ " expects " ^ string_of_int n ^ " argument" ^ (if n > 1 then "s" else "") ^ ", but " ^ string_of_int m ^ (if m > 1 then " were" else " was") ^ " given.", defn.loc)))
  | _ ->
    failwith "Shouldn't have happened."

let type_decl d =
  match d.decl with
    | Dcmpted
        ({ loc = _ ;
          decl = Dtdecl (fid, vars, impls, argtypes, rettype) },
        defns) ->
      let defn = compactify_fun_dec (List.length argtypes) defns in
      (match defn.decl with
        | Ddefn (_, args, ret) ->
          (let tenv =
            List.fold_left
            (fun tenv v ->
              (match v with
                | _ when v <> "_" ->
                  (try let _ = Smap.find v tenv in
                    raise (Typing_error ("Type argument " ^ v ^ " appears more than once.", d.loc))
                  with Not_found ->
                    Smap.add v TV tenv)
                | _ -> tenv))
            !gtenv
            vars
          and mapping =
            Smap.add_seq
              (List.to_seq
                (List.map
                  (fun v ->
                    (v,
                    { id = new_id ();
                      def = None }))
                  vars))
            Smap.empty in
          let tenv, insts, _ =
            List.fold_left
              (fun (tenv, insts , i) (linst : loc_instance) ->
                let Iinst (id, pts) = linst.instance in
                try 
                  match Smap.find id tenv with
                    | TTC tc ->
                      (match tc.ar = List.length pts with
                        | true ->
                          let tpts = List.map (type_purestype tenv !gvenv) pts in
                          (Smap.add id
                            (TTC
                              { ar = tc.ar;
                                methods = tc.methods;
                                forms = tc.forms;
                                insts =
                                  { ded = tpts;
                                    impl = [];
                                    is_loc = true;
                                    id = i }
                                  :: tc.insts })
                            tenv,
                          { id = id;
                            args = tpts } ::
                          insts,
                          i + 1)
                        | _ ->
                          let m = List.length pts in
                          raise (Typing_error ("Type class " ^ id ^ " expects " ^ string_of_int tc.ar ^ " argument" ^ (if tc.ar > 1 then "s" else "") ^ ", but " ^ string_of_int m ^ (if m > 1 then " were" else " was") ^ " given", linst.loc)))
                    | _ ->
                      raise (Typing_error ("Unknown instance " ^ id ^ ".", linst.loc))
                with Not_found ->
                  raise (Typing_error ("Unknown instance " ^ id ^ ".", linst.loc)))
              (tenv, [], 0)
              impls in
          let targtypes = List.map
            (fun pt -> clean_up (type_purestype tenv !gvenv pt))
            argtypes
          and trettype = clean_up (type_purestype tenv !gvenv rettype) in
          (match argtypes with
            | [] ->
              (try let _ = Smap.find fid !gvenv in
                raise (Typing_error ("Value " ^ fid ^ " has been defined several times.", d.loc))
              with Not_found ->
                gvenv :=
                  Smap.add
                    fid
                    (V
                      { typ = generalise mapping trettype;
                        insts =
                          List.rev
                            (List.map
                              (fun (inst : inst) ->
                                { id = inst.id;
                                  args = List.map (generalise mapping) inst.args })
                              insts) })
                    !gvenv)
            | _ ->
              (try let _ = Smap.find fid !gvenv in
                raise (Typing_error ("Value " ^ fid ^ " has been defined several times.", d.loc))
              with Not_found ->
                gvenv :=
                  Smap.add
                    fid
                    (F 
                      { args = List.map (generalise mapping) targtypes;
                        ret = generalise mapping trettype;
                        insts =
                          List.rev
                              (List.map
                                (fun (inst : inst) ->
                                  { id = inst.id;
                                    args = List.map (generalise mapping) inst.args })
                                insts) })
                    !gvenv));
        Some (type_defn tenv trettype targtypes defn))    
        | _ ->
          failwith "Shouldn't have happened.")
    | Ddata (tcid, vars, cstrs) ->
      let tenv = List.fold_left
        (fun tenv v ->
          (match v with
            | _ when v <> "_" ->
              (try let _ = Smap.find v tenv in
                raise (Typing_error ("Type argument " ^ v ^ " appears more than once.", d.loc))
              with Not_found ->
                Smap.add v TV tenv)
            | _ ->
              raise (Typing_error ("_ is not allowed as a type variable name.", d.loc))))
        !gtenv
        vars
      and mapping =
        Smap.add_seq
          (List.to_seq
            (List.map
              (fun v ->
                (v,
                { id = new_id ();
                  def = None }))
              vars))
          Smap.empty in
      let t =
        generalise
          mapping
          (Tcstr
            (tcid,
            List.map
              (fun v ->
                Tvar v)
              vars)) in
      let cstr_ids = List.fold_left
        (fun cstr_ids (cid, args) ->
          try let _ = Smap.find cid !gvenv in
            raise
              (Typing_error
                ("Declaration for data constructor " ^ cid ^ " conflicts with an existing object of the same name.",
                d.loc))
          with Not_found ->
            try let _ = Smap.find cid cstr_ids in
              raise
                (Typing_error
                  ("Declaration for data constructor " ^ cid ^ " conflicts with an existing object of the same name.",
                  d.loc))
            with Not_found ->
              Smap.add cid () cstr_ids)
        Smap.empty
        cstrs in
      (try let _ = Smap.find tcid !gtenv in
        raise
          (Typing_error
            ("Declaration for type " ^ tcid ^ " conflicts with an existing object of the same name.",
            d.loc))
      with Not_found ->
        gtenv :=
          Smap.add
            tcid
            (TD 
              { ar = List.length vars;
                forms =
                  List.map
                    (fun var ->
                      Tform (Smap.find var mapping))
                    vars;
                cstrs = cstr_ids})
            !gtenv);
      let tenv =
        Smap.add
          tcid
          (TD 
            { ar = List.length vars;
              forms =
                List.map
                  (fun var ->
                    Tform (Smap.find var mapping))
                  vars;
              cstrs = cstr_ids})
          tenv in
      List.iter
        (fun (cid, args) -> 
          let targs = List.map (type_purestype tenv !gvenv) args in
          gvenv :=
            Smap.add
              cid
              (C
              { args = List.map (generalise mapping) targs;
                typ = t })
              !gvenv)
        cstrs;
      None
    | Dclass (cid, vars, decls) ->
      (try let _ = Smap.find cid !gtenv in
        raise (Typing_error ("Declaration for type class " ^ cid ^ " conflicts with an existing object of the same name.", d.loc))
      with Not_found ->
        ());
      let tenv =
        List.fold_left
          (fun tenv v ->
            (match v with
              | _ when v <> "_" ->
                (try let _ = Smap.find v tenv in
                  raise (Typing_error ("Type argument " ^ v ^ " appears more than once.", d.loc))
                with Not_found ->
                  Smap.add v TV tenv)
              | _ ->
                raise (Typing_error ("_ is not allowed as a type variable name.", d.loc))))
        !gtenv
        vars
      and mapping =
        Smap.add_seq
          (List.to_seq
            (List.map
              (fun v ->
                (v,
                { id = new_id ();
                  def = None }))
              vars))
          Smap.empty in
      let forms =
        List.map
          (fun v -> Tform (Smap.find v mapping))
          vars in
      let inst =
        { id = cid;
          args = forms } in
      let methods =
        List.map
          (fun decl ->
            match decl.decl with
              | Dtdecl (fid, vars, insts, argtypes, rettype) when vars = [] && insts = [] ->
                (match argtypes with
                  | [] ->
                    (try let _ = Smap.find fid !gvenv in
                    raise (Typing_error ("Value " ^ fid ^ " has been defined several times.", decl.loc))
                      with Not_found ->
                        gvenv :=
                          Smap.add
                            fid
                            (V
                              { typ = generalise mapping (clean_up (type_purestype tenv !gvenv rettype));
                                insts = [ inst ] })
                            !gvenv)
                  | _ ->
                    (try let _ = Smap.find fid !gvenv in
                    raise (Typing_error ("Value " ^ fid ^ " has been defined several times.", decl.loc))
                      with Not_found ->
                        gvenv :=
                          Smap.add
                            fid
                            (F 
                              { args =
                                  List.map
                                    (fun argtype ->
                                      generalise mapping (clean_up (type_purestype tenv !gvenv argtype)))
                                    argtypes;
                                ret = generalise mapping (clean_up (type_purestype tenv !gvenv rettype));
                                insts = [ inst ] })
                            !gvenv));
                fid
              | Dtdecl (fid, _, _, _, _) ->
                raise (Typing_error ("Type declaration for method " ^ fid ^ "should involve neither new type variables nor instance derivations.", decl.loc))
              | _ ->
                failwith "Shouldn't have happened.")
          decls in
      gtenv :=
        Smap.add
          cid
          (TTC
            { ar = List.length forms;
              forms = forms; 
              methods = methods;
              insts = []})
          !gtenv;
      None
    | Dinst (impls', ded', defns) ->
      let method_defns = compactifies_inst defns in
      let (tenv, mapping) = List.fold_left extract_variables_inst (!gtenv, Smap.empty) (ded' :: impls') in
      let Iinst (iid, args) = ded'.instance in
        (try (match Smap.find iid tenv with
          | TTC tc ->
            let vars, methods = copy_methods tc in
            (try List.iter2
              (fun var pt ->
                match var with
                  | Tform f ->
                    f.def <- Some (type_purestype tenv !gvenv pt)
                  | _ ->
                    failwith "Shouldn't have happened.")
              vars
              args
            with Invalid_argument _ ->
              let m = List.length args in
              raise (Typing_error ("Type class " ^ iid ^ " expects " ^ string_of_int tc.ar ^ " argument" ^ (if tc.ar > 1 then "s" else "") ^ ", but " ^ string_of_int m ^ (if m > 1 then " were" else " was") ^ " given.", d.loc)));
            let impls =
              List.map
                (fun (linst : loc_instance) ->
                  let Iinst (id, pts) = linst.instance in
                  { id = id;
                    args = List.map (type_purestype tenv !gvenv) pts })
                impls'
            and ded =
              let Iinst (id, pts) = ded'.instance in
                  { id = id;
                    args = List.map (type_purestype tenv !gvenv) pts } in
            let gen_args = List.map (generalise mapping) ded.args in
            List.iter
              (fun inst_s ->
                try unify_typ_lists (copy_typ_list gen_args) (copy_typ_list (inst_s.ded));
                  raise
                    (Typing_error
                      ("Type class instances " ^
                      str_of_inst
                        { id = iid;
                          args = inst_s.ded } ^
                      " and " ^
                      str_of_inst ded ^
                      " overlap.",
                      d.loc))
                with UnificationFailure _ ->
                  ())
              tc.insts;
            let id = new_inst_id () in
            let gen_tc =
              { ar = tc.ar;
                forms = tc.forms;
                methods = tc.methods;
                insts =
                  { ded = gen_args;
                    impl =
                      List.map
                        (fun (inst : inst) ->
                          { id = inst.id;
                            args = List.map (generalise mapping) inst.args })
                        impls;
                    is_loc = false;
                    id = id} ::
                      tc.insts; } in
            gtenv :=
              Smap.add
                iid
                (TTC
                  gen_tc)
                !gtenv;
            let tenv =
              Smap.add
                iid
                (TTC
                  gen_tc)
                !gtenv in
            let (tenv, _, _) =
              List.fold_left2
                (fun (tenv, is_ded, i) (inst : inst) (linst : loc_instance) ->
                  try 
                    match Smap.find inst.id tenv with
                      | TTC tc ->
                        (match tc.ar = List.length inst.args with
                          | true ->
                            ((match is_ded with
                              | false ->
                                Smap.add
                                  inst.id
                                  (TTC
                                    { ar = tc.ar;
                                      methods = tc.methods;
                                      forms = tc.forms;
                                      insts =
                                        { ded = inst.args;
                                          impl = [];
                                          is_loc = true;
                                          id = i }
                                        :: tc.insts })
                                  tenv
                              | _ ->
                                tenv),
                              false,
                              i + 1)
                          | _ ->
                            let m = List.length inst.args in
                            raise (Typing_error ("Type class " ^ inst.id ^ " expects " ^ string_of_int tc.ar ^ " argument" ^ (if tc.ar > 1 then "s" else "") ^ ", but " ^ string_of_int m ^ (if m > 1 then " were" else " was") ^ " given", linst.loc)))
                      | _ ->
                        raise (Typing_error ("Unknown type class " ^ inst.id ^ ".", linst.loc))
                  with Not_found ->
                    raise (Typing_error ("Unknown type class " ^ inst.id ^ ".", linst.loc)))
                (tenv, true, 0)
                (ded :: impls)
                (ded' :: impls') in
            let (methods, tdefns) =
              List.fold_left
                (fun (methods, tdefns) cmpted ->
                  match cmpted.decl with
                    | Dcmpted
                        ({ loc = _ ;
                          decl = Dtdecl (fid, _, _, _, _) },
                        defns) ->
                      (try
                        (match Smap.find fid methods with
                          | None ->
                            raise (Typing_error ("Multiple value declarations exist for value " ^ fid ^ ".", cmpted.loc))
                          | Some (V v) ->
                            Smap.add fid None methods,
                            type_defn tenv v.typ [] (compactify_fun_dec 0 defns) :: tdefns
                          | Some (F f) ->
                            Smap.add fid None methods,
                            type_defn tenv f.ret f.args (compactify_fun_dec (List.length f.args) defns) :: tdefns
                          | _ ->
                            failwith "Shouldn't have happened.")
                      with Not_found ->
                        raise (Typing_error (fid ^ " is not a member of type class " ^ iid ^ ".", cmpted.loc)))
                    | _ ->
                      failwith "Shouldn't have happened.")
                (methods, [])
                method_defns in
            let not_implemented = Smap.fold
              (fun id opt acc ->
                match opt with
                | Some _ ->
                  id :: acc
                | _ ->
                  acc)
              methods
              [] in
            (match List.length not_implemented with
              | 0 ->
                ()
              | n ->
                raise (Typing_error ("Member" ^ (if n > 1 then "s " else " ") ^ String.concat ", " not_implemented ^ " of type class " ^ iid ^ (if n > 1 then " have" else " has") ^ " not been implemented", d.loc)));
            Some (TDinst (id, TIinst (iid, ded.args), tdefns))
          | _ ->
            failwith "Shouldn't have happened.")
          with Not_found ->
            raise (Typing_error ("Unknown type class " ^ iid ^ ".", d.loc)))
    | _ ->
      failwith "Shouldn't have happened."

let type_program (p : program) =
  let tp = List.filter_map type_decl p in
  (try let _ = Smap.find "main" !gvenv in
    ()
  with Not_found ->
    raise (Typing_error ("No main declaration was found.", { lnum = 0; cnum = 0 })));
  tp