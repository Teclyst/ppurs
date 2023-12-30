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
        failwith "Shouldn't have happened." in
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
        failwith "Shouldn't have happened." in
  cuts defns

exception Found of int

let finds_last_nonvar n defn =
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
      failwith "Shouldn't have happened."

let rec subs_vars_in_expr mapping e =
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
        expr = Etyped (subs_vars_in_expr mapping e', p) }
    | Eapp (fid, args) ->
      { loc = e.loc;
        expr = Eapp (fid, List.map (subs_vars_in_expr mapping) args) }
    | Ecstr (cid, args) ->
      { loc = e.loc;
        expr = Ecstr (cid, List.map (subs_vars_in_expr mapping) args) }
    | Eif (eif, ethen, eelse) ->
      { loc = e.loc;
        expr = Eif (subs_vars_in_expr mapping eif, subs_vars_in_expr mapping ethen, subs_vars_in_expr mapping eelse) }
    | Edo es ->
      { loc = e.loc;
        expr = Edo (List.map (subs_vars_in_expr mapping) es) }
    | Elocbind (bs, e') ->
      { loc = e.loc;
        expr = Elocbind (List.map (subs_vars_in_locbind mapping) bs, e') }
    | Ecase (e', brnchs) ->
      { loc = e.loc;
        expr = Ecase
          (subs_vars_in_expr mapping e',
          List.map
            (fun (p, e) ->
              (subs_vars_in_pattern mapping p, subs_vars_in_expr mapping e)) brnchs) }

and subs_vars_in_locbind mapping (Bbind (var, e)) =
  try Bbind (Smap.find var mapping, subs_vars_in_expr mapping e)
  with Not_found ->
    Bbind (var, subs_vars_in_expr mapping e)

and subs_vars_in_pattern mapping p =
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
        pattern = Pcstr (cid, List.map (subs_vars_in_pattern mapping) args) }

let treats_defn n i defn =
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
          | _ when i = j -> ipat := Some p
          | Pvar v, _ ->
            mapping := Smap.add v (string_of_int j) !mapping
          | _ -> 
            raise (Typing_error ("Non variable patterns should not occur in more than one column.", p.loc)))
      ps;
    (match !ipat with
      | Some p ->
        (p, subs_vars_in_expr !mapping e)
      | _ ->
        failwith "Shouldn't have happened.")
  | _ ->
    failwith "Shouldn't have happened."

let checks_if_vars_differ pvars =
  let alrseen = ref Smap.empty in
  List.iter
    (fun p ->
      match p.pattern with
        | Pvar v when v <> "_" ->
          (try let () = Smap.find v !alrseen in
            raise (Typing_error ("Variable " ^ v ^ " appears more than once.", p.loc))
          with Not_found ->
            alrseen := Smap.add v () !alrseen)
          | Pvar v ->
            ()
        | _ ->
          failwith "Shouldn't have happened.")
    pvars

let compactifies_fun_dec n defns =
  let fst = List.hd defns in
  (match fst.decl with
    | Ddefn (id, ps, e) ->
      let i =
        (try List.iter (finds_last_nonvar n) defns;
          -1
        with Found i ->
          i) in
      (if n = 0 && List.length defns > 1
        then raise (Typing_error ("Multiple value declarations exist for " ^ id ^ ".", e.loc)));
      (match i with
        | _ when i = -1 && n = 0 ->
          checks_if_vars_differ ps;
          fst
        | _ ->
          let i = max 0 i in
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
                  List.map (treats_defn n i) defns ) }) })
    | _ ->
      failwith "Shouldn't have happened.")


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

let form_ident = ref 0

let new_id () =
  let id = !form_ident in
  incr form_ident;
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

let str_of_type t =
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


(*Type definitions for typing environments*)

type tdata =
  { ar: int;
    cstrs: unit Smap.t }

type inst =
  { id: ident;
    args: typ list}

type var =
  { typ: typ;
    insts: inst list }

and func =
  { args: typ list;
    ret: typ;
    insts: inst list }

type inst_scheme =
  { ded: typ list;
    impl: inst list }     

type tpclass =
  { ar: int;
    forms: typ list;
    methods: ident list;
    insts: inst_scheme list}

type cstr =
  { args: typ list;
    typ: typ }
  
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
              cstrs = Smap.empty});
          ("Boolean", TD
            { ar = 0;
              cstrs = Smap.empty});
          ("Int", TD
            { ar = 0;
              cstrs = Smap.empty});
          ("String", TD
            { ar = 0;
              cstrs = Smap.empty});
          ("Effect", TD
            { ar = 1;
              cstrs = Smap.empty});
          ("Eq", TTC
            { ar = 1;
              methods = [ "(==)"; "(/=)" ];
              forms = [ Tform def_form ]; 
              insts = 
                [ { ded = [ _Unit ];
                    impl = [] };
                  { ded = [ _Boolean ];
                    impl = [] };
                  { ded = [ _Int ];
                    impl = [] };
                  { ded = [ _String ];
                    impl = [] }; ] }) ])
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
          ("(&&)", F 
            { args = [ _Boolean; _Boolean ];
              ret = _Boolean;
              insts = [] });
          ("(||)", F 
            { args = [ _Boolean; _Boolean ];
              ret = _Boolean;
              insts = [] });
          ("negate", F 
            { args = [ _Int ];
              ret = _Int;
              insts = [] }); 
          ("(+)", F 
            { args = [ _Int; _Int ];
              ret = _Int;
              insts = [] });
          ("(-)", F 
            { args = [ _Int; _Int ];
              ret = _Int;
              insts = [] });
          ("(*)", F 
            { args = [ _Int; _Int ];
              ret = _Int;
              insts = [] });
          ("(/)", F 
            { args = [ _Int; _Int ];
              ret = _Int;
              insts = [] });
          ("mod", F 
            { args = [ _Int; _Int ];
              ret = _Int;
              insts = [] });
          ("(<=)", F 
            { args = [ _Int; _Int ];
              ret = _Boolean;
              insts = [] });
          ("(>=)", F 
            { args = [ _Int; _Int ];
              ret = _Boolean;
              insts = [] });
          ("(<)", F 
            { args = [ _Int; _Int ];
              ret = _Boolean;
              insts = [] });
          ("(>)", F 
            { args = [ _Int; _Int ];
              ret = _Boolean;
              insts = [] });
          ("(==)", F 
            { args = [Tform def_form; Tform def_form];
              ret = _Boolean;
              insts = 
                [ { id = "Eq";
                    args = [Tform def_form] } ] });
          ("(/=)", F 
            { args = [Tform def_form; Tform def_form];
              ret = _Boolean;
              insts = 
                [ { id = "Eq";
                    args = [ Tform def_form ] } ] });
          ("pure", F 
            { args = 
              [ Tform def_form ];
              ret = Tcstr ("Effect", 
                [ Tform def_form ]);
              insts = [] }) ])
      gve)      


(*Type definitions for type-annoted asts*)      
type tinstance =
  | TIinst of ident * (typ list)

type typ_tpattern =
  { pattern: tpattern;
    typ: typ }

and tpattern =
  | TPcons of constant
  | TPvar of ident
  | TPcstr of ident * (typ_tpattern list)

type typ_texpr =
  { expr: texpr;
    typ: typ }

and texpr =
  | TEcons of constant
  | TEvar of ident
  | TEapp of ident * (typ_texpr list)
  | TEcstr of ident * (typ_texpr list)
  | TEif of typ_texpr * typ_texpr * typ_texpr
  | TEdo of typ_texpr list
  | TElocbind of decl list * typ_texpr
  | TEcase of typ_texpr * ((typ_tpattern * typ_texpr) list)

and tbinding =
  | TBbind of ident * typ_texpr

and tdecl =
  | TDdefn of ident * (typ_tpattern list) * typ_texpr
  | TDinst of tinstance * (tdecl list)
    
type tprogram = tdecl list


(* Instance resolution checks *)

let str_of_inst inst =
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
        (fun inst ->
          { id = inst.id;
            args = List.map (type_copy_aux mapping) inst.args })
        v.insts }

let copy_func (f : func) =        
  let mapping = ref Imap.empty in
  { ret = type_copy_aux mapping f.ret;
    args = List.map (type_copy_aux mapping) f.args;
    insts =
      List.map
        (fun inst ->
          { id = inst.id;
            args = List.map (type_copy_aux mapping) inst.args })
        f.insts }

let copy_inst_scheme inst_s =
  let mapping = ref Imap.empty in
  { ded = List.map (type_copy_aux mapping) inst_s.ded;
    impl =
      List.map
        (fun inst ->
          { id = inst.id;
            args = List.map (type_copy_aux mapping) inst.args})
        inst_s.impl }

let copy_methods tpclass =
  let mapping = ref Imap.empty in
  (List.map (type_copy_aux mapping) tpclass.forms,
  List.fold_left
    (fun methods id ->
      Smap.add
        id
        (Some
          (match Smap.find id !gvenv with
            | V v ->
              V
                { typ = type_copy_aux mapping v.typ;
                  insts =
                    List.map
                      (fun inst ->
                        { id = inst.id;
                          args = List.map (type_copy_aux mapping) inst.args })
                      v.insts }
            | F f ->
              F
                { ret = type_copy_aux mapping f.ret;
                  args = List.map (type_copy_aux mapping) f.args;
                  insts =
                    List.map
                      (fun inst ->
                        { id = inst.id;
                          args = List.map (type_copy_aux mapping) inst.args })
                      f.insts }
            | _ ->
              failwith "Shouldn't have happened."))
          methods)
    Smap.empty  
    tpclass.methods)

let rec is_solved tenv inst =
  match Smap.find inst.id tenv with
    | TTC tc ->
      List.exists
        (fun inst_s ->
            let inst_s = copy_inst_scheme inst_s in
              is_subst_typ_lists inst.args inst_s.ded && List.for_all (is_solved tenv) inst_s.impl)
        tc.insts
    | _ ->
      failwith ("Shouldn't have happened.")

let (to_be_checked : (inst * loc) Stack.t) = Stack.create ()


(*Pattern matching exhaustivity check*)

type pmatrix = typ_tpattern list list

exception Non_exhaust of loc_pattern list

let convert_to_pmatrix (brnchs : (typ_tpattern * typ_texpr) list) =
  (List.map (fun (p, _) -> [ p ]) brnchs : pmatrix)

let wildcards_list n =
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

let rec test_for_exhaustivity (pmat : pmatrix) =
  match pmat with
    | [] ->
      failwith "Shouldn't have happened."
    | pr :: _ ->
      (match pr with
        | [] ->
          ()
        | p :: pr'  ->
          (match List.exists
            (fun pr ->
              match (List.hd pr).pattern with
                | TPvar _ -> true
                | _ -> false)
            pmat with
            | true ->
              (try test_for_exhaustivity (List.map List.tl pmat)
              with Non_exhaust ps ->
                raise
                  (Non_exhaust
                    ({ loc = dummy_pos;
                      pattern = Pvar "_" } :: ps)))
            | _ ->
              (match p.typ with
                | t when t = _Int || t = _String ->
                  raise
                    (Non_exhaust (wildcards_list (List.length pr)))
                | t when t = _Boolean ->
                  (match List.exists
                    (fun pr ->
                      match (List.hd pr).pattern with
                        | TPcons Cbool true -> true
                        | _ -> false)
                    pmat with
                    | true ->
                      ()
                    | _ ->
                      raise
                        (Non_exhaust
                          ({ loc = dummy_pos;
                            pattern = Pcons (Cbool true) } ::
                          wildcards_list (List.length pr - 1))));
                  (match List.exists
                    (fun pr ->
                      match (List.hd pr).pattern with
                        | TPcons Cbool false -> true
                        | _ -> false)
                    pmat with
                    | true ->
                      ()
                    | _ ->
                      raise
                        (Non_exhaust
                          ({ loc = dummy_pos;
                            pattern = Pcons (Cbool false) } ::
                          wildcards_list (List.length pr - 1))));
                  (try test_for_exhaustivity (List.map List.tl pmat)
                  with Non_exhaust ps ->
                    raise
                      (Non_exhaust
                        ({ loc = dummy_pos;
                          pattern = Pvar "_" } :: ps)))
                | Tcstr (c, args) ->
                  let cstrs = Smap.map
                    (fun () -> ([] : pmatrix))
                    (match (Smap.find c !gtenv) with
                      | TD d ->
                        d.cstrs
                      | _ ->
                        failwith "Shouldn't have happened.") in
                  let sign =
                    List.fold_left
                      (fun sign pr ->
                        match (List.hd pr).pattern with
                          | TPcstr (cid, args) ->
                            let cpmat = Smap.find cid sign in
                            Smap.add cid ((args @ List.tl pr) :: cpmat) sign
                          | _ ->
                            failwith "Shouldn't have happened." )
                      cstrs pmat in
                    Smap.iter
                      (fun cid cpmat ->
                        let cstr_ar =
                          match Smap.find cid !gvenv with
                            | C cstr ->
                              List.length (cstr.args)
                            | _ ->
                              failwith "Shouldn't have happened." in
                        match cpmat with
                          | [] ->
                            raise
                            (Non_exhaust
                            ({ loc = dummy_pos;
                              pattern =
                                Pcstr
                                  (cid,
                                  wildcards_list cstr_ar) } ::
                              wildcards_list (List.length pr - 1)))
                          | _ ->
                            try test_for_exhaustivity cpmat
                            with Non_exhaust ps ->
                              let args, ps' = slice cstr_ar ps in
                              raise
                                (Non_exhaust
                                  ({ loc = dummy_pos;
                                    pattern = 
                                    Pcstr
                                    (cid, args) } ::
                                  ps')))
                      sign;
                | _ ->
                  failwith "Shouldn't have happened.")))


(*Typing functions*)

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
            raise (Typing_error ("Unification failure: could not unify type " ^ str_of_type t1 ^ " and type " ^ str_of_type t2 ^ ".", p.loc)))
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
      (try (match Smap.find v venv with
        | V x ->
          let x = copy_var x in
          List.iter 
            (fun inst ->
              Stack.push (inst, e.loc) to_be_checked)
            x.insts; 
          { expr = TEvar v;
            typ = x.typ }
        | F f ->
            let n = List.length f.args in
            raise (Typing_error ("Value " ^ v ^ " expects " ^ string_of_int n ^ " argument" ^ (if n > 1 then "s" else "") ^ ", but 0 was given.", e.loc))
        | _ ->
          failwith "Shouldn't have happened.")
      with Not_found ->
        raise (Typing_error ("Unknown value " ^ v ^ ".", e.loc)))
    | Ecstr (cid, args) ->
      (try (match Smap.find cid venv with
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
              raise (Typing_error ("Unification failure: could not unify type " ^ str_of_type t1 ^ " and type " ^ str_of_type t2 ^ ".", e.loc))
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
          List.iter 
            (fun inst ->
              Stack.push (inst, e.loc) to_be_checked)
            f.insts;
          (try unify_typ_lists f.args (List.map (fun e -> e.typ) targs);
            { expr = TEapp (fid, targs);
              typ = f.ret }
          with 
            | UnificationFailure (t1, t2) ->
              raise (Typing_error ("Unification failure: could not unify type " ^ str_of_type t1 ^ " with type " ^ str_of_type t2 ^ ".", e.loc))
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
      type_expr tenv (List.fold_left (type_binding tenv) venv binds) e
    | Eif (b, e1, e2) ->
      let tb = type_expr tenv venv b
      and te1 = type_expr tenv venv e1
      and te2 = type_expr tenv venv e2 in
      (try unify tb.typ _Boolean;
        unify te1.typ te2.typ;
          { expr = TEif (tb, te1, te2);
            typ = te1.typ }
      with UnificationFailure (t1, t2) ->
        raise (Typing_error ("Could not match type " ^ str_of_type t1 ^ " with type " ^ str_of_type t2 ^ ".", e.loc)))
    | Etyped (e, pt) ->
      let te = type_expr tenv venv e
      and ti = type_purestype tenv venv pt in
      (try unify te.typ ti;
        { expr = te.expr;
          typ = ti }
      with UnificationFailure (t1, t2) ->
        raise (Typing_error ("Could not match type " ^ str_of_type t1 ^ " with type " ^ str_of_type t2 ^ ".", e.loc)))
    | Edo es ->
      let tes = List.map (type_expr tenv venv) es in
      List.iter
        (fun te ->
          try unify te.typ (Tcstr ("Effect", [ Tcstr ("Unit", []) ])) with
            | UnificationFailure (t1, t2) -> raise (Typing_error ("Could not match type " ^ str_of_type t1 ^ " with type " ^ str_of_type t2 ^ ".", e.loc)))
        tes;
        { expr = TEdo tes;
          typ = Tcstr ("Effect", [ Tcstr ("Unit", []) ]) }
    | Ecase (e, brnchs) ->
      let te = type_expr tenv venv e
      and tpats =
        List.map
          (fun (p, _) -> type_pattern tenv venv Smap.empty p)
          brnchs in
      List.iter
        (fun ((tp : typ_tpattern), _) -> unify te.typ tp.typ)
        tpats;
      let varmapping = List.map
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
        brnchs varmapping in
      let te = List.hd tes
      and tbrnchs =
        List.map2 
          (fun (tp, _) te -> (tp, te)) tpats tes in
      List.iter (fun te' -> unify te.typ te'.typ) (List.tl tes);
      (try test_for_exhaustivity (convert_to_pmatrix tbrnchs)
      with Non_exhaust ps ->
        (match ps with
          | p :: [] ->
            raise (Typing_error ("A case expression could not be determined to cover all inputs: " ^ Pretty.str_of_pattern p ^ " is not covered.", e.loc))
          | _ ->
            failwith "Shouldn't have happened."));
      { expr = TEcase (te, tbrnchs);
        typ = te.typ }
      
and type_binding (tenv : tenv_element Smap.t) venv b =
  let Bbind (var, e) = b in
  Smap.add
    var
    (V
      { typ = (type_expr tenv venv e).typ; 
        insts = []}) venv

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
        raise (Typing_error ("Could not match type " ^ str_of_type t1 ^ " with type " ^ str_of_type t2 ^ ".", defn.loc)));
      Stack.iter
        (fun (inst, loc) ->
          match is_solved tenv inst with
            | true ->
              ()
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
                { pattern = TPvar v;
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
      let defn = compactifies_fun_dec (List.length argtypes) defns in
      (match defn.decl with
        | Ddefn (_, args, ret) ->
          (let tenv =
            List.fold_left
            (fun tenv v ->
              (match v with
                | _ when v <> "_" ->
                  (try let _ = Smap.find v tenv in
                    raise (Typing_error ("Type argument " ^ v ^ " appears more than once.", rettype.loc))
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
          let tenv =
            List.fold_left
              (fun tenv (linst : loc_instance) ->
                let Iinst (id, pts) = linst.instance in
                try 
                  match Smap.find id tenv with
                    | TTC tc ->
                      (match tc.ar = List.length pts with
                        | true ->
                          Smap.add id
                            (TTC
                              { ar = tc.ar;
                                methods = tc.methods;
                                forms = tc.forms;
                                insts =
                                  { ded = List.map (type_purestype tenv !gvenv) pts;
                                    impl = [] }
                                  :: tc.insts })
                            tenv
                        | _ ->
                          let m = List.length pts in
                          raise (Typing_error ("Type class " ^ id ^ " expects " ^ string_of_int tc.ar ^ " argument" ^ (if tc.ar > 1 then "s" else "") ^ ", but " ^ string_of_int m ^ (if m > 1 then " were" else " was") ^ " given", linst.loc)))
                    | _ ->
                      raise (Typing_error ("Unknown instance " ^ id ^ ".", linst.loc))
                with Not_found ->
                  raise (Typing_error ("Unknown instance " ^ id ^ ".", linst.loc)))
              tenv
              impls in
          let targtypes = List.map
            (fun pt -> clean_up (type_purestype tenv !gvenv pt))
            argtypes
          and trettype = clean_up (type_purestype tenv !gvenv rettype) in
          (match argtypes with
            | [] ->
              (try let _ = Smap.find fid !gvenv in
                raise (Typing_error ("Value " ^ fid ^ " has been defined several times.", ret.loc))
              with Not_found ->
                gvenv :=
                  Smap.add
                    fid
                    (V
                      { typ = generalise mapping trettype;
                        insts = [] })
                    !gvenv)
            | _ ->
              (try let _ = Smap.find fid !gvenv in
                raise (Typing_error ("Value " ^ fid ^ " has been defined several times.", ret.loc))
              with Not_found ->
                gvenv :=
                  Smap.add
                    fid
                    (F 
                      { args = List.map (generalise mapping) targtypes;
                        ret = generalise mapping trettype;
                        insts = [] })
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
      and mapping = Smap.add_seq (List.to_seq (List.map (fun v -> (v, { id = new_id (); def = None })) vars)) Smap.empty in
      let t = generalise mapping (Tcstr (tcid, List.map (fun v -> Tvar v) vars)) in
      let cstr_ids = List.fold_left
        (fun cstr_ids (cid, args) ->
          let targs = List.map (type_purestype tenv !gvenv) args in
          try let _ = Smap.find cid !gvenv in
            raise (Typing_error ("Declaration for data constructor " ^ cid ^ " conflicts with an existing object of the same name.", d.loc))
          with Not_found ->
            gvenv := Smap.add cid
              (C
                { args = List.map (generalise mapping) targs;
                  typ = t })
              !gvenv;
            Smap.add cid () cstr_ids) Smap.empty cstrs in
      (try let _ = Smap.find tcid !gtenv in
        raise (Typing_error ("Declaration for type " ^ tcid ^ " conflicts with an existing object of the same name.", d.loc))
      with Not_found ->
        gtenv :=
          Smap.add tcid
            (TD 
            { ar = List.length vars;
              cstrs = cstr_ids}) !gtenv;
      None)
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
            let tenv =
              List.fold_left2
                (fun tenv inst (linst : loc_instance) ->
                  try 
                    match Smap.find inst.id tenv with
                      | TTC tc ->
                        (match tc.ar = List.length inst.args with
                          | true ->
                            Smap.add inst.id
                              (TTC
                                { ar = tc.ar;
                                  methods = tc.methods;
                                  forms = tc.forms;
                                  insts =
                                    { ded = inst.args;
                                      impl = [] }
                                    :: tc.insts })
                              tenv
                          | _ ->
                            let m = List.length inst.args in
                            raise (Typing_error ("Type class " ^ inst.id ^ " expects " ^ string_of_int tc.ar ^ " argument" ^ (if tc.ar > 1 then "s" else "") ^ ", but " ^ string_of_int m ^ (if m > 1 then " were" else " was") ^ " given", linst.loc)))
                      | _ ->
                        raise (Typing_error ("Unknown type class " ^ inst.id ^ ".", linst.loc))
                  with Not_found ->
                    raise (Typing_error ("Unknown type class " ^ inst.id ^ ".", linst.loc)))
                tenv
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
                            type_defn tenv v.typ [] (compactifies_fun_dec 0 defns) :: tdefns
                          | Some (F f) ->
                            Smap.add fid None methods,
                            type_defn tenv f.ret f.args (compactifies_fun_dec (List.length f.args) defns) :: tdefns
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
            gtenv :=
              Smap.add
                iid
                (TTC
                  { ar = tc.ar;
                    forms = tc.forms;
                    methods = tc.methods;
                    insts =
                      { ded = gen_args;
                        impl =
                          List.map
                          (fun inst ->
                            { id = inst.id;
                              args = List.map (generalise mapping) inst.args}) impls } :: tc.insts })
                !gtenv;
            Some (TDinst (TIinst (iid, ded.args), tdefns))
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