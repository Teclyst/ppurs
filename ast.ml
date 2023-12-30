type loc =
  { lnum: int;
    cnum: int }

let localisation (pos: Lexing.position) =
  { lnum = pos.pos_lnum;
    cnum = pos.pos_cnum - pos.pos_bol }

type constant = 
  | Cbool of bool
  | Cint of int
  | Cstr of string

type ident =
  string

type loc_purstype =
  { loc: loc;
    purstype: purstype }

and purstype =
  | PTvar of ident
  | PTcstr of ident * (loc_purstype list)

type loc_instance =
  { loc: loc;
    instance: instance }

and instance =
  | Iinst of ident * (loc_purstype list)

type loc_pattern =
  { loc: loc;
    pattern: pattern }

and pattern =
  | Pcons of constant
  | Pvar of ident
  | Pcstr of ident * (loc_pattern list)

type loc_expr =
  { loc: loc;
    expr: expr }

and expr =
  | Econs of constant
  | Evar of ident
  | Etyped of loc_expr * loc_purstype
  | Eapp of ident * (loc_expr list)
  | Ecstr of ident * (loc_expr list)
  | Eif of loc_expr * loc_expr * loc_expr
  | Edo of loc_expr list
  | Elocbind of binding list * loc_expr
  | Ecase of loc_expr * ((loc_pattern * loc_expr) list)

and loc_decl =
  { loc : loc;
    decl : decl }

and decl =
  | Ddefn of ident * (loc_pattern list) * loc_expr
  | Dtdecl of ident * (ident list) * (loc_instance list) * (loc_purstype list) * loc_purstype
  | Ddata of ident * (ident list) * ((ident * loc_purstype list) list)
  | Dclass of ident * (ident list) * (loc_decl list)
  | Dinst of loc_instance list * loc_instance * (loc_decl list)
  | Dcmpted of loc_decl * (loc_decl list) (*The list should consist of Ddefn equations*)

and binding =
  | Bbind of ident * loc_expr

type program = loc_decl list