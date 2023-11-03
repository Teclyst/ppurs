type constant = 
  | Cbool of bool
  | Cint of int
  | Cstr of string

type ident =
  string

type purstype =
  | Tat of ident
  | Tcstr of ident * (purstype list)

type pattern =
  | Pcons of constant
  | Pid of ident
  | Pcstr of ident * (pattern list)

type expr =
  | Econs of constant
  | Evar of ident
  | Etyped of expr * purstype
  | Eapp of ident * (expr list)
  | Eif of expr * expr * expr
  | Edo of expr list
  | Elocbind of decl list * expr
  | Ecase of (pattern * expr) list

and decl =
  | Ddefn of ident * (pattern list) * expr
  | Dtdecl of ident * (ident list) * (purstype list) * (purstype list)
  | Ddata of ident * (ident list) * (( ident * purstype list) list)
  | Dclass of ident * (ident list) * (decl list)
  | Dinst of purstype list * purstype * (decl list)

(* Dclass _ should always match Dclass _ _ [Dtdecl _; ...; Dtdecl _]. *)
(* Dinst _ should always match Dinst [Tcstr _; ...; Tcstr] Tcstr [Ddef _; ...; Ddef _]. *)
  
type file = decl list
