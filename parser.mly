%{

  open Ast

%}

(* Token declaration. *)

%token INIT EOF

%token <string> UIDENT LIDENT
%token LPAR RPAR LBRA RBRA COM SEMCOL DBLCOL

%token <bool> BOOL
%token <int> INT
%token <string> STR
%token AND OR EQ NEQ GEQ GT LEQ LT
%token ADD SUB MUL DIV
%token CONC
%token IF THEN ELSE LET IN DO CASE OF

%token BIND TO BAR IMPL FORALL DOT
%token DATA CLASS INST WHERE

(* Priorities and associativities. *)

%nonassoc IN ELSE
%left OR
%left AND
%nonassoc EQ NEQ GEQ GT LEQ LT
%left ADD SUB CONC
%left MUL DIV
%nonassoc UNSUB

(* Starting Point. *)

%start <file> file

%%

(* Grammar. *)

sep_list(t, n):
  | 
    { [] }
  | x = n
    { x :: [] }
  | x = n; t; ns = sep_list(t, n)
    { x :: ns }

nempt_sep_list(t, n):
  | x = n
    { x :: [] }
  | x = n; t; ns = sep_list(t, n)
    { x :: ns } 

file:
  INIT; ds = nempt_sep_list(SEMCOL, decl); EOF
    { ds }

decl:
  | d = defn
    { d }
  | d = tdecl
    { d }
  | DATA; did = UIDENT; forms = LIDENT *; BIND; cstrs = nempt_sep_list(BAR, cstrdecl)
    { Ddata (did, forms, cstrs) }
  | CLASS; cid = UIDENT; forms = LIDENT *; WHERE; LBRA; cvars = sep_list(SEMCOL, tdecl); RBRA
    { Dclass (cid, forms, cvars) }
  | INST; inst = instance; WHERE; LBRA; ivars = sep_list(SEMCOL, defn); RBRA
    { let (impls, t) = inst in Dinst (impls, t, ivars) } 

cstrdecl:
  cid = UIDENT; args = atype *
    { (cid, args) }

defn:
  | fid = LIDENT; args = patarg *; BIND; e = expr
    { Ddefn (fid, args, e) }

tdecl:
  | var = LIDENT; DBLCOL; impls = nempt_sep_list(IMPL, ntype)
    { let h :: t = List.rev impls in
      Dtdecl (var, [], List.rev t, h :: []) }
  | var = LIDENT; DBLCOL; FORALL; forms = LIDENT +; DOT; impls = nempt_sep_list(IMPL, ntype)
    { let h :: t = List.rev impls in
      Dtdecl (var, forms, List.rev t, h :: []) }
  | var = LIDENT; DBLCOL; FORALL; forms = LIDENT +; DOT; impls = nempt_sep_list(IMPL, ntype); TO; tos = nempt_sep_list(TO, purstype)
    { let h :: t = List.rev impls in
      Dtdecl (var, forms, List.rev t, h :: tos) }
  | var = LIDENT; DBLCOL; impls = nempt_sep_list(IMPL, ntype); TO; tos = nempt_sep_list(TO, purstype)
    { let h :: t = List.rev impls in
      Dtdecl (var, [], List.rev t, h :: tos) }

ntype:
  | t = UIDENT
    { Tat t }
  | t = cstrntype
    { t }

cstrntype:
  cstr = UIDENT; args = atype +
    { Tcstr (cstr, args) }

atype:
  | t = LIDENT
    { Tat t }
  | t = UIDENT
    { Tat t }
  | LPAR; t = purstype; RPAR
    { t }

purstype:
  | t = atype
    { t }
  | t = cstrntype
    { t }

instance:
  | t = ntype
    { ([], t) }
  | impl = ntype; IMPL; t = ntype
    { (impl :: [], t) }
  | LPAR; impls = nempt_sep_list(COM, ntype); RPAR; t = ntype
    { (impls, t) }

patarg:
  | c = constant
    { Pcons c }
  | form = LIDENT
    { Pform form }
  | form = UIDENT
    { Pform form }
  | LPAR; pat = pattern; RPAR
    { pat }

pattern:
  | pat = patarg
    { pat }
  | cstr = UIDENT; pats = patarg +
    { Pcstr (cstr, pats) }

constant:
  | b = BOOL
    { Cbool b }
  | i = INT
    { Cint i }
  | s = STR
    { Cstr s}

atom:
  | c = constant
    { Econs c }
  | var = LIDENT
    { Evar var }
  | var = UIDENT
    { Evar var }
  | LPAR; e = expr; RPAR
    { e }
  | LPAR; e = expr; DBLCOL; t = purstype; RPAR
    { Etyped (e, t) }

expr:
  | at = atom
    { at }
  | e1 = expr; b = OR; e2 = expr
    { Eapp ("(||)", e1 :: e2 :: [])}
  | e1 = expr; b = AND; e2 = expr
    { Eapp ("(&&)", e1 :: e2 :: [])}
  | e1 = expr; b = EQ; e2 = expr
    { Eapp ("(==)", e1 :: e2 :: [])}
  | e1 = expr; b = NEQ; e2 = expr
    { Eapp ("(!=)", e1 :: e2 :: [])}
  | e1 = expr; b = GEQ; e2 = expr
    { Eapp ("(>=)", e1 :: e2 :: [])}
  | e1 = expr; b = GT; e2 = expr
    { Eapp ("(>)", e1 :: e2 :: [])}
  | e1 = expr; b = LEQ; e2 = expr
    { Eapp ("(<=)", e1 :: e2 :: [])}
  | e1 = expr; b = LT; e2 = expr
    { Eapp ("(<>)", e1 :: e2 :: [])}
  | e1 = expr; b = ADD; e2 = expr
    { Eapp ("(+)", e1 :: e2 :: [])}
  | e1 = expr; b = SUB; e2 = expr
    { Eapp ("(-)", e1 :: e2 :: [])}
  | e1 = expr; b = CONC; e2 = expr
    { Eapp ("(<>)", e1 :: e2 :: [])}
  | e1 = expr; b = MUL; e2 = expr
    { Eapp ("(*)", e1 :: e2 :: [])}
  | e1 = expr; b = DIV; e2 = expr
    { Eapp ("(/)", e1 :: e2 :: [])}
  | SUB; e = expr
    { Eopp e }
    %prec UNSUB
  | f = LIDENT; ats = atom +
    { Eapp (f, ats) }
  | cstr = UIDENT; ats = atom +
    { Eapp (cstr, ats) }
  | IF; e1 = expr; THEN; e2 = expr; ELSE; e3 = expr
    { Eif (e1, e2, e3) }
  | DO; LBRA; es = nempt_sep_list(SEMCOL, expr); RBRA
    { Edo es }
  | LET; LBRA; bnds = nempt_sep_list(SEMCOL, binding); RBRA; IN; e = expr
    { Elocbind (bnds, e) }
  | CASE; e = expr; OF; LBRA; brchs = nempt_sep_list(SEMCOL, branch); RBRA
    { Ecase (e, brchs) }

binding:
  var = LIDENT; BIND; e = expr
    {Ddefn (var, [], e)}

branch:
  p = pattern; TO; e = expr
    { (p, e) }