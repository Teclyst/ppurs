%{

  open Ast

%}

(* Token declaration. *)

%token MODULE MAIN IMPRT PREL EF EFCONS EOF

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

%start <program> file

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
  | x = n; t; ns = nempt_sep_list(t, n)
    { x :: ns } 

nempt_sep_list_diff_end(t, m, n):
  | y = n
    { ([], y) }
  | x = m; t; ms = nempt_sep_list_diff_end(t, m, n)
    { let (l, y) = ms in
      (x :: l, y) }

file:
  | MODULE; MAIN; WHERE; LBRA; IMPRT; PREL; SEMCOL; IMPRT; EF; SEMCOL; IMPRT; EFCONS; RBRA; EOF
    { [] }
  | MODULE; MAIN; WHERE; LBRA; IMPRT; PREL; SEMCOL; IMPRT; EF; SEMCOL; IMPRT; EFCONS ; SEMCOL ; ds = nempt_sep_list(SEMCOL, decl); RBRA; EOF
    { ds }

decl:
  | d = defn
    { d }
  | d = tdecl
    { d }
  | DATA; did = UIDENT; forms = LIDENT *; BIND; cstrs = nempt_sep_list(BAR, cstrdecl)
    { { loc = localisation $startpos;
        decl = Ddata (did, forms, cstrs) } }
  | CLASS; cid = UIDENT; forms = LIDENT *; WHERE; LBRA; cvars = sep_list(SEMCOL, tdecl); RBRA
    { { loc = localisation $startpos;
        decl = Dclass (cid, forms, cvars) } }
  | INST; inst = instances; WHERE; LBRA; ivars = sep_list(SEMCOL, defn); RBRA
    { let (impls, t) = inst in
      { loc = localisation $startpos;
        decl = Dinst (impls, t, ivars) } } 

cstrdecl:
  cid = UIDENT; args = atype *
    { (cid, args) }

defn:
  | fid = LIDENT; args = patarg *; BIND; e = expr
    { { loc = localisation $startpos;
        decl = Ddefn (fid, args, e) } }

tdecl:
  | var = LIDENT; DBLCOL; FORALL; forms = LIDENT +; DOT; impls = nempt_sep_list_diff_end(IMPL, instance, purstype)
    { let (insts, ret) = impls in
      { loc = localisation $startpos;
        decl = Dtdecl (var, forms, insts, [], ret) } }
  | var = LIDENT; DBLCOL; impls = nempt_sep_list_diff_end(IMPL, instance, purstype)
    { let (insts, ret) = impls in
      { loc = localisation $startpos;
        decl = Dtdecl (var, [], insts, [], ret) } }
  | var = LIDENT; DBLCOL; FORALL; forms = LIDENT +; DOT; impls = nempt_sep_list_diff_end(IMPL, instance, purstype); TO; tos = nempt_sep_list_diff_end(TO, purstype, purstype)
    { let (insts, arg) = impls
      and (args, ret) = tos in
      { loc = localisation $startpos;
        decl = Dtdecl (var, forms, insts, arg :: args, ret) } }
  | var = LIDENT; DBLCOL; impls = nempt_sep_list_diff_end(IMPL, instance, purstype); TO; tos = nempt_sep_list_diff_end(TO, purstype, purstype)
    { let (insts, arg) = impls
      and (args, ret) = tos in
      { loc = localisation $startpos;
        decl = Dtdecl (var, [], insts, arg :: args, ret) } }

ntype:
  cstr = UIDENT; args = atype +
    { { loc = localisation $startpos;
        purstype = PTcstr (cstr, args) } }

atype:
  | t = LIDENT
    { { loc = localisation $startpos;
        purstype = PTvar t } }
  | t = UIDENT
    { { loc = localisation $startpos;
        purstype = PTcstr (t, []) } }
  | LPAR; t = purstype; RPAR
    { t }

purstype:
  | t = atype
    { t }
  | t = ntype
    { t }

instances:
  | i = instance
    { ([], i) }
  | impl = instance; IMPL; i = instance
    { (impl :: [], i) }
  | LPAR; impls = nempt_sep_list(COM, instance); RPAR; IMPL; i = instance
    { (impls, i) }

instance:
  iid = UIDENT; args = atype *
    { { loc = localisation $startpos;
        instance = Iinst (iid, args) } }

patarg:
  | c = constant
    { { loc = localisation $startpos;
        pattern = Pcons c } }
  | var = LIDENT
    { { loc = localisation $startpos;
        pattern = Pvar var } }
  | cstr = UIDENT
    { { loc = localisation $startpos;
        pattern = Pcstr (cstr, []) } }
  | LPAR; pat = pattern; RPAR
    { pat }

pattern:
  | pat = patarg
    { pat }
  | cstr = UIDENT; pats = patarg +
    { { loc = localisation $startpos;
        pattern = Pcstr (cstr, pats) } }

constant:
  | b = BOOL
    { Cbool b }
  | i = INT
    { Cint i }
  | s = STR
    { Cstr s}

atom:
  | c = constant
    { { loc = localisation $startpos;
        expr = Econs c } }
  | var = LIDENT
    { { loc = localisation $startpos;
        expr = Evar var } }
  | cstr = UIDENT
    { { loc = localisation $startpos;
        expr = Ecstr (cstr, []) } }
  | LPAR; e = expr; RPAR
    { e }
  | LPAR; e = expr; DBLCOL; t = purstype; RPAR
    { { loc = localisation $startpos;
        expr = Etyped (e, t) } }

expr:
  | at = atom
    { at }
  | e1 = expr; OR; e2 = expr
    { { loc = localisation $startpos;
        expr = Eapp ("disj", e1 :: e2 :: [])} }
  | e1 = expr; AND; e2 = expr
    { { loc = localisation $startpos;
        expr = Eapp ("conj", e1 :: e2 :: [])} }
  | e1 = expr; EQ; e2 = expr
    { { loc = localisation $startpos;
        expr = Eapp ("eq", e1 :: e2 :: [])} }
  | e1 = expr; NEQ; e2 = expr
    { { loc = localisation $startpos;
        expr = Eapp ("notEq", e1 :: e2 :: [])} }
  | e1 = expr; GEQ; e2 = expr
    { { loc = localisation $startpos;
        expr = Eapp ("greaterThanOrEq", e1 :: e2 :: [])} }
  | e1 = expr; GT; e2 = expr
    { { loc = localisation $startpos;
        expr = Eapp ("greaterThan", e1 :: e2 :: [])} }
  | e1 = expr; LEQ; e2 = expr
    { { loc = localisation $startpos;
        expr = Eapp ("lessThanOrEq", e1 :: e2 :: [])} }
  | e1 = expr; LT; e2 = expr
    { { loc = localisation $startpos;
        expr = Eapp ("lessThan", e1 :: e2 :: [])} }
  | e1 = expr; ADD; e2 = expr
    { { loc = localisation $startpos;
        expr = Eapp ("add", e1 :: e2 :: [])} }
  | e1 = expr; SUB; e2 = expr
    { { loc = localisation $startpos;
        expr = Eapp ("sub", e1 :: e2 :: [])} }
  | e1 = expr; CONC; e2 = expr
    { { loc = localisation $startpos;
        expr = Eapp ("append", e1 :: e2 :: [])} }
  | e1 = expr; MUL; e2 = expr
    { { loc = localisation $startpos;
        expr = Eapp ("mul", e1 :: e2 :: [])} }
  | e1 = expr; DIV; e2 = expr
    { { loc = localisation $startpos;
        expr = Eapp ("div", e1 :: e2 :: [])} }
  | SUB; e = expr
    { { loc = localisation $startpos;
        expr = Eapp ("negate", e :: []) } }
    %prec UNSUB
  | f = LIDENT; ats = atom +
    { { loc = localisation $startpos;
        expr = Eapp (f, ats) } }
  | cstr = UIDENT; ats = atom +
    { { loc = localisation $startpos;
        expr = Ecstr (cstr, ats) } }
  | IF; e1 = expr; THEN; e2 = expr; ELSE; e3 = expr
    { { loc = localisation $startpos;
        expr = Eif (e1, e2, e3) } }
  | DO; LBRA; es = nempt_sep_list(SEMCOL, expr); RBRA
    { { loc = localisation $startpos;
        expr = Edo es } }
  | LET; LBRA; bnds = nempt_sep_list(SEMCOL, binding); RBRA; IN; e = expr
    { { loc = localisation $startpos;
        expr = Elocbind (bnds, e) } }
  | CASE; e = expr; OF; LBRA; brchs = nempt_sep_list(SEMCOL, branch); RBRA
    { { loc = localisation $startpos;
        expr = Ecase (e, brchs) } }

binding:
  var = LIDENT; BIND; e = expr
    { Bbind (var, e) }

branch:
  p = pattern; TO; e = expr
    { (p, e) }