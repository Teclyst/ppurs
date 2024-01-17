open Ast
open Parser

let print_token =
  fun tok ->
    match tok with
      | ADD ->
        "ADD"
      | AND ->
        "AND"
      | BAR ->
        "BAR"
      | BIND ->
        "BIND"
      | BOOL b ->
        "BOOL " ^ string_of_bool b
      | CASE ->
        "CASE"
      | CLASS ->
        "CLASS"
      | COM ->
        "COM"
      | CONC ->
        "CONC"
      | DATA ->
        "DATA"
      | DBLCOL ->
        "DBLCOL"
      | DIV ->
        "DIV"
      | DO ->
        "DO"
      | DOT ->
        "DOT"
      | EF ->
        "EF"
      | EFCONS ->
        "EFCONS"
      | ELSE ->
        "ELSE"
      | EOF ->
        "EOF"
      | EQ ->
        "EQ"
      | FORALL ->
        "FORALL"
      | GEQ ->
        "GEQ"
      | GT ->
        "GT"
      | IF ->
        "IF"
      | IMPL ->
        "IMPL"
      | IMPRT ->
        "IMPRT"
      | IN ->
        "IN"
      | INST ->
        "INST"
      | INT i ->
        "INT " ^ string_of_int i
      | LBRA ->
        "LBRA"
      | LEQ ->
        "LEQ"
      | LET ->
        "LET"
      | LIDENT s ->
        "LIDENT " ^ s 
      | LPAR ->
        "LPAR"
      | LT ->
        "LT"
      | MAIN ->
        "MAIN"
      | MODULE ->
        "MODULE"
      | MUL ->
        "MUL"
      | NEQ ->
        "NEQ"
      | OF ->
        "OF"
      | OR ->
        "OR"
      | PREL ->
        "PREL"
      | RBRA ->
        "RBRA"
      | RPAR ->
        "RPAR"
      | SEMCOL ->
        "SEMCOL"
      | STR s ->
        "STR " ^ s
      | SUB ->
        "SUB"
      | THEN ->
        "THEN"
      | TO ->
        "TO"
      | UIDENT s ->
        "UIDENT " ^ s
      | WHERE ->
        "WHERE"

let print_file q =
  Queue.iter (fun (_, t) -> print_endline (print_token t)) q

let white_space i =
  print_string(String.make i ' ')

let str_of_const c =
  match c with
    | Cbool b ->
      string_of_bool b
    | Cint i ->
      string_of_int i
    | Cstr s ->
      "\"" ^ s ^ "\""

let str_of_pattern p =
  let rec aux init p =
    match p.pattern with
      | Pvar v ->
        v
      | Pcons c ->
        str_of_const c
      | Pcstr (cid, args) when List.length args = 0 || init ->
        String.concat " " (cid :: List.map (aux false) args)
      | Pcstr (cid, args) ->
        "(" ^ String.concat " " (cid :: List.map (aux false) args) ^ ")" in
  aux true p