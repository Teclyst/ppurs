{

  open Lexing
  open Parser

  exception Lexing_error of string

  let keywords = Hashtbl.create 32
  let () = List.iter (fun (s,t) -> Hashtbl.add keywords s t)
  [
    ("case", CASE);
    ("class", CLASS);
    ("where", WHERE);
    ("data", DATA);
    ("instance", INST);
    ("of", OF);
    ("do", DO);
    ("if", IF);
    ("then", THEN);
    ("else", ELSE);
    ("let", LET);
    ("in", IN);
    ("forall", FORALL);
    ("import", IMPRT);
    ("module", MODULE);
    ("true", BOOL true);
    ("false", BOOL false)
  ]

  let imports = Hashtbl.create 4
  let () = List.iter (fun (s,t) -> Hashtbl.add imports s t)
  [
    ("Prelude", PREL);
    ("Effect", EF);
    ("Effect.Console", EFCONS)
  ]
  
  let symbols = Hashtbl.create 32
  let () = List.iter (fun (s,t) -> Hashtbl.add symbols s t)
  [
    ("||", OR);
    ("&&", AND);
    ("==", EQ);
    ("/=", NEQ);
    (">=", GEQ);
    (">", GT);
    ("<=", LEQ);
    ("<", LT);
    ("+", ADD);
    ("-", SUB);
    ("<>", CONC);
    ("*", MUL);
    ("/", DIV);
    ("=", BIND);
    ("::", DBLCOL);
    ("|", BAR);
    ("->", TO);
    ("=>", IMPL);
    (".", DOT);
    (",", COM)
  ]

}

let digit = ['0' - '9']
let lower = ['a' - 'z' '_']
let upper = ['A' - 'Z']
let other = digit | lower | upper | [''']
let symbchar = ['|' '&' '=' '!' '>' '<' '+' '-' '*' '/' ':' '.' ',']
let uident = upper (other | ['.']) *
let lident = lower (other) *

rule token = parse
  | [' ' '\t'] +
    { token lexbuf }
  | ['\n']
    { Lexing.new_line lexbuf; token lexbuf }
  | "{-"
    { comment 0 lexbuf }
  | "--"
    { comment 1 lexbuf }
  | "Main"
    { MAIN }
  | eof
    { EOF }
  | lident as lid
    { try Hashtbl.find keywords lid
      with Not_found -> LIDENT lid }
  | uident as uid
    { try let t = Hashtbl.find imports uid in
        Hashtbl.remove imports uid;
        t
      with Not_found -> UIDENT uid }
  | [ '0' ] | [ '1' - '9' ] digit * as s
    { INT (int_of_string s) }
  | [ '0' ] digit *
    { raise (Lexing_error ("Unexpected leading zeros.")) }
  | ['\"']
    { str [] lexbuf }
  | ['(']
    { LPAR }
  | [')']
    { RPAR }
  | symbchar + as sid
    { try Hashtbl.find symbols sid
      with Not_found -> raise (Lexing_error ("Unexpected token '" ^ sid ^ "'.")) }
  | _ as c
    { raise (Lexing_error ("Unexpected token '" ^ (String.make 1 c) ^ "'.")) }

and comment cmmttype = parse
  | "-}"
    { match cmmttype with
        | 0 -> token lexbuf
        | 1 -> comment 1 lexbuf
        | _ -> failwith "Shouldn't have happened." }
  | '\n'
    { Lexing.new_line lexbuf;
      match cmmttype with
        | 0 -> comment 0 lexbuf
        | 1 -> token lexbuf
        | _ -> failwith "Shouldn't have happened." }
  | eof
    { EOF }
  | _
    { comment cmmttype lexbuf }

and str acc = shortest
  | "\\\""
    { str ('\"' :: acc) lexbuf }
  | "\\n"
    { str ('\n' :: acc) lexbuf }
  | "\\\\"
    { str ('\\' :: acc) lexbuf }
  | ['\\'] [' ']
    { str_ignore acc lexbuf }
  | ['\\'] [^ ' ']
    { raise (Lexing_error "Illegal character escape code.") }
  | ['\"']
    { STR (String.of_seq (List.to_seq (List.rev acc))) }
  | eof
    { raise (Lexing_error "Unexpected end of input.") }
  | [ '\n' ]
    { raise (Lexing_error "Unexpected line feed in string literal.") }
  | [^ '\\'] as c
    { str (c :: acc) lexbuf }

and str_ignore acc = parse
  | ['\n']
    { Lexing.new_line lexbuf;
     str_ignore acc lexbuf }
  | [' ' '\t'] +
    { str_ignore acc lexbuf }
  | ['\\']
    { str acc lexbuf }
  | ['\"']
    { STR (String.of_seq (List.to_seq (List.rev acc))) }
  | [^ '\\' '\"' ' '] as c
    { raise (Lexing_error ("Unexpected character '" ^ String.make 1 c ^ "' in gap.")) }

{

  type stack_element = M | B of int

  let s = Stack.create ()

  let q = Queue.create ()

  let weakmode = ref false

  let column pos =
    pos.pos_cnum - pos.pos_bol

  let rec close c buf =
    match Stack.is_empty s with
      | true ->
        ()
      | false ->
        (match Stack.pop s with
        | M ->
          Stack.push M s
        | B n when n < c ->
          Stack.push (B n) s
        | B n when n = c ->
          Stack.push (B n) s;
          Queue.push SEMCOL q
        | B n ->
          Queue.push RBRA q;
          close c buf)

  let rec unstack buf =
    try
      match Stack.pop s with
        | M ->
          ()
        | _ ->
          Queue.push RBRA q;
          unstack buf
    with
      | Stdlib.Stack.Empty ->
        raise Parser.Error

  let lexer buf =
    (match Queue.is_empty q with
      | true ->
        let t = token buf in
        let c = column (Lexing.lexeme_start_p buf) in
        (match t with
          | IF | LPAR | CASE ->
            close c buf;
            if !weakmode then
              Stack.push (B c) s;
            Stack.push M s;
            Queue.push t q;
            weakmode := false
          | RPAR | THEN | ELSE | IN ->
            if !weakmode then
              (close c buf;
              Stack.push (B c) s);
            unstack buf;
            if t = THEN then
              Stack.push M s;
            Queue.push t q;
            weakmode := false
          | WHERE | DO | LET | OF ->
            close c buf;
            if !weakmode then
              Stack.push (B c) s;
            if t = LET then
              Stack.push M s;
            if t = OF then
              unstack buf;
            Queue.push t q;
            Queue.push LBRA q;
            weakmode := true
          | EOF ->
            close (- 1) buf;
            Queue.push EOF q
          | _ ->
            close c buf;
            if !weakmode then
              Stack.push (B c) s;
            Queue.push t q;
            weakmode := false)
      | _ ->
        ());
    Queue.pop q

}