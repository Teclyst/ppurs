open Format
open Lexing
open Ast

let parse_only = ref false
and type_only = ref false

let ifile = ref ""
let ofile = ref ""

let set_file f s = f := s
  
let options =
  [ ("--parse-only",
    Arg.Set parse_only,
    " To stop after parsing.");
    ("--type-only",
    Arg.Set type_only,
    " To stop after typing.");
    ("-o",
    Arg.String (set_file ofile),
    " To set the output's name.") ]
  
let usage = "usage: ppurs [option] file.purs"

let print_loc loc =
  eprintf "File \"%s\", line %d, characters %d-%d:\n" !ifile loc.lnum loc.cnum (loc.cnum + 1)

let () =
  Arg.parse options (set_file ifile) usage;
  if !ifile = ""
    then
      (eprintf "No file to compile\n@?";
      exit 1);
  if !ofile = ""
    then ofile := Filename.chop_suffix !ifile ".purs" ^ ".s";
  if not (Filename.check_suffix !ifile ".purs")
    then
      (eprintf "File must have .purs extension\n@?";
      Arg.usage options usage;
      exit 1);
  let f = open_in !ifile in
  let buf = Lexing.from_channel f in
  try
    let p = Parser.file Lexer.lexer buf in
    close_in f;
    if !parse_only then exit 0;
    let p = Typing.compactifies p in
    let tp = Typing.type_program p in
    if !type_only then exit 0;
    Compile.compile_program tp !ofile;
    exit 0
  with
    | Lexer.Lexing_error c ->
      print_loc (localisation (Lexing.lexeme_start_p buf));
      eprintf "Lexing error: %s@." c;
      exit 1
    | Parser.Error ->
      print_loc (localisation (Lexing.lexeme_start_p buf));
      eprintf "Syntax error.@.";
      exit 1
    | Typing.Typing_error (c, loc) ->
      print_loc loc;
      eprintf "Typing error: %s@." c;
      exit 1
    | Failure c ->
      print_loc { lnum = 0; cnum = 0 };
      eprintf "Compiler error: %s@." c;
      exit 2