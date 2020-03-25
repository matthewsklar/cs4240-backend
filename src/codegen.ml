open Lexing
open TigerIR

let example_program =
  let open TigerIR.Ir in
  let main_body =
    [ Assign ("__x", Int 0);
      ArrayAssign ("__xs", 3, Ident "__x");
      Assign ("__n", Ident "__x");
      Label "start";
      ArrayStore (Ident "__n", "__xs", Ident "__n");
      Add ("__n", Ident "__n", Int 1);
      Brgeq ("start", Ident "__n", Int 3);
      Callr ("__x", "do_stuff", [Ident "__x"; Ident "__n"; Int 3; Int 6; Int 7]) ] in
  let main_data = { floatList = []; intList = [
    Scalar "__x";
    Array ("__xs", 3);
    Scalar "__n"
  ] } in
  let main = {
    name = "main";
    returnType = None;
    params = [];
    data = main_data;
    body = main_body
  } in
  let do_stuff = {
    name = "do_stuff";
    returnType = Some TyInt;
    params = [("a", TyInt); ("b", TyInt); ("c", TyInt); ("d", TyInt);
              ("e", TyInt); ("f", TyInt); ("g", TyInt)];
    data = { floatList = []; intList = [] };
    body = [Return (Int 100)]
  } in
  [main; do_stuff]

let string_of_position filename lexbuf =
  let pos = lexbuf.lex_curr_p in
  Printf.sprintf "%s:%d:%d"
    filename
    pos.pos_lnum
    (pos.pos_cnum - pos.pos_bol + 1)

let read_file eval filename =
  let ic = open_in filename in
  let lexbuf = Lexing.from_channel ic in
  match Parser.program Lexer.read lexbuf with
  | exception Lexer.SyntaxError msg ->
    Printf.fprintf stderr "Syntax error: %s at %s\n"
      (string_of_position filename lexbuf)
      msg
  | exception _ ->
    Printf.fprintf stderr "Syntax error at %s\n"
      (string_of_position filename lexbuf)
  | prog -> eval prog

let eval out_filename ~allocator prog =
  let out_file = open_out out_filename in
  let prog' = Isel.compile_program ~allocator prog in
  output_string out_file prog'

let () =
  let in_filename = ref ""
  and out_filename = ref ""
  and alloc = ref "naive" in
  let arg_spec = Arg.[
    "-i", Set_string in_filename, "Input IR file";
    "-o", Set_string out_filename, "Output IR file";
    "--allocator", Set_string alloc, "Type of allocator to use";
  ] in
  let program_name = Sys.argv.(0) in
  Arg.parse arg_spec ignore (Printf.sprintf "Usage: %s -i <input_file> -o <output_file> --allocator <allocator>\n" program_name);
  if !in_filename = "" then begin
    Printf.eprintf "Error: No input file given!\n";
    exit 1
  end;
  if !out_filename = "" then begin
    Printf.eprintf "Error: No output file given!\n";
    exit 1
  end;
  let allocator fn body =
    let preallocs = Alloc.init_mapping fn body in
    let (allocs, new_spills) = match !alloc with
    | "naive" -> Alloc.naive fn preallocs body
    | "graph" -> Alloc.chaitin_briggs fn preallocs body
    | _ -> Printf.eprintf "Error: invalid allocator type\n";
           exit 1 in
    (Alloc.apply_allocations allocs body, new_spills) in
  read_file (eval !out_filename ~allocator) !in_filename
