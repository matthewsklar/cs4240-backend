open Lexing

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
  print_endline prog';
  output_string out_file prog'

let naive_allocator fn body =
  let preallocs = Alloc.init_mapping fn body in
  let (allocs, new_spills) = Alloc.naive fn preallocs body in
  (Alloc.apply_allocations allocs body, new_spills)

let chaitin_briggs_allocator fn body =
  let body_with_params = Isel.load_params TigerIR.(fn.params) body in
  let preallocs = Alloc.init_mapping fn body_with_params in
  let (allocs, new_spills) = Alloc.chaitin_briggs fn preallocs body_with_params in
  (Alloc.apply_allocations allocs body_with_params, new_spills)

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
  let allocator = match !alloc with
    | "naive" -> naive_allocator
    | "graph" -> chaitin_briggs_allocator
    | _ ->
      Printf.eprintf "Error: invalid allocator type\n";
      exit 1 in
  read_file (eval !out_filename ~allocator) !in_filename
