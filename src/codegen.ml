let example_program =
  let open TigerIR.Ir in
  [ Assign ("__x", Int 0);
    ArrayAssign ("__xs", 3, Ident "__x");
    Assign ("__n", Ident "__x");
    Label "start";
    ArrayStore (Ident "__n", "__xs", Ident "__n");
    Add ("__n", Ident "__n", Int 1);
    Brgeq ("start", Ident "__n", Int 3);
    Callr ("__x", "do_stuff", [Ident "__x"; Ident "__n"; Int 3; Int 6; Int 7]) ]

let () =
  print_endline (Passes.compile example_program)
