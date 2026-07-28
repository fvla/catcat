(* Smoke test for the extracted reference interpreter.

   Runs each example from R05_Driver against the demo dictionary and prints the
   result. This is the executable check that P01's specification and P02's
   machine actually produce a working evaluator -- until P03's parser exists,
   these hand-built terms are the only programs there are. *)

let fuel = Z.of_int 10_000

let run_example (name, term) =
  let result = R05_Driver.eval R05_Driver.demo_dict fuel term [] in
  Printf.printf "%-12s %s\n" name (R05_Driver.render_result result)

let () =
  print_endline "catcat reference interpreter -- examples";
  print_endline "";
  List.iter run_example R05_Driver.examples
