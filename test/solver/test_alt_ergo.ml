open Smtml
open Smtml_tests

let () =
  assert Alt_ergo_mappings.is_available;
  let module Test_solver_params = Test_solver_params.Make (Alt_ergo_mappings) in
  let module Test_solver = Test_solver.Make (Alt_ergo_mappings) in
  let module Test_bv = Test_bv.Make (Alt_ergo_mappings) in
  let module Test_fp = Test_fp.Make (Alt_ergo_mappings) in
  let module Test_lia = Test_lia.Make (Alt_ergo_mappings) in
  ()
