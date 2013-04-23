open OUnit

let tests =
  "InvarGenT" >::: [TermsTest.tests; InferTest.tests; NumSTest.tests;
                    AbductionTest.tests; DisjElimTest.tests;
                    InvariantsTest.tests]

let () = ignore (OUnit.run_test_tt ~verbose:true tests)
