Require Import CoreTests.
Require Import PropertyTests.
Require Import IntegrationTests.

(* CLEAN v10 Test Runner *)

Module TestRunner.

(* Run all tests *)
Definition run_all_tests : Prop :=
  test_header_addition /\
  test_header_multiplication /\
  test_kernel_associativity /\
  test_observer_value.

End TestRunner.