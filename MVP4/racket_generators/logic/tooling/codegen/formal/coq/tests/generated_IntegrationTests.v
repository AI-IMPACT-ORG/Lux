Require Import lib.generated_Core.
Require Import lib.generated_Observers.
Require Import lib.generated_Kernels.

(* CLEAN v10 Integration Tests *)

Module IntegrationTests.

(* Test: End-to-end workflow *)
Definition test_end_to_end : Prop :=
  let h := header 2.0 3.0 in
  let t := make_term 'test_term h 'test_core in
  let obs := observer_value t in
  term_equal obs t.

End IntegrationTests.