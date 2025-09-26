Require Import M3Coq.

Definition scale_arity (scale : nat) (a : arity) : arity :=
  {| input_arity := input_arity a; output_arity := output_arity a * scale |}.

Definition renormalise (scale : nat) (k : EdgeKind) : arity :=
  scale_arity scale (arity_of k).

Lemma scale_arity_identity : forall a, scale_arity 1 a = a.
Proof. intros a. destruct a; simpl. reflexivity. Qed.

Lemma renormalise_base_sigma6 : renormalise 1 Sigma6 = arity_of Sigma6.
Proof. reflexivity. Qed.

Lemma renormalise_base_tensor : renormalise 1 Tensor = arity_of Tensor.
Proof. reflexivity. Qed.

Lemma renormalise_base_wire : renormalise 1 Wire = arity_of Wire.
Proof. reflexivity. Qed.

