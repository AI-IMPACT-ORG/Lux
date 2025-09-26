Require Import M3Coq RGCoq.

Lemma src_pattern_sigma6 : src_of Sigma6 = [PortReg; PortReg; PortReg].
Proof. reflexivity. Qed.

Lemma src_pattern_tensor : src_of Tensor = [PortReg; PortReg].
Proof. reflexivity. Qed.

Lemma src_pattern_wire : src_of Wire = [InputReg; OutputReg].
Proof. reflexivity. Qed.

Lemma sigma6_renormalise_twice : renormalise 2 Sigma6 = {| input_arity := input_arity (arity_of Sigma6); output_arity := output_arity (arity_of Sigma6) * 2 |}.
Proof. reflexivity. Qed.
