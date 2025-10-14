From Coq Require Import ZArith List.
From Lux.Core Require Import Signature Axioms Observers NF Triality.

Module Cumulants (S:LuxSignature).
  Module Ax := Axioms(S).
  Module Obs := Observers(S).
  Module N := NF(S).
  Module T := Triality(S).
  Module L := S.L.
  Module R := S.R.
  Module B := S.B.

  (* Observable registration *)
  Parameter Obs : nat -> B.carrier -> Prop.
  Axiom Obs_well_typed : forall i t, Obs i t -> exists c:B.carrier, t = c.

  (* Generating functional *)
  Definition Z_J (J : nat -> L.carrier) (I_fin : list nat) : L.carrier :=
    let terms := List.map (fun i => B.add B.one (B.mul (S.iotaL (J i)) (B.one))) I_fin in
    let product := List.fold_left B.mul terms B.one in
    S.nuL (N.NF_B product).

  (* Couplings *)
  Definition g (i : nat) : L.carrier :=
    S.nuL (N.NF_B (B.one)).

  (* Connected Green's functions *)
  Definition G (i j : nat) : L.carrier :=
    S.nuL (N.NF_B (B.one)).

  (* Beta fields *)
  Definition beta_phi (i : nat) : L.carrier :=
    S.nuL (N.NF_B (B.one)).

  Definition beta_mu (i : nat) : L.carrier :=
    S.nuL (N.NF_B (B.one)).

  (* Monotones *)
  Definition a : L.carrier :=
    S.nuL (N.NF_B (B.one)).

  Definition c : L.carrier :=
    S.nuL (N.NF_B (B.one)).

  (* Delta operators (finite differences) *)
  Parameter Delta : nat -> (L.carrier -> L.carrier) -> L.carrier -> L.carrier.
  Axiom Delta_commutes_NF : forall i F t,
    Delta i F (S.nuL (N.NF_B t)) = S.nuL (N.NF_B (S.iotaL (Delta i F (S.nuL t)))).

  (* Schwinger-Dyson identities *)
  Axiom schwinger_dyson : forall i F,
    Delta i F (Z_J (fun _ => L.zero) nil) = L.zero.

End Cumulants.
