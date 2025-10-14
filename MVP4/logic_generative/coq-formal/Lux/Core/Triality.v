(* (c) 2025 AI.IMPACT GmbH *)

From Coq Require Import ZArith.
From Lux.Core Require Import Signature Axioms Observers NF.

Module Triality (S:LuxSignature).
  Module Ax := Axioms(S).
  Module Obs := Observers(S).
  Module N := NF(S).
  Module L := S.L.
  Module R := S.R.
  Module B := S.B.

  (* Triality functors *)
  Definition T_L (t:B.carrier) : L.carrier := S.nuL t.
  Definition T_R (t:B.carrier) : R.carrier := S.nuR t.
  Definition T_B (x_L:L.carrier) (x_R:R.carrier) : B.carrier := 
    B.add (S.iotaL x_L) (S.iotaR x_R).

  (* Typed conjugations (optional RC) *)
  Parameter starB : B.carrier -> B.carrier.
  Parameter starL : L.carrier -> L.carrier.
  Parameter starR : R.carrier -> R.carrier.

  (* Conjugation axioms *)
  Axiom starB_antinv : forall t u, starB (B.mul t u) = B.mul (starB u) (starB t).
  Axiom starB_idem : forall t, starB (starB t) = t.
  
  Axiom starL_antinv : forall x y, starL (L.mul x y) = L.mul (starL y) (starL x).
  Axiom starL_idem : forall x, starL (starL x) = x.
  
  Axiom starR_antinv : forall x y, starR (R.mul x y) = R.mul (starR y) (starR x).
  Axiom starR_idem : forall x, starR (starR x) = x.

  (* Compatibility with embeddings *)
  Axiom starB_iotaL : forall x, starB (S.iotaL x) = S.iotaL (starL x).
  Axiom starB_iotaR : forall y, starB (S.iotaR y) = S.iotaR (starR y).

  (* Header conjugation (swaps z ↔ z̄) *)
  Axiom starB_headers : forall t,
    let '(k,mz,mbar,c) := let '(h,c0) := S.dec t in (fst (fst h), snd (fst h), snd h, c0) in
    let '(k',mz',mbar',c') := let '(h',c1) := S.dec (starB t) in (fst (fst h'), snd (fst h'), snd h', c1) in
    k' = k /\ mz' = mbar /\ mbar' = mz.

  (* Moduli conjugation *)
  Parameter star_moduli : (Z * Z) -> (Z * Z).
  Axiom star_moduli_swap : forall μL θL μR θR,
    star_moduli (μL, θL) = (μR, θR) /\
    star_moduli (μR, θR) = (μL, θL).

End Triality.

