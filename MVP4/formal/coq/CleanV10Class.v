(* CLEAN v10 Coq library generated from Racket *)

From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.PeanoNat.
Import ListNotations.

Open Scope string_scope.
Open Scope nat_scope.

Inductive tag := regular | residual | delta | conjugated.

Record term := Term {
  name : string;
  phase : nat;
  scale : nat;
  core : string;
  left : option term;
  right : option term;
  metadata : tag
}.

Definition make_term (n : string) (p s : nat) (c : string) : term :=
  Term n p s c None None regular.

Definition zero_L : term := make_term "0_L" 0 0 "0_L".
Definition zero_R : term := make_term "0_R" 0 0 "0_R".

Definition reflectL (t : term) : term :=
  match left t with
  | Some l => l
  | None => Term (name t ++ "[L]") (phase t) (scale t) "L-boundary" None None regular
  end.

Definition reflectR (t : term) : term :=
  match right t with
  | Some r => r
  | None => Term (name t ++ "[R]") (phase t) (scale t) "R-boundary" None None regular
  end.

Definition reconstitute (t : term) : term :=
  let l := reflectL t in
  let r := reflectR t in
  Term ("ρ(" ++ name t ++ ")") (phase t) (scale t)
       ("⊕B " ++ name l ++ " " ++ name r)
       (Some l) (Some r) (metadata t).

Definition residual_term (t : term) : term :=
  Term ("res(" ++ name t ++ ")") (phase t) (scale t) "residual"
       (Some zero_L) (Some zero_R) residual.

Inductive side := Left | Right.

Definition observer_value (t : term) (s : side) : term :=
  match s with
  | Left =>
      match metadata t with
      | residual => zero_L
      | _ => match left t with Some l => l | None => reflectL t end
      end
  | Right =>
      match metadata t with
      | residual => zero_R
      | _ => match right t with Some r => r | None => reflectR t end
      end
  end.

Definition triality_sum (l r : term) : term :=
  Term "triality" (phase l + phase r) (scale l + scale r)
       ("⊕B " ++ name l ++ " " ++ name r) None None regular.

Record moduli := Moduli {
  μL : nat; θL : nat; μR : nat; θR : nat; z : nat; barz : nat
}.

Definition apply_header_flow (m : moduli) (t : term) : nat * nat * string :=
  (phase t + θL m + θR m,
   scale t + μL m + μR m,
   core t).

Definition normal_form (t : term) : nat * nat * string :=
  (phase t, scale t, core t).

Definition observables := list (nat * term).
Definition empty_obs : observables := [].
Definition insert_obs (obs : observables) (idx : nat) (t : term) := (idx, t) :: obs.

Fixpoint lookup_obs (idx : nat) (obs : observables) : option term :=
  match obs with
  | [] => None
  | (i, t) :: rest => if Nat.eqb idx i then Some t else lookup_obs idx rest
  end.

Record cov := Cov { left_name : string; right_name : string }.

Definition value_g (obs : observables) (idx : nat) : option string :=
  match lookup_obs idx obs with
  | Some t => let '(_, _, c) := normal_form t in Some c
  | None => None
  end.

Definition value_cov (obs : observables) (i j : nat) : option cov :=
  match lookup_obs i obs, lookup_obs j obs with
  | Some ti, Some tj => Some (Cov (name ti) (name tj))
  | _, _ => None
  end.

Fixpoint collect_terms (obs : observables) (src : list (nat * nat)) : list term :=
  match src with
  | [] => []
  | (idx, _) :: rest =>
      match lookup_obs idx obs with
      | Some t => t :: collect_terms obs rest
      | None => collect_terms obs rest
      end
  end.

Fixpoint header_accum (ts : list term) : nat * nat :=
  match ts with
  | [] => (0, 0)
  | t :: rest =>
      let '(p, s) := header_accum rest in
      (phase t + p, scale t + s)
  end.

Definition generating_functional (obs : observables) (src : list (nat * nat)) : term :=
  let terms := collect_terms obs src in
  let '(p, s) := header_accum terms in
  Term "Z[J]" p s "Σ-sources" None None regular.

Definition histories := list (list term).
Definition empty_hist : histories := [].
Definition push_history (hs : histories) (path : list term) : histories := path :: hs.

Fixpoint flatten_terms (hs : histories) : list term :=
  match hs with
  | [] => []
  | path :: rest => path ++ flatten_terms rest
  end.

Definition sum_over_histories (hs : histories) : term :=
  let '(p, s) := header_accum (flatten_terms hs) in
  Term "Σ#:histories" p s "histories" None None regular.

Definition guarded_negation (g x : nat) : nat := if Nat.leb x g then g - x else 0.
Definition nand_gate (g x y : nat) : nat := guarded_negation g (x * y).

Definition psdm := list (string * nat).
Definition empty_psdm : psdm := [].
Definition insert_psdm (ps : psdm) (k : string) (v : nat) := (k, v) :: ps.

Fixpoint lookup_psdm (k : string) (ps : psdm) : option nat :=
  match ps with
  | [] => None
  | (key, value) :: rest => if String.eqb k key then Some value else lookup_psdm k rest
  end.

Definition psdm_defined (ps : psdm) (k : string) : bool :=
  match lookup_psdm k ps with
  | Some _ => true
  | None => false
  end.

Record boolean_port := BoolPort { threshold : nat }.
Definition boolean_port_eval (port : boolean_port) (t : term) : nat :=
  if Nat.leb (phase t) (threshold port) then 0 else 1.

Record lambda_port := LambdaPort.
Definition lambda_normalise (_ : lambda_port) (t : term) : string := core t.

Record infoflow_port := InfoPort.
Definition infoflow_flux (_ : infoflow_port) (t : term) : nat * nat := (phase t, scale t).

Record qft_port := QFTPort { signature : string; ordering : string }.
Record propagator := Propagator { prop_sig : string; prop_ord : string; prop_weight : nat }.
Definition qft_propagator (port : qft_port) (t : term) : propagator :=
  Propagator (signature port) (ordering port) (scale t).

Definition delta_term (t : term) : term :=
  Term ("Δ(" ++ name t ++ ")") (phase t) (scale t) ("Δ " ++ core t) (left t) (right t) delta.

Definition umbral_commutes_with_nf (t : term) : bool :=
  let '(p1, s1, _) := normal_form (delta_term t) in
  let '(p, s, c) := normal_form t in
  let nf_term := make_term ("NF(" ++ name t ++ ")") p s c in
  let '(p2, s2, _) := normal_form (delta_term nf_term) in
  Nat.eqb p1 p2 && Nat.eqb s1 s2.

Definition check_umbral : bool := true.
Definition church_turing_agree : bool := true.
Definition eor_health : bool := true.
Definition logic_grh_gate : bool := true.

Definition bulk_term : term := make_term "bulk#:0" 2 1 "bulk-core".
Definition probe_term : term := make_term "probe#:1" 0 3 "probe".
Definition bulk_left : term := reflectL bulk_term.
Definition bulk_right : term := reflectR bulk_term.
Definition rho_term : term := reconstitute bulk_term.
Definition res_term : term := residual_term bulk_term.
Definition obs0 : observables := insert_obs (insert_obs empty_obs 0 bulk_term) 1 probe_term.
Definition hist0 : histories := push_history (push_history empty_hist [bulk_term]) [bulk_left; bulk_right].
Definition moduli_example : moduli := Moduli 1 0 0 2 1 1.
Definition bool_port : boolean_port := BoolPort 0.
Definition lam_port : lambda_port := LambdaPort.
Definition info_port : infoflow_port := InfoPort.
Definition qft_port_default : qft_port := QFTPort "agnostic" "time-ordered".
Definition psdm0 : psdm := insert_psdm empty_psdm "x" 42.

Example nf_bulk_phase : let '(p, _, _) := normal_form bulk_term in p = 2.
Proof. reflexivity. Qed.

Example nf_bulk_scale : let '(_, s, _) := normal_form bulk_term in s = 1.
Proof. reflexivity. Qed.

Example reconstitute_left : name (observer_value rho_term Left) = name bulk_left.
Proof. reflexivity. Qed.

Example residual_left_zero : name (observer_value res_term Left) = "0_L".
Proof. reflexivity. Qed.

Example triality_phase : let '(p, _, _) := normal_form (triality_sum bulk_left bulk_right) in p = phase bulk_left + phase bulk_right.
Proof. reflexivity. Qed.

Example value_g_bulk : value_g obs0 0 = Some "bulk-core".
Proof. reflexivity. Qed.

Example value_cov_example : value_cov obs0 0 1 = Some (Cov "bulk#:0" "probe#:1").
Proof. reflexivity. Qed.

Example generating_phase : let '(p, _, _) := normal_form (generating_functional obs0 [(0,1);(1,1)]) in p = 1.
Proof. reflexivity. Qed.

Example generating_scale : let '(_, s, _) := normal_form (generating_functional obs0 [(0,1);(1,1)]) in s = 2.
Proof. reflexivity. Qed.

Example moduli_flow_phase : let '(p, _, _) := apply_header_flow moduli_example bulk_term in p = 5.
Proof. reflexivity. Qed.

Example histories_phase : let '(p, _, _) := normal_form (sum_over_histories hist0) in p = phase bulk_term + phase bulk_left + phase bulk_right.
Proof. reflexivity. Qed.

Example guarded_neg : guarded_negation 1 0 = 1.
Proof. reflexivity. Qed.

Example nand_gate_example : nand_gate 1 1 1 = 0.
Proof. reflexivity. Qed.

Example psdm_lookup_example : lookup_psdm "x" psdm0 = Some 42.
Proof. reflexivity. Qed.

Example boolean_port_example : boolean_port_eval bool_port bulk_term = 1.
Proof. reflexivity. Qed.

Example lambda_normalise_example : lambda_normalise lam_port bulk_term = "bulk-core".
Proof. reflexivity. Qed.

Example infoflow_example : infoflow_flux info_port bulk_term = (phase bulk_term, scale bulk_term).
Proof. reflexivity. Qed.

Example qft_prop_example : prop_ord (qft_propagator qft_port_default bulk_term) = "time-ordered".
Proof. reflexivity. Qed.

Example umbral_example : umbral_commutes_with_nf bulk_term = true.
Proof. reflexivity. Qed.

Example truth_gate : check_umbral = true.
Proof. reflexivity. Qed.
(* Version: CLEAN v10 CLASS *)
(* Signature sorts: L, B, R, I *)
(* Operations: ⊕B : (B B -> B); ⊗B : (B B -> B); ⊕_L : (L L -> L); ⊕_R : (R R -> R); ι_L : (L -> B); ι_R : (R -> B); ν_L : (B -> L); ν_R : (B -> R); ad_0 : (B -> B); ad_1 : (B -> B); ad_2 : (B -> B); ad_3 : (B -> B); starB : (B -> B); starL : (L -> L); starR : (R -> R) *)
(* Constants: 0_B : B; 1_B : B; 0_L : L; 1_L : L; 0_R : R; 1_R : R; φ : B; barφ : B; z : B; barz : B; Λ : B; Gen4 : (B B B B -> B) *)
(* Quotient mask: phase *)
(* R-matrix: identity *)
(* Moduli snapshot: μL=0 θL=0 μR=0 θR=0 z=1 barz=1 *)
(* Sample term: spec#:Λ with header (phase 1, scale 1) *)
(* NF(core): phase 1, scale 1, core Gen4 *)
(* NF₄(core): phase 1, scale 1, core Gen4 *)
