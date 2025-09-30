theory CLEAN_V10_Class
  imports Main
begin

definition cleanVersion :: string where
  "cleanVersion = 'CLEAN v10 CLASS'"

  text ‹Version: CLEAN v10 CLASS›
  text ‹Signature sorts: L, B, R, I›
  text ‹Operations: ⊕B : (B B -> B); ⊗B : (B B -> B); ⊕_L : (L L -> L); ⊕_R : (R R -> R); ι_L : (L -> B); ι_R : (R -> B); ν_L : (B -> L); ν_R : (B -> R); ad_0 : (B -> B); ad_1 : (B -> B); ad_2 : (B -> B); ad_3 : (B -> B); starB : (B -> B); starL : (L -> L); starR : (R -> R)›
  text ‹Constants: 0_B : B; 1_B : B; 0_L : L; 1_L : L; 0_R : R; 1_R : R; φ : B; barφ : B; z : B; barz : B; Λ : B; Gen4 : (B B B B -> B)›
  text ‹Quotient mask: phase›
  text ‹R-matrix: identity›
  text ‹Moduli snapshot: μL=0 θL=0 μR=0 θR=0 z=1 barz=1›
  text ‹Sample term: spec#:Λ with header (phase 1, scale 1)›
  text ‹NF(core): phase 1, scale 1, core Gen4›
  text ‹NF₄(core): phase 1, scale 1, core Gen4›

end
