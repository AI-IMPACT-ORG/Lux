<!-- (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use. -->

Shortlist of quick-win paper tweaks (to align with the reference mechanisation)

This note pinpoints where the paper can be minimally softened or clarified so that statements precisely match the current Racket implementation. Each item: what the paper claims, what the code does, and the smallest safe text tweak.

1) Exp/Log two-sided identity
- Paper (A6): rec∘dec = id_B and dec∘rec = id_(Z×Z×Z×Core)
- Code: rec∘dec = id_B holds; dec∘rec = id now holds for rec-constructed tuples and in the Z³ header demo (LUX_HEADER_MODEL=Z3); otherwise headers are schematic.
- Text tweak: “In the reference mechanisation we rely on rec∘dec = id_B and tuple NF collapse; dec∘rec is guaranteed on rec-constructed tuples, and in intended models (Z³) it recovers headers.”

2) Idempotent/selective ⊕_B
- Paper: ⊕_B idempotent and selective under dominance order
- Code: Idempotent on identical values; optional selective mode behind LUX_B_SELECT.
- Text tweak: “Intended models use idempotent/selective ⊕_B; the reference mechanisation is symbolic by default and provides idempotence on identical values (and an optional selective mode). Uses hereafter only require the multiplicative law and NF collapse.”

3) Observer homomorphisms ν*
- Paper (A2): ν* are semiring homomorphisms plus retractions
- Code: Homomorphic on im(ι*)/0/1; globally, homomorphism is reliable after projector reconstitution ρ; global mixed sum caveat remains.
- Text tweak: “ν* are homomorphisms on im(ι*) and after projector reconstitution ρ (or in the 2BI quotient). Retractions hold globally.”

4) B-valued normaliser [[·]]
- Paper (Def. 4.2): header-only B-normaliser present
- Code: Tuple NF is primary; now ‘B-normalize’ is an alias to header-only NF at the B-level.
- Text tweak: “We use tuple NF; [[·]] is schematic in ports and is instantiated as header-only NF in the reference build.”

5) Basepoint/G₄ axiom
- Paper (A7): constants a₀…a₃ and G₄ with G₄(a₀,…,a₃)=0_B
- Code: Not used by proofs/tests.
- Text tweak: Move to “Optional constants” or mark A7 as conservative extension (not used in this build).

6) ℤ³ header model example
- Paper (Ex. 4.1): concrete Z³ header model
- Code: Default abstract headers; Z³ model available as a runtime mode (LUX_HEADER_MODEL=Z3)
- Text tweak: “Illustrative (not default). The reference build uses abstract headers (dec returns zeros) for model agnosticism.”

7) Braided operators (A5)
- Paper: ad_i preserve headers, Core automorphism with braid relations
- Code: ad_i act as identity in the reference build (braid relations hold trivially); non-trivial Core automorphisms are reserved for ports.
- Text tweak: “In the reference mechanisation ad_i are the identity (braid relations hold trivially); non-trivial automorphisms live in ports.”

8) Guarded negation scope (Def. 4.4)
- Paper: general lattice-ordered semiring story
- Code: Instantiated on an ordered/numeric semiring for L; general case schematic
- Text tweak: “In the reference mechanisation L is a concrete ordered semiring; the general Heyting/Boolean case is schematic here and not used by tests.”

9) “Bulk = two boundaries” (Thm. 4.1)
- Paper: observer equality with residual invisible to observers
- Code: Matches; equality is indeed observational
- Text tweak: Emphasise observer-form equality (“residual invisible to observers”), not extensional B-equality.

10) Normaliser naming in ports
- Paper: [[·]]_{μ_L,θ_L,μ_R,θ_R} used inside ports
- Code: Port-local normalisers are identity by default; header-only [[·]] is schematic.
- Text tweak: “Port normaliser is identity unless stated; header-only [[·]] is schematic (instantiated as header-only NF in the build).”

11) Equality hierarchy and ‘idempotent normaliser’ wording
- Paper (Prop. 4.1 note): idempotence refers to tuple NF
- Code: Matches
- Text tweak: Add “In code, ‘idempotent’ always refers to tuple NF.”

12) “Observers vs Ports” box placement
- Paper: currently later in A2
- Code: Precisely splits algebraic ν* and semantic ports
- Text tweak: Move the box immediately after A2 and include the mixed-sum caveat (item 3) and the “after ρ” clarification.

Anchors in code (helpful for cross-referencing)
- Rec/dec: src/algebra/explog-decomposition.rkt
- B-add and observers: src/algebra/algebraic-structures.rkt
- Header model toggle: LUX_HEADER_MODEL env; see explog-decomposition.rkt
- B-normalize: src/moduli/moduli-system.rkt:B-normalize
- Gap kernel and port propagation: src/logic/gap-kernel.rkt; src/ports/*/gap-view.rkt

These tweaks are minimal and preserve every proof dependency while aligning the claims with the mechanised contracts.
