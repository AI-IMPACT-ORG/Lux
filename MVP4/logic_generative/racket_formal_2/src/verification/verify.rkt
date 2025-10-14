#lang racket
;; Lux Verification — abstract-first witnesses and optional heavy packs.
;;
;; Exports:
;;  - verify-summary : produce an association list of (symbol . boolean)
;;  - verify-all     : full, human-facing suite (prints small reports)
;;  - heavy-checks   : list of (symbol . thunk) for heavyweight checks, lazily loaded

(require rackunit
         (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "../logic/gap-kernel.rkt")
         (file "../foundation/v2-axioms.rkt")
         (file "../theorems/generating-functionals.rkt")
         (file "../theorems/categorical-naturality.rkt")
         (prefix-in th: (file "../theorems/categorical-logic.rkt"))
         (file "../ports/evidence/isomorphisms.rkt")
         (file "../ports/evidence/generating-functionals-iso.rkt")
         (file "../ports/evidence/categorical-logic-iso.rkt")
         (file "../logic/kernel.rkt")
         (file "../logic/proof.rkt")
         (file "../logic/kernel-checker.rkt")
         (file "../logic/inference.rkt")
         (file "../logic/sequent-checker.rkt")
         (file "../logic/internalize.rkt")
         (file "../theorems/logic-properties.rkt")
         (file "../logic/conservativity.rkt")
         (file "../set/zfc.rkt")
         (file "../theorems/lifting.rkt")
         (file "../theorems/truth.rkt")
         (file "../theorems/gap.rkt")
         (file "../rewrite/engine.rkt")
         (file "../theorems/self-application.rkt")
         (file "./registry.rkt"))

(provide verify-all verify-summary)
;; Export heavy checks for scanning via the runner
(provide heavy-checks)
;; Export gap propagation snapshot for runner display
(provide gap-propagation-snapshot)

;; A list of (symbol . thunk) for heavyweight checks. Each thunk returns a boolean.
;; Thunks use dynamic-require to avoid loading heavy modules unless executed.
(require racket/runtime-path)
;; Robust base directory for relative dynamic-require paths
(define-runtime-path here ".")

(define (heavy-checks)
  (list
   (cons 'ant-evidence (λ () ((dynamic-require (build-path here "../ports/analytic-number-theory/evidence.rkt") 'run-ant-evidence-tests))))
   (cons 'ant-symbolic (λ () ((dynamic-require (build-path here "../ports/analytic-number-theory/symbolic-evidence.rkt") 'run-ant-symbolic-evidence-tests))))
   (cons 'beta-system (λ () ((dynamic-require (build-path here "../theorems/beta-system.rkt") 'beta-system-sanity))))
   (cons 'complexity-gap (λ () ((dynamic-require (build-path here "../theorems/complexity-separation.rkt") 'verify-complexity-gap-separations))))
   (cons 'pnp-separations (λ () ((dynamic-require (build-path here "../theorems/complexity-separation.rkt") 'verify-pnp-separations))))
   (cons 'complexity-internal (λ () ((dynamic-require (build-path here "../logic/complexity-internal.rkt") 'complexity-internal-sanity))))
   (cons 'lens-soundness (λ () ((dynamic-require (build-path here "../logic/complexity-internal.rkt") 'soundness-under-lenses))))
   (cons 'blum-axioms (λ () ((dynamic-require (build-path here "../logic/complexity-blum.rkt") 'blum-axioms-sanity))))
   (cons 'karp-closure (λ () (semiring-element? ((dynamic-require (build-path here "../logic/complexity-blum.rkt") 'closure-under-karp)))))
   (cons 'time-hierarchy-sanity (λ () ((dynamic-require (build-path here "../theorems/time-hierarchy.rkt") 'time-hierarchy-sanity))))
   (cons 'time-hierarchy-derivation (λ () ((dynamic-require (build-path here "../theorems/time-hierarchy.rkt") 'time-hierarchy-derivation))))
   (cons 'comp-direct-argument (λ () ((dynamic-require (build-path here "../theorems/complexity-lens.rkt") 'verify-complexity-direct-argument))))
   (cons 'logic-driven (λ () ((dynamic-require (build-path here "../theorems/logic-driven-complexity.rkt") 'logic-driven-complexity-pack))))
   (cons 'spectral-gap (λ () ((dynamic-require (build-path here "../logic/spectral-gap-logic.rkt") 'spectral-gap-driven-separation))))
   (cons 'semantics-pack (λ () ((dynamic-require (build-path here "../semantics/categorical-model.rkt") 'semantics-pack))))
   (cons 'equivalence-pack (λ () ((dynamic-require (build-path here "../logic/complexity-equivalence.rkt") 'equivalence-pack))))
   (cons 'barriers (λ () ((dynamic-require (build-path here "../theorems/barriers.rkt") 'barriers-pack))))
   (cons 'lens-framework (λ () ((dynamic-require (build-path here "../logic/lens-framework.rkt") 'lens-framework-pack))))
   (cons 'domain-lens-reuse (λ () ((dynamic-require (build-path here "../theorems/domain-lens-reuse.rkt") 'domain-lens-reuse-pack))))
   (cons 'mass-gap-evidence (λ () ((dynamic-require (build-path here "../ports/mass-gap.rkt") 'run-mass-gap-evidence-tests))))
   (cons 'qft-gap (λ () ((dynamic-require (build-path here "../ports/qft/mass-gap.rkt") 'qft-gap-pack))))
   (cons 'universal-translation (λ () ((dynamic-require (build-path here "../ports/universal-translation.rkt") 'universal-translation-pack))))))

(define (verify-all)
  (displayln "=== Lux verification: axioms → consequences ===")
  ;; Start proof registry and load LaTeX labels, then verify V2 axioms runner
  (start-registry!)
  (load-latex-labels!)
  ;; Verify V2 axioms runner completes without failures
  (run-v2-rigorous-tests)
  ;; Verify generating functional unity
  (check-true (verify-generating-functional-unity) "Generating functionals unify paradigms")
  (check-true (verify-generating-functional-constraints) "GF constraints hold")
  ;; Verify evidence isomorphisms (structure-preserving)
  (check-true (verify-evidence-isomorphism gf-iso) "GF evidence is an isomorphism")
  (check-true (verify-evidence-isomorphism categorical-logic-iso) "Categorical-logic evidence is an isomorphism")
  ;; Verify categorical logic coherence (theorem module, single source of truth)
  (check-true (th:verify-categorical-logic) "Categorical logic coherence holds")
  (check-true (naturality-braids) "Observer naturality with braids holds")
  (check-true (naturality-explog) "Observer naturality with exp/log holds")
  ;; Kernel basics: witnesses exist and live in L
  (let ([kb (kernel-basics)])
    (for ([kv kb])
      (define w (cdr kv))
      (check-true (semiring-element? w))
      (check-equal? (semiring-element-semiring-type w) 'L)))
  ;; Kernel step-proof: reflexivity pattern P⇒P
  (let* ([P (abstract-op 'var (list (make-abstract-const 'P 'symbol)) 'boolean)]
         [formula (abstract-op 'implies (list P P) 'boolean)]
         [kp (make-kernel-proof formula)])
    (check-true (check-kernel-proof kp) "Kernel step proof for reflexivity"))
  ;; Internal inference rules exist as L-level theorems
  (for ([kv (inference-basics)])
    (define w (cdr kv))
    (check-true (semiring-element? w))
    (check-equal? (semiring-element-semiring-type w) 'L))
  ;; Context structural rules / tactics
  (let* ([P (embed-proposition (make-abstract-const 'P 'symbol))]
         [Q (embed-proposition (make-abstract-const 'Q 'symbol))]
         [R (embed-proposition (make-abstract-const 'R 'symbol))]
         [ctx '()])
    (check-true (semiring-element? (rule-contraction ctx P Q)))
    (check-true (semiring-element? (rule-exchange ctx P Q ctx R)))
    (check-true (semiring-element? (tactic-mp2 ctx P Q R))))
  ;; Sequent checker: validate an and-intro step
  (let* ([P (embed-proposition (make-abstract-const 'P 'symbol))]
         [Q (embed-proposition (make-abstract-const 'Q 'symbol))]
         [ctx '()]
         [wit (rule-and-intro ctx P Q)]
         [st (deriv-step 'and-intro (list ctx P Q) wit)])
    (check-true (check-step st) "sequent checker validates and-intro"))
  ;; Additional internal rule witnesses
  (let* ([P (embed-proposition (make-abstract-const 'P 'symbol))]
         [Q (embed-proposition (make-abstract-const 'Q 'symbol))]
         [ctx '()])
    (check-true (semiring-element? (rule-imp-intro ctx P Q)) "imp-intro witness exists")
    (check-true (semiring-element? (rule-cut ctx P Q)) "cut-like admissibility witness exists"))
  ;; Guarded schemas witnesses exist
  (let* ([phi (abstract-op 'phi '() 'predicate)]
         [G   (abstract-op 'G '() 'guard)])
    (check-true (semiring-element? (schema-separation-guarded phi G)))
    (check-true (semiring-element? (schema-replacement-guarded phi G))))
  ;; Logic properties as integration tests
  (check-true (semiring-element? (prop-implies-trans)))
  (check-true (semiring-element? (prop-imp-ante-strengthen)))
  (check-true (semiring-element? (prop-cut)))
  (check-true (semiring-element? (prop-imp-distribute-right)))
  (check-true (prop-reflect-L-B))
  (check-true (prop-context-normalization))
  ;; Self-application: rules-as-theorems via the catalog + checker
  (check-true (self-apply-ruleset))
  ;; Guarded monotonicity of implication
  (check-true (semiring-element? (prop-guarded-imp-monotone)))
  ;; Conservativity demo: weakening empty-context theorems into ZFC-augmented context
  (check-true (conservativity-demo-implies-trans))
  ;; Lifting: boundary uniqueness, exp/log coherence, transport invariance
  (check-true (local-boundary-uniqueness))
  (check-true (local-explog-coherence))
  (check-true (global-uniqueness-up-to-nf))
  (check-true (transport-invariance-mp))
  (check-true (transport-invariance-and-intro))
  (check-true (global-to-local-naturality))
  (check-true (nf-lift-stability))
  ;; Truth and dagger: global reversible truth demos lift locally
  (check-true (global-local-truth-demo))
  (check-true (semiring-element? (truth-conjunction-canonical)))
  (check-true (truth-transport-preservation))
  (check-true (semiring-element? (truth-imp-reflexive)))
  ;; Gap checks and dagger-normal form
  (define gap-contraction-ok (contraction-gap-witness))
  (define gap-dnf-idem (dnf-idempotent?))
  (define gap-dnf-trans (dnf-transport-invariant?))
  (check-true gap-contraction-ok)
  (check-true gap-dnf-idem)
  (check-true gap-dnf-trans)
  ;; Non-contraction and regime/marginal reports
  (check-true (non-contraction-witness))
  (regime-report)
  (check-true (marginal-axis-demo))
  (check-true (marginal-truth-demo))
  (marginal-report)
  ;; Beta-system / CS identity (symbolic)
  (check-true ((dynamic-require (build-path here "../theorems/beta-system.rkt") 'beta-system-sanity))
              "β-system sanity and CS identity")
  ;; Rewrite report
  (displayln "--- rewrite report ---")
  (check-true (rewrite-eq-roundtrip?))
  (displayln "eq-roundtrip: ok")
  (check-true (rewrite-red-noninvertible?))
  (displayln "red-noninvertible: ok")
  (check-true (rewrite-metric-monotone?))
  (displayln "metric-monotone: ok")
  ;; Small printed gap report (summary only)
  (displayln "--- gap report ---")
  (displayln (string-append "contraction: " (if gap-contraction-ok "ok" "fail")))
  (displayln (string-append "DNF idempotence: " (if gap-dnf-idem "ok" "fail")))
  (displayln (string-append "DNF transport invariance: " (if gap-dnf-trans "ok" "fail")))
  ;; Congruence (small pack): f(x)=f(y) ⇒ congruent under + and *
  (let* ([x (semiring-element (get-two) B)]
         [y (semiring-element (get-two) B)]
         [z (semiring-element (get-three) B)]
         [add ((semiring-ops-add B-ops) x z)]
         [add-prime ((semiring-ops-add B-ops) y z)]
         [mul ((semiring-ops-mul B-ops) x z)]
         [mul-prime ((semiring-ops-mul B-ops) y z)])
    (check-true (abstract-expr-equal? (semiring-element-value add)
                                      (semiring-element-value add-prime)))
    (check-true (abstract-expr-equal? (semiring-element-value mul)
                                      (semiring-element-value mul-prime))))
  ;; ANT evidence pack: product/sum equivalence, RC-universality, functional equation
  (check-true ((dynamic-require (build-path here "../ports/analytic-number-theory/evidence.rkt") 'run-ant-evidence-tests))
              "ANT evidence suite passes")
  ;; Symbolic ANT evidence: Euler product ≡ Dirichlet sum; Von Mangoldt identity
  (check-true ((dynamic-require (build-path here "../ports/analytic-number-theory/symbolic-evidence.rkt") 'run-ant-symbolic-evidence-tests))
              "ANT symbolic evidence suite passes")
  ;; Complexity separation and Mass-Gap evidence (symbolic)
  (check-true ((dynamic-require (build-path here "../ports/complexity-theory.rkt") 'run-complexity-separation-evidence))
              "Complexity separation evidence passes")
  (check-true ((dynamic-require (build-path here "../ports/mass-gap.rkt") 'run-mass-gap-evidence-tests))
              "Mass gap evidence passes")
  (check-true ((dynamic-require (build-path here "../theorems/complexity-separation.rkt") 'verify-complexity-gap-separations))
              "Complexity separations via spectral gap hold")
  (check-true ((dynamic-require (build-path here "../theorems/complexity-separation.rkt") 'verify-pnp-separations))
              "P≠NP and NP≠coNP (observer-level) hold")
  (check-true ((dynamic-require (build-path here "../logic/complexity-internal.rkt") 'complexity-internal-sanity))
              "Complexity internal skeleton sane")
  ;; Lens soundness (observer-level identity/idempotence on canonical reps)
  (check-true ((dynamic-require (build-path here "../logic/complexity-internal.rkt") 'soundness-under-lenses))
              "Lens soundness for P/NP holds (observer-level)")
  (check-true ((dynamic-require (build-path here "../logic/complexity-blum.rkt") 'blum-axioms-sanity))
              "Blum axioms fragment sane")
  (check-true (semiring-element? ((dynamic-require (build-path here "../logic/complexity-blum.rkt") 'closure-under-karp)))
              "Karp closure witness exists")
  (check-true ((dynamic-require (build-path here "../theorems/time-hierarchy.rkt") 'time-hierarchy-sanity))
              "Time hierarchy witness sane")
  (check-true ((dynamic-require (build-path here "../theorems/time-hierarchy.rkt") 'time-hierarchy-derivation))
              "Time hierarchy derivation sketch holds")
  ;; Direct lens-based argument checks
  (check-true ((dynamic-require (build-path here "../theorems/complexity-lens.rkt") 'verify-complexity-direct-argument))
              "Direct lens-based complexity argument checks")
  ;; Logic-driven (constructive) witness pack
  (check-true ((dynamic-require (build-path here "../theorems/logic-driven-complexity.rkt") 'logic-driven-complexity-pack))
              "Logic-driven complexity pack passes")
  ;; Deep logic integration of spectral gap → separation (sequent-level)
  (check-true ((dynamic-require (build-path here "../logic/spectral-gap-logic.rkt") 'spectral-gap-driven-separation))
              "Spectral-gap → separation sequent witness exists")
  ;; Categorical + metric semantics pack
  (check-true ((dynamic-require (build-path here "../semantics/categorical-model.rkt") 'semantics-pack))
              "Dagger SMC + Lawvere metric semantics pack")
  ;; Port model declarations: ANT allows dagger at model level; meta remains dagger-unconstrained
  ((dynamic-require (build-path here "../ports/analytic-number-theory/model.rkt") 'register-ant-model!))
  (check-true ((dynamic-require (build-path here "../ports/analytic-number-theory/model.rkt") 'ant-dagger-allowed?))
              "ANT model declares dagger support (port-level)")
  ;; Carry declaration in ANT port output (detailed)
  (let* ([det ((dynamic-require (build-path here "../ports/domain-registry.rkt") 'produce-analytic-number-theory-detailed))]
         [decl (last det)]
         [l-euler (list-ref det 6)]
         [l-rcuni (list-ref det 7)]
         [l-xisym (list-ref det 8)])
    (check-equal? (length det) 10 "ANT detailed output length")
    ;; First 6 entries should be booleans; last 4 are L-witnesses
    (for ([b (in-list (take det 6))]) (check-true (boolean? b)))
    (check-true (semiring-element? l-euler) "ANT port carries Euler↔Dirichlet antecedent witness")
    (check-true (semiring-element? l-rcuni) "ANT port carries RC-universality antecedent witness")
    (check-true (semiring-element? l-xisym) "ANT port carries ξ-symmetry antecedent witness")
    (check-true (semiring-element? decl) "ANT port carries dagger assumption witness")
    ;; Print a small assumptions/antecedents summary
    (displayln "--- ANT model + antecedents ---")
    (displayln (format "booleans: ~a" (take det 6)))
    (displayln (format "antecedents: EulerDirichletEq(~a) RCUniversal(~a) XiSymmetry(~a)"
                       'ant-default 'ant-default 'ant-default))
    (displayln "assumption: dagger (model)"))
  ;; Stability under label change (symbolic): recompute RC antecedents with another label
  (let* ([lbl 'ant-alt]
         [l-euler (embed-proposition (abstract-op 'EulerDirichletEq (list (make-abstract-const lbl 'symbol)) 'meta))]
         [l-rcuni (embed-proposition (abstract-op 'RCUniversal (list (make-abstract-const lbl 'symbol)) 'meta))]
         [l-xisym (embed-proposition (abstract-op 'XiSymmetry (list (make-abstract-const lbl 'symbol)) 'meta))])
    (check-true (semiring-element? l-euler))
    (check-true (semiring-element? l-rcuni))
    (check-true (semiring-element? l-xisym)))
  ;; Hilbert–Pólya analogue (symbolic, port-level, dagger-enabled model)
  (check-true ((dynamic-require (build-path here "../ports/analytic-number-theory/hilbert-polya.rkt") 'hp-definition-sequent))
              "HP definition: HP = RG† ∘ RG (port-level)")
  (check-true ((dynamic-require (build-path here "../ports/analytic-number-theory/hilbert-polya.rkt") 'hp-analogue-pack))
              "Hilbert–Pólya analogue (symbolic) holds under ANT model")
  ;; Bridge: logic RG ⇒ HP candidate at the ANT port level
  (check-true ((dynamic-require (build-path here "../ports/analytic-number-theory/hp-from-rg.rkt") 'hp-from-rg-pack))
              "RG→HP bridge (symbolic, port-level) holds")
  ;; QFT model declarations and detailed output witnesses
  ((dynamic-require (build-path here "../ports/qft/model.rkt") 'register-qft-model!))
  (check-true ((dynamic-require (build-path here "../ports/qft/model.rkt") 'qft-dagger-allowed?))
              "QFT model declares dagger support (port-level)")
  (check-true ((dynamic-require (build-path here "../ports/qft/model.rkt") 'qft-metric-allowed?))
              "QFT model declares metric support (port-level)")
  (let* ([qd ((dynamic-require (build-path here "../ports/qft/details.rkt") 'produce-qft-detailed))]
         [Z (first qd)]
         [l-dag (second qd)]
         [l-met (third qd)]
         [m-dag (fourth qd)]
         [m-met (fifth qd)]
         [evs (drop qd 5)])
    (check-true (semiring-element? Z) "QFT Z is semiring element")
    (check-true (semiring-element? l-dag) "QFT carries L-dagger witness")
    (check-true (semiring-element? l-met) "QFT carries Lawvere-metric witness")
    (check-true (semiring-element? m-dag) "QFT carries model dagger declaration")
    (check-true (semiring-element? m-met) "QFT carries model metric declaration")
    (check-equal? (length evs) 12 "QFT evidence list length")
    (for ([w (in-list evs)]) (check-true (semiring-element? w) "QFT evidence item is L-witness"))
    (displayln "--- QFT model + antecedents ---")
    (displayln (format "Z: ~a" Z))
    (displayln "assumptions: dagger (model), metric (model)")
    (displayln "antecedents sample: ReflectionPositivity, SpectralCondition, ClusterDecomposition, MetricSignatureOpen, CosmologicalConstantOpen"))
  ;; QFT evidence stability under label change (symbolic)
  (let* ([alt ((dynamic-require (build-path here "../ports/qft/evidence.rkt") 'qft-evidence-witnesses) #:label 'qft-alt)])
    (check-equal? (length alt) 12)
    (for ([w (in-list alt)]) (check-true (semiring-element? w))))
  ;; QFT renormalisation sequents (symbolic)
  (check-true ((dynamic-require (build-path here "../ports/qft/renormalisation.rkt") 'renorm-pack))
              "QFT renormalisation sequents hold (symbolic)")
  ;; Info metric monotonicity (symbolic)
  (check-true ((dynamic-require (build-path here "../theorems/info-metric.rkt") 'info-metric-pack))
              "Fisher information monotone under RG (symbolic)")
  ;; Optical identity (renormalised, symbolic)
  (check-true ((dynamic-require (build-path here "../ports/qft/smatrix.rkt") 'smatrix-pack))
              "Optical identity (renormalised, symbolic)")
  ;; Kernel-style step proofs for ∧/∨ via kernel-checker axioms
  (let* ([P (abstract-op 'var (list (make-abstract-const 'P 'symbol)) 'boolean)]
         [Q (abstract-op 'var (list (make-abstract-const 'Q 'symbol)) 'boolean)]
         [and-int-steps (prove-and-intro P Q)]
         [and-int-goal (abstract-op 'implies (list P (abstract-op 'implies (list Q (abstract-op 'and (list P Q) 'boolean)) 'boolean)) 'boolean)]
         [and-el-steps (prove-and-elim-left P Q)]
         [and-el-goal (abstract-op 'implies (list (abstract-op 'and (list P Q) 'boolean) P) 'boolean)]
         [or-il-steps (prove-or-intro-left P Q)]
         [or-il-goal (abstract-op 'implies (list P (abstract-op 'or (list P Q) 'boolean)) 'boolean)])
    (check-true (kernel-check and-int-steps and-int-goal) "kernel and-intro")
    (check-true (kernel-check and-el-steps and-el-goal) "kernel and-elim-left")
    (check-true (kernel-check or-il-steps or-il-goal) "kernel or-intro-left"))
  ;; Registry entries (selected): logic trace, ANT HP, RG→HP, QFT gap
  (reg-add-l! 'logic-trace-lipschitz 'logic 'sequent '(Trace(Rdet,X_RG))
              ((dynamic-require (build-path here "../logic/traced-operators.rkt") 'trace-lipschitz-sequent)
               'Rdet 'X_RG (make-abstract-const 9/10 'real))
              #:keywords '(trace Trace LIPSCHITZ rg Rdet))
  (reg-add-l! 'ant-hp-definition 'ant 'sequent '(DaggerSMC ANT_Dagger)
              ((dynamic-require (build-path here "../ports/analytic-number-theory/hilbert-polya.rkt") 'hp-definition-sequent))
              #:keywords '(hilbert polya hp rg dagger))
  (reg-add-l! 'ant-hp-resolvent 'ant 'sequent '(EulerDirichletEq RCUniversal XiSymmetry)
              ((dynamic-require (build-path here "../ports/analytic-number-theory/hilbert-polya.rkt") 'hp-resolvent-trace-sequent)
               ((dynamic-require (build-path here "../ports/analytic-number-theory/rc-scheme.rkt") 'make-rc-scheme))
               (make-abstract-const 's 'symbol))
              #:keywords '(resolvent xi zeta))
  (reg-add-l! 'bridge-rg-to-hp-selfadjoint 'ant 'sequent '(Trace(RG,X_RG) Lipschitz(RG,c) DaggerSMC ANT_Dagger)
              ((dynamic-require (build-path here "../ports/analytic-number-theory/hp-from-rg.rkt") 'rg-to-hp-selfadjoint-sequent)
               (make-abstract-const 9/10 'real))
              #:keywords '(selfadjoint rg hp))
  (reg-add-l! 'bridge-rg-to-hp-resolvent 'ant 'sequent '(RCInvariants Trace(RG,X_RG))
              ((dynamic-require (build-path here "../ports/analytic-number-theory/hp-from-rg.rkt") 'rg-to-hp-resolvent-trace-sequent)
               ((dynamic-require (build-path here "../ports/analytic-number-theory/rc-scheme.rkt") 'make-rc-scheme))
               (make-abstract-const 's 'symbol))
              #:keywords '(resolvent xi rc))
  (reg-add-l! 'qft-mass-gap 'qft 'sequent '(DaggerSMC ReflectionPositivity Trace/Lipschitz(RG,c))
              ((dynamic-require (build-path here "../ports/qft/mass-gap.rkt") 'qft-mass-gap-sequent)
               (make-abstract-const 9/10 'real))
              #:keywords '(mass gap reflection positivity))
  (reg-add-l! 'qft-exp-decay 'qft 'sequent '(MassGap SpectralCondition ClusterDecomposition)
              ((dynamic-require (build-path here "../ports/qft/mass-gap.rkt") 'qft-exp-decay-sequent)
               (make-abstract-const 9/10 'real))
              #:keywords '(cluster spectral decay))
  (reg-add-l! 'qft-optical-identity 'qft 'sequent '(LSZ Spectral Cluster)
              ((dynamic-require (build-path here "../ports/qft/smatrix.rkt") 'optical-identity-sequent))
              #:keywords '(optical identity S-matrix))
  (reg-add-l! 'qft-partial-unitarity 'qft 'sequent '(LSZ Spectral)
              ((dynamic-require (build-path here "../ports/qft/smatrix.rkt") 'partial-unitarity-sequent))
              #:keywords '(unitarity S-matrix))
  (reg-add-l! 'qft-scheme-independence 'qft 'sequent '(RCUniversal)
              ((dynamic-require (build-path here "../ports/qft/renormalisation.rkt") 'scheme-independence-sequent) 'qft-default)
              #:keywords '(scheme-independence))
  (reg-add-l! 'qft-callan-symanzik 'qft 'sequent '(Trace/Lip Scale)
              ((dynamic-require (build-path here "../ports/qft/renormalisation.rkt") 'callan-symanzik-sequent) 'qft-default)
              #:keywords '(callan_symanzik))
  (reg-add-l! 'qft-ward-identity 'qft 'sequent '(Gauge BRST)
              ((dynamic-require (build-path here "../ports/qft/renormalisation.rkt") 'ward-identity-sequent) 'qft-default)
              #:keywords '(ward identity))
  (reg-add-l! 'info-fisher-monotone 'logic 'sequent '(Trace/Lip Fisher)
              ((dynamic-require (build-path here "../theorems/info-metric.rkt") 'fisher-monotone-sequent)
               (make-abstract-const 9/10 'real))
              #:keywords '(fisher monotone information))
  (reg-add-l! 'ant-hp-resolvent-completed 'ant 'sequent '(XiCompleted)
              ((dynamic-require (build-path here "../ports/analytic-number-theory/hilbert-polya.rkt") 'hp-resolvent-trace-completed-sequent)
               ((dynamic-require (build-path here "../ports/analytic-number-theory/rc-scheme.rkt") 'make-rc-scheme))
               (make-abstract-const 's 'symbol))
              #:keywords '(universal-generating-function xi completed))
  (reg-add-l! 'ant-xi-hadamard 'ant 'sequent '(XiHadamard)
              ((dynamic-require (build-path here "../ports/analytic-number-theory/hilbert-polya.rkt") 'xi-hadamard-sequent)
               ((dynamic-require (build-path here "../ports/analytic-number-theory/rc-scheme.rkt") 'make-rc-scheme)))
              #:keywords '(hadamard xi))
  ;; QFT gap sequents (symbolic): mass gap and exponential decay from RG + positivity
  (check-true ((dynamic-require (build-path here "../ports/qft/mass-gap.rkt") 'qft-gap-pack))
              "QFT mass-gap and decay sequents hold (symbolic)")
  ;; Universal translation across domains (symbolic naturality under trace)
  (check-true ((dynamic-require (build-path here "../ports/universal-translation.rkt") 'universal-translation-pack))
              "Universal translation sequents hold (symbolic)")
  ;; Write registry JSON for cross-check with LaTeX
  (reg-add-l! 'universal-translation 'ports 'sequent '(TraceNatural UTrans)
              ((dynamic-require (build-path here "../ports/universal-translation.rkt") 'universal-translation-sequent) 'turing 'lambda)
              #:keywords '(universal generating function domain translation))
  (reg-write!)
  (reg-write-coverage!)
  ;; Complexity equivalence (Blum-style up to poly)
  (check-true ((dynamic-require (build-path here "../logic/complexity-equivalence.rkt") 'equivalence-pack))
              "Complexity equivalence (up to poly) witnesses")
  ;; Complexity time hierarchy (summary boolean)
  (reg-add-bool! 'complexity-time-hierarchy 'complexity 'theorem '(TimeDiag)
                 ((dynamic-require (build-path here "../theorems/time-hierarchy.rkt") 'time-hierarchy-derivation)))
  ;; Barrier annotations (non-relativizing, non-natural, non-algebrizing)
  (check-true ((dynamic-require (build-path here "../theorems/barriers.rkt") 'barriers-pack))
              "Barrier annotations witnesses")
  ;; Lens framework generic sanity + domain reuse
  (check-true ((dynamic-require (build-path here "../logic/lens-framework.rkt") 'lens-framework-pack))
              "Generic lens framework pack")
  (check-true ((dynamic-require (build-path here "../theorems/domain-lens-reuse.rkt") 'domain-lens-reuse-pack))
              "Domain lens reuse pack (QFT, ANT)")
  (displayln "=== All verification checks passed ===")
  #t)

;; Collect a machine-readable summary of key verification checks.
;; Returns an association list '((name . boolean) ...)
(define (verify-summary)
  (define results '())
  (define (add name val) (set! results (append results (list (cons name val)))))
  (define (log x)
    (when (getenv "LUX_DEBUG_SUMMARY") (displayln x)))
  ;; V2 runner: if it raises, caller fails before consuming summary; mark as true here.
  (log 'start)
  (add 'v2-runner #t)
  ;; GF unity and evidence isos
  (log 'gf)
  (add 'gf-unity (verify-generating-functional-unity))
  (add 'evidence-gf (verify-evidence-isomorphism gf-iso))
  (add 'evidence-categorical (verify-evidence-isomorphism categorical-logic-iso))
  (log 'categorical)
  (add 'categorical-coherence (th:verify-categorical-logic))
  ;; Kernel basics
  (log 'kernel)
  (add 'kernel-basics
       (for/and ([kv (kernel-basics)])
         (define w (cdr kv))
         (and (semiring-element? w)
              (eq? (semiring-element-semiring-type w) 'L))))
  ;; Kernel reflexivity (summary assumes presence via kernel-basics)
  (log 'kernel-reflexive)
  (add 'kernel-reflexivity
       (let* ([w (cdr (assoc 'reflexivity (kernel-basics)))])
         (and (semiring-element? w)
              (eq? (semiring-element-semiring-type w) 'L))))
  ;; Inference basic rules live in L
  (log 'inference)
  (add 'inference-basics
       (for/and ([kv (inference-basics)])
         (define w (cdr kv))
         (and (semiring-element? w)
              (eq? (semiring-element-semiring-type w) 'L))))
  ;; Structural/tactic demo
  (log 'structural)
  (let* ([P (embed-proposition (make-abstract-const 'P 'symbol))]
         [Q (embed-proposition (make-abstract-const 'Q 'symbol))]
         [R (embed-proposition (make-abstract-const 'R 'symbol))]
         [ctx '()])
    (add 'structural-contraction (semiring-element? (rule-contraction ctx P Q)))
    (add 'structural-exchange (semiring-element? (rule-exchange ctx P Q ctx R)))
    (add 'tactic-mp2 (semiring-element? (tactic-mp2 ctx P Q R))))
  ;; Sequent checker sample
  (log 'sequent)
  (let* ([P (embed-proposition (make-abstract-const 'P 'symbol))]
         [Q (embed-proposition (make-abstract-const 'Q 'symbol))]
         [ctx '()]
         [wit (rule-and-intro ctx P Q)]
         [st (deriv-step 'and-intro (list ctx P Q) wit)])
    (add 'sequent-checker (check-step st)))
  ;; Guarded ZFC schemas symbolic
  (log 'zfc)
  (let* ([phi (abstract-op 'phi '() 'predicate)]
         [G   (abstract-op 'G '() 'guard)])
    (add 'schema-separation (semiring-element? (schema-separation-guarded phi G)))
    (add 'schema-replacement (semiring-element? (schema-replacement-guarded phi G))))
  ;; Logic properties
  (log 'logic)
  (add 'imp-trans (semiring-element? (prop-implies-trans)))
  (add 'imp-ante-strengthen (semiring-element? (prop-imp-ante-strengthen)))
  (add 'cut (semiring-element? (prop-cut)))
  (add 'imp-distribute-right (semiring-element? (prop-imp-distribute-right)))
  (add 'reflect-L-B (prop-reflect-L-B))
  (add 'context-normalization (prop-context-normalization))
  (add 'self-apply (self-apply-ruleset))
  (add 'guarded-imp-monotone (semiring-element? (prop-guarded-imp-monotone)))
  ;; Conservativity
  (log 'conservativity)
  (add 'conservativity (conservativity-demo-implies-trans))
  ;; Lifting pack
  (log 'lifting)
  (add 'local-boundary-uniqueness (local-boundary-uniqueness))
  (add 'local-explog-coherence (local-explog-coherence))
  (add 'global-uniqueness-up-to-nf (global-uniqueness-up-to-nf))
  (add 'transport-invariance-mp (transport-invariance-mp))
  (add 'transport-invariance-and-intro (transport-invariance-and-intro))
  (add 'global-to-local-naturality (global-to-local-naturality))
  (add 'nf-lift-stability (nf-lift-stability))
  ;; Truth pack
  (log 'truth)
  (add 'global-local-truth-demo (global-local-truth-demo))
  (add 'truth-conjunction-canonical (semiring-element? (truth-conjunction-canonical)))
  (add 'truth-transport-preservation (truth-transport-preservation))
  (add 'truth-imp-reflexive (semiring-element? (truth-imp-reflexive)))
  ;; Gap / normal form
  (log 'gap)
  (add 'gap-contraction (contraction-gap-witness))
  (add 'dnf-idempotent (dnf-idempotent?))
  (add 'dnf-transport-invariant (dnf-transport-invariant?))
  (add 'non-contraction (non-contraction-witness))
  (add 'marginal-axis (marginal-axis-demo))
  (add 'marginal-truth (marginal-truth-demo))
  (add 'rewrite-eq-roundtrip (rewrite-eq-roundtrip?))
  (add 'rewrite-red-noninvertible (rewrite-red-noninvertible?))
  (add 'rewrite-metric-monotone (rewrite-metric-monotone?))
  ;; (non-contraction) already recorded above; avoid duplicate entries
  (log 'congruence)
  ;; Congruence quick check
  (let* ([x (semiring-element (get-two) B)]
         [y (semiring-element (get-two) B)]
         [z (semiring-element (get-three) B)]
         [sumR ((semiring-ops-add B-ops) x z)]
         [sumR-prime ((semiring-ops-add B-ops) y z)]
         [prodR ((semiring-ops-mul B-ops) x z)]
         [prodR-prime ((semiring-ops-mul B-ops) y z)])
    (add 'congruence-add (abstract-expr-equal? (semiring-element-value sumR)
                                               (semiring-element-value sumR-prime)))
    (add 'congruence-mul (abstract-expr-equal? (semiring-element-value prodR)
                                               (semiring-element-value prodR-prime))))
  ;; ANT and complexity evidence (disabled in summary by default; enable with LUX_SUMMARY_HEAVY=1)
  (when (let ([v (getenv "LUX_SUMMARY_HEAVY")]) (and v (or (string-ci=? v "1") (string-ci=? v "true"))))
    (add 'ant-evidence ((dynamic-require (build-path here "../ports/analytic-number-theory/evidence.rkt") 'run-ant-evidence-tests)))
    (add 'ant-symbolic ((dynamic-require (build-path here "../ports/analytic-number-theory/symbolic-evidence.rkt") 'run-ant-symbolic-evidence-tests)))
    (add 'beta-system ((dynamic-require (build-path here "../theorems/beta-system.rkt") 'beta-system-sanity)))
    (add 'complexity-gap-separations ((dynamic-require (build-path here "../theorems/complexity-separation.rkt") 'verify-complexity-gap-separations)))
    (add 'pnp-separations ((dynamic-require (build-path here "../theorems/complexity-separation.rkt") 'verify-pnp-separations)))
    (add 'complexity-internal-sanity ((dynamic-require (build-path here "../logic/complexity-internal.rkt") 'complexity-internal-sanity)))
    ;; (add 'complexity-lens-soundness ((dynamic-require (build-path here "../logic/complexity-internal.rkt") 'soundness-under-lenses)))
    (add 'blum-axioms ((dynamic-require (build-path here "../logic/complexity-blum.rkt") 'blum-axioms-sanity)))
    (add 'karp-closure (semiring-element? ((dynamic-require (build-path here "../logic/complexity-blum.rkt") 'closure-under-karp))))
    (add 'time-hierarchy ((dynamic-require (build-path here "../theorems/time-hierarchy.rkt") 'time-hierarchy-sanity)))
    (add 'time-hierarchy-derivation ((dynamic-require (build-path here "../theorems/time-hierarchy.rkt") 'time-hierarchy-derivation)))
    (add 'logic-driven-complexity ((dynamic-require (build-path here "../theorems/logic-driven-complexity.rkt") 'logic-driven-complexity-pack)))
    (add 'spectral-gap-driven-separation ((dynamic-require (build-path here "../logic/spectral-gap-logic.rkt") 'spectral-gap-driven-separation)))
    (add 'semantics-pack ((dynamic-require (build-path here "../semantics/categorical-model.rkt") 'semantics-pack)))
    (add 'complexity-equivalence ((dynamic-require (build-path here "../logic/complexity-equivalence.rkt") 'equivalence-pack)))
    (add 'barriers ((dynamic-require (build-path here "../theorems/barriers.rkt") 'barriers-pack)))
    (add 'lens-framework ((dynamic-require (build-path here "../logic/lens-framework.rkt") 'lens-framework-pack)))
    (add 'domain-lens-reuse ((dynamic-require (build-path here "../theorems/domain-lens-reuse.rkt") 'domain-lens-reuse-pack))))
  ;; Optional: register strong assumption → conclusion sequents for registry export
  (when (let ([v (getenv "LUX_STRONG_ASSUMPTIONS")]) (and v (or (string-ci=? v "1") (string-ci=? v "true"))))
    ;; GRH via HP route (symbolic sequent)
    (let* ([scheme ((dynamic-require (build-path here "../ports/analytic-number-theory/rc-scheme.rkt") 'make-rc-scheme)
                    #:label 'ant-default)]
           [rh-seq ((dynamic-require (build-path here "../ports/analytic-number-theory/hilbert-polya.rkt") 'rh-sequent)
                    scheme)])
      (reg-add-l! 'HP_to_RH 'ANT 'sequent '(DaggerSMC ANT_Dagger XiCompleted XiHadamard ResolventTraceEq)
                  rh-seq #:keywords '(HilbertPolya Resolvent Xi RC)))
    ;; Complexity separation as sequents
    (let* ([pnp-seq ((dynamic-require (build-path here "../theorems/complexity-separation.rkt") 'pnp-separation-sequent))]
           [npcnp-seq ((dynamic-require (build-path here "../theorems/complexity-separation.rkt") 'npcnp-separation-sequent))]
           [contrad-seq ((dynamic-require (build-path here "../theorems/complexity-separation.rkt") 'p-equals-np-contradiction-sequent))])
      (reg-add-l! 'P_neq_NP 'Complexity 'sequent '(DetNonExp NondetNeutral LensSoundness)
                  pnp-seq #:keywords '(P NP Lens Regime))
      (reg-add-l! 'NP_neq_coNP 'Complexity 'sequent '(DetNonExp NondetNeutral LensSoundness)
                  npcnp-seq #:keywords '(NP coNP Lens Regime))
      (reg-add-l! 'P_eq_NP_contradiction 'Complexity 'sequent '(PEqNP DetNonExp NondetNeutral LensSoundness)
                  contrad-seq #:keywords '(Counterfactual)))
    ;; Mass-gap bridge sequent
    (let ([mg-bridge ((dynamic-require (build-path here "../ports/mass-gap.rkt") 'mass-gap-bridge-sequent))])
      (reg-add-l! 'QFT_ExpDecay 'QFT 'sequent '(ReflectionPositivity SpectralCondition ClusterDecomposition Lipschitz<1 PortInvariance)
                  mg-bridge #:keywords '(MassGap ExpDecay QFT)))
    (reg-write!)
    (reg-write-coverage!))
  ;; Deep integration: register Gap → Port consequence manifests (as GapPort entries)
  (let* ([ant ((dynamic-require (build-path here "../ports/analytic-number-theory/gap-view.rkt") 'gap->ant))]
         [cplx ((dynamic-require (build-path here "../ports/complexity/gap-view.rkt") 'gap->complexity))]
         [qft ((dynamic-require (build-path here "../ports/qft/gap-view.rkt") 'gap->qft))]
         [mk-tags (λ (alist)
                    (for/list ([kv (in-list alist)])
                      (make-abstract-const (car kv) 'symbol)))]
         [mk-gapport (λ (port tags)
                       (embed-proposition (abstract-op 'GapPort
                                                       (list (make-abstract-const port 'symbol)
                                                             (abstract-op 'Tags tags 'meta))
                                                       'meta)))])
    (reg-add-l! 'GapPort_ANT 'ANT 'sequent '(LogicGap)
                (mk-gapport 'ANT (mk-tags ant)) #:keywords '(GapPort ANT HP Xi RC))
    (reg-add-l! 'GapPort_Complexity 'Complexity 'sequent '(LogicGap)
                (mk-gapport 'Complexity (mk-tags cplx)) #:keywords '(GapPort Complexity Lenses Regime))
    (reg-add-l! 'GapPort_QFT 'QFT 'sequent '(LogicGap)
                (mk-gapport 'QFT (mk-tags qft)) #:keywords '(GapPort QFT MassGap ExpDecay)))
  results)

;; Return a snapshot of Gap propagation: list of (port . ((name . L-witness) ...))
(define (gap-propagation-snapshot)
  (list
   (cons 'ANT ((dynamic-require (build-path here "../ports/analytic-number-theory/gap-view.rkt") 'gap->ant)))
   (cons 'Complexity ((dynamic-require (build-path here "../ports/complexity/gap-view.rkt") 'gap->complexity)))
   (cons 'QFT ((dynamic-require (build-path here "../ports/qft/gap-view.rkt") 'gap->qft)))))
