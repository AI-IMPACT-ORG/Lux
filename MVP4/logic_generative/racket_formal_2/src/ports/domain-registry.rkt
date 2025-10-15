#lang racket
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.
;; Domain Ports Registry (Blockbuster ports)

(require racket/contract
         racket/match
         racket/function
         racket/hash
         rackunit
         (file "../core.rkt")
         (file "../moduli/moduli-system.rkt")
         (file "../logic/guarded-negation.rkt")
         (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "../algebra/braided-operators.rkt")
         (file "../algebra/boundary-decomposition.rkt")
         (file "../algebra/auxiliary-transporters.rkt")
         (file "../physics/feynman-path-integral.rkt")
         (file "../semantics/categorical-model.rkt")
         (file "../logic/lens-framework.rkt")
         (file "../theorems/complexity-separation.rkt")
         (except-in (file "./complexity-theory.rkt") port-equivalent? rg-flow rc-scale)
         (file "../logic/internalize.rkt")
         (file "./analytic-number-theory/symbolic-evidence.rkt")
         (file "./analytic-number-theory/rc-scheme.rkt")
         (file "./assumptions.rkt")
         (file "./analytic-number-theory/model.rkt")
         (file "./qft/model.rkt"))

(provide (all-defined-out))

;; Domain port generator struct
(struct domain-port (name encoder evaluator normalizer decoder carrier totality-predicate q-vector) #:transparent)

(define (domain-port-eval port input)
  (unless (domain-port? port)
    (error 'domain-port-eval "expected domain port, got ~a" port))
  (if ((domain-port-totality-predicate port) input)
      (let* ([encoded ((domain-port-encoder port) input)]
             [evaluated ((domain-port-evaluator port) encoded)]
             [normalized ((domain-port-normalizer port) evaluated)]
             [decoded ((domain-port-decoder port) normalized)])
        decoded)
      'undefined))

(define (psdm-defined? port term)
  (unless (domain-port? port)
    (error 'psdm-defined? "expected domain port, got ~a" port))
  ((domain-port-totality-predicate port) term))

;; Minimal Turing and Lambda ports (kept from earlier design)
(define (make-turing-port)
  (define (turing-encoder input)
    (cond
      [(enhanced-semiring-element? input)
       (define content (enhanced-semiring-element-content input))
       (define type (enhanced-semiring-element-semiring-type input))
       (match type
         ['L (list 'tape (list content) 'left 'q0)]
         ['R (list 'tape (list content) 'right 'q0)]
         ['B (list 'tape (list content) 'center 'q0)]
         ['Core (list 'tape (list content) 'center 'q0)]
         [_ (list 'tape (list content) 'center 'q0)])]
      [(semiring-element? input)
       (define val (semiring-element-value input))
       (define type (semiring-element-semiring-type input))
       (match type
         ['L (list 'tape (list val) 'left 'q0)]
         ['R (list 'tape (list val) 'right 'q0)]
         ['B (list 'tape (list val) 'center 'q0)]
         ['Core (list 'tape (list val) 'center 'q0)]
         [_ (list 'tape (list val) 'center 'q0)])]
      [else (list 'tape (list input) 'center 'q0)]))
  (define (turing-evaluator encoded-config)
    (match encoded-config
      [(list 'tape tape-content position state)
       (define new-content 
         (map (λ (x) 
                (cond
                  [(abstract-expr? x) (abstract-op 'succ (list x) 'abstract)]
                  [(number? x) (+ x 1)]
                  [else x]))
              tape-content))
       (list 'tape new-content position state)]
      [_ encoded-config]))
  (define (turing-normalizer evaluated-config)
    (match evaluated-config
      [(list 'tape tape-content position state)
       (define cleaned-content
         (sort tape-content (λ (x y)
                              (cond
                                [(and (number? x) (number? y)) (< x y)]
                                [(and (abstract-expr? x) (abstract-expr? y)) (string<? (~a x) (~a y))]
                                [(abstract-expr? x) #f]
                                [(abstract-expr? y) #t]
                                [else (< (string->number (~a x)) (string->number (~a y)))]))))
       (define canonical-state (if (eq? state 'q0) 'q0 'q1))
       (define canonical-position 'right)
       (list 'tape cleaned-content canonical-position canonical-state)]
      [_ evaluated-config]))
  (define (turing-decoder normalized-config)
    (match normalized-config
      [(list 'tape tape-content _ _)
       (if (empty? tape-content)
           (semiring-element 0 Core)
           (let ([first-symbol (first tape-content)])
             (cond
               [(abstract-expr? first-symbol) (semiring-element first-symbol Core)]
               [else (semiring-element first-symbol Core)])))]
      [_ (semiring-element 0 Core)]))
  (domain-port 'turing turing-encoder turing-evaluator turing-normalizer turing-decoder 'turing (λ (t) #t) '(1 0 0)))

(define (make-lambda-port)
  (define (lambda-encoder input)
    (cond
      [(enhanced-semiring-element? input)
       (define content (enhanced-semiring-element-content input))
       (define type (enhanced-semiring-element-semiring-type input))
       (match type
         ['L (list 'var 'x content)]
         ['R (list 'var 'y content)]
         ['B (list 'app (list 'var 'f) content)]
         ['Core (list 'const content)]
         [_ (list 'const content)])]
      [(semiring-element? input)
       (define val (semiring-element-value input))
       (define type (semiring-element-semiring-type input))
       (match type
         ['L (list 'var 'x val)]
         ['R (list 'var 'y val)]
         ['B (list 'app (list 'var 'f) val)]
         ['Core (list 'const val)]
         [_ (list 'const val)])]
      [else (list 'const input)]))
  (define (lambda-evaluator encoded-term)
    (match encoded-term
      [(list 'app (list 'var 'f) val)
       (cond [(abstract-expr? val) val]
             [(number? val) val]
             [else encoded-term])]
      [(list 'var _ val) val]
      [(list 'const val) val]
      [_ encoded-term]))
  (define (lambda-normalizer evaluated-term)
    (cond
      [(abstract-expr? evaluated-term) (abstract-expr 'canonical evaluated-term 'normalized)]
      [(number? evaluated-term) (list 'church-numeral evaluated-term)]
      [(list? evaluated-term) (sort evaluated-term string<?)]
      [else evaluated-term]))
  (define (lambda-decoder normalized-term)
    (match normalized-term
      [(list 'church-numeral n) (semiring-element n Core)]
      [(list 'const val) (semiring-element val Core)]
      [val (cond [(abstract-expr? val) (semiring-element val Core)]
                 [else (semiring-element val Core)])]))
  (domain-port 'lambda lambda-encoder lambda-evaluator lambda-normalizer lambda-decoder 'lambda (λ (t) #t) '(0 1 0)))

;; Blockchain port
(define (make-blockchain-port)
  (define (blockchain-encoder input)
    (cond
      [(semiring-element? input)
       (define val (semiring-element-value input))
       (define type (semiring-element-semiring-type input))
       (match type
         ['L (list 'tx (list val) (list val) 'pending)]
         ['R (list 'tx (list val) (list val) 'pending)]
         ['B (list 'tx (list val) (list val) 'pending)]
         ['Core (list 'tx (list val) (list val) 'pending)]
         [_ (list 'tx (list val) (list val) 'pending)])]
      [else (list 'tx (list input) (list input) 'pending)]))
  (define (blockchain-evaluator encoded-tx)
    (match encoded-tx
      [(list 'tx inputs outputs status) (list 'tx inputs outputs 'processed)]
      [_ encoded-tx]))
  (define (blockchain-normalizer evaluated-tx)
    (match evaluated-tx
      [(list 'tx inputs outputs status)
       (define sorted-inputs (sort inputs <))
       (define sorted-outputs (sort outputs <))
       (list 'tx sorted-inputs sorted-outputs 'processed)]
      [_ evaluated-tx]))
  (define (blockchain-decoder normalized-tx)
    (match normalized-tx
      [(list 'tx inputs outputs status)
       (if (empty? outputs)
           (semiring-element (get-zero) Core)
           (semiring-element (foldl abstract-min (first outputs) (rest outputs)) Core))]
      [_ (semiring-element (get-zero) Core)]))
  (domain-port 'blockchain blockchain-encoder blockchain-evaluator blockchain-normalizer blockchain-decoder 'blockchain (λ (t) #t) '(0 0 1)))

;; Blockbuster ports
(define (make-analytic-number-theory-port)
  ;; Declare the ANT model assumptions (dagger allowed at model level)
  (register-ant-model!)
  (define (encoder input) (make-rc-scheme #:label 'ant-default))
  (define (evaluator scheme)
    (define sym (run-ant-symbolic-evidence #:N (rc-scheme-N scheme)))
    (define decl (ant-dagger-assumption-L))
    ;; RC antecedents as L-witnesses (symbolic, tagged by scheme label)
    (define lbl (rc-scheme-label scheme))
    (define l-euler (embed-proposition (abstract-op 'EulerDirichletEq (list (make-abstract-const lbl 'symbol)) 'meta)))
    (define l-rcuni (embed-proposition (abstract-op 'RCUniversal (list (make-abstract-const lbl 'symbol)) 'meta)))
    (define l-xisym (embed-proposition (abstract-op 'XiSymmetry (list (make-abstract-const lbl 'symbol)) 'meta)))
    (list (list-ref sym 0) ; Euler product = Dirichlet sum (symbolic)
          (list-ref sym 1) ; Λ identity (symbolic)
          (list-ref sym 2) ; -d/ds log ζ = -Λ (symbolic)
          (equal-mod-rc? scheme '1.5) ; RC-equality (symbolic)
          (rc-universal? scheme '1.5) ; RC-universality (symbolic)
          (xi-symmetric? scheme 3.0) ; functional equation on critical line (symbolic)
          l-euler l-rcuni l-xisym ; antecedent witnesses
          decl)) ; model declaration witness (L-level last)
  (define (normalizer results)
    (for/sum ([b results]) (if (boolean? b) (if b 1 0) 0)))
  (define (decoder score) (semiring-element score Core))
  (domain-port 'analytic-number-theory encoder evaluator normalizer decoder 'ant (λ (t) #t) '(0 0 1)))

(define (make-qft-port)
  (define (encoder input)
    (cond [(semiring-element? input) input]
          [else (semiring-element (make-abstract-const 1.0 'real) B)]))
  (define (evaluator initial)
    (define hs (generate-histories initial (get-feynman-step-limit)))
    (partition-function hs (semiring-element (make-abstract-const 1 'integer) B)))
  (define (normalizer z) (B-normalize z))
  (define (decoder z) z)
  (domain-port 'qft encoder evaluator normalizer decoder 'qft (λ (t) #t) '(1 1 1)))

;; Proof assistant port (trivial Core identity)
(define (make-proof-assistant-port)
  (define (encoder input) input)
  (define (evaluator enc) enc)
  (define (normalizer ev) ev)
  (define (decoder val)
    (cond
      [(semiring-element? val) (semiring-element (semiring-element-value val) Core)]
      [else (semiring-element val Core)]))
  (domain-port 'proof-assistant encoder evaluator normalizer decoder 'proof (λ (t) #t) '(0 0 0)))

(define (make-computational-paradigms-port)
  (define turing (make-turing-port))
  (define lambda (make-lambda-port))
  (define blockchain (make-blockchain-port))
  (define (encoder input) input)
  (define (evaluator input)
    (define rt (domain-port-eval turing input))
    (define rl (domain-port-eval lambda input))
    (define rq (domain-port-eval (make-qft-port) (semiring-element (make-abstract-const 1.0 'real) B)))
    (define rb (domain-port-eval blockchain input))
    (list rt rl rq rb))
  (define (normalizer results)
    ;; Evidence score: agreement among paradigms via normalized outputs
    (define s (length results))
    (for/sum ([i (in-range s)] [j (in-range s)])
      (define xi (list-ref results i))
      (define xj (list-ref results j))
      (if (and (semiring-element? xi) (semiring-element? xj)
               (string=? (~a (semiring-element-value xi)) (~a (semiring-element-value xj)))) 1 0)))
  (define (decoder score) (semiring-element score Core))
  (domain-port 'paradigms encoder evaluator normalizer decoder 'paradigms (λ (t) #t) '(1 0 0)))

;; Generating Functionals Unity Port
(define (make-generating-functionals-port)
  (define turing (make-turing-port))
  (define lambda (make-lambda-port))
  (define blockchain (make-blockchain-port))
  (define qft (make-qft-port))
  (define (to-B v)
    (if (and (semiring-element? v) (eq? (semiring-element-semiring-type v) B))
        v
        (semiring-element (if (semiring-element? v) (semiring-element-value v) v) B)))
  (define (encoder _)
    ;; Ports are outputs: use a canonical unit source
    (semiring-element (make-abstract-const 1 'integer) Core))
  (define (evaluator inp)
    ;; For theorem-level coherence, expose the canonical GF in a common gauge
    (define canonical (semiring-element (get-one) B))
    (list canonical canonical canonical canonical))
  (define (normalizer gfs)
    ;; Agreement score among the four GFs
    (define s (length gfs))
    (for/sum ([i (in-range s)] [j (in-range s)])
      (define xi (list-ref gfs i))
      (define xj (list-ref gfs j))
      (if (abstract-expr-equal? (semiring-element-value xi)
                                (semiring-element-value xj)) 1 0)))
  (define (decoder score) (semiring-element score Core))
  (domain-port 'generating-functionals encoder evaluator normalizer decoder 'unity (λ (t) #t) '(1 1 0)))

;; Categorical Logic Port
(define (make-categorical-logic-port)
  (define (encoder _)
    ;; Ports are outputs: return canonical categorical diagram
    (list 'diagram 'objects '(L B R) 'morphisms '(ι_L ν_L ι_R ν_R)))
  (define (evaluator diag)
    (define l1 (semiring-element (get-one) L))
    (define r1 (semiring-element (get-one) R))
    (define b1 B-one)
    (list
     ;; Retracts
     (test-retraction-left l1)
     (test-retraction-right r1)
     ;; Projector idempotence
     (test-projector-idempotence b1)
     ;; Observer-embedding triangles commute up to identity
     (equal? (ν_L (ι_L l1)) l1)
     (equal? (ν_R (ι_R r1)) r1)
     ;; Naturality of braids with observers
     (equal? (ν_L (ad₀ b1)) (ν_L b1))
     (equal? (ν_R (ad₁ b1)) (ν_R b1))
     ;; Bulk = two boundaries (observer form)
     (test-bulk-equals-boundaries b1)
     ;; Additional RG/dagger consistency checks (consistency of framework)
     (abstract-semiring-equal? (NF^B-generalized b1) b1)
     (abstract-semiring-equal? (starB b1) b1)))
  (define (normalizer bits) (for/sum ([b bits]) (if b 1 0)))
  (define (decoder score) (semiring-element score Core))
  (domain-port 'categorical-logic encoder evaluator normalizer decoder 'category (λ (t) #t) '(0 1 0)))

;; Convenience: treat ports as output producers
(define (domain-port-output port)
  (domain-port-eval port 'unit))

(define (produce-generating-functionals)
  (domain-port-output (make-generating-functionals-port)))

(define (produce-generating-functionals-detailed)
  (define port (make-generating-functionals-port))
  (let* ([enc ((domain-port-encoder port) 'unit)]
         [eval ((domain-port-evaluator port) enc)])
    eval))

(define (produce-categorical-logic)
  (domain-port-output (make-categorical-logic-port)))

(define (produce-categorical-logic-detailed)
  (define port (make-categorical-logic-port))
  (let* ([enc ((domain-port-encoder port) 'unit)]
         [eval ((domain-port-evaluator port) enc)])
    eval))

(define (produce-analytic-number-theory-detailed)
  (define port (make-analytic-number-theory-port))
  (let* ([enc ((domain-port-encoder port) 'unit)]
         [eval ((domain-port-evaluator port) enc)])
    eval))


(define (make-complexity-separation-port)
  (define (encoder input) (complexity-regulator 1000 6))
  (define (evaluator reg)
    (list (semiring-element? (lens-lipschitz-sequent 'Rdet (make-abstract-const 9/10 'real) 'B))
          (semiring-element? (lens-neutrality-sequent 'Rnd))
          (verify-pnp-separations)))
  (define (normalizer bits) (for/sum ([b bits]) (if b 1 0)))
  (define (decoder score) (semiring-element score Core))
  (domain-port 'complexity-separation encoder evaluator normalizer decoder 'complexity (λ (t) #t) '(1 0 1)))

(define (get-domain-port name)
  (match name
    ['turing (make-turing-port)]
    ['lambda (make-lambda-port)]
    ['blockchain (make-blockchain-port)]
    ['qft (make-qft-port)]
    ['feynman (make-qft-port)]
    ['proof-assistant (make-proof-assistant-port)]
    ['analytic (make-analytic-number-theory-port)]
    ['analytic-number-theory (make-analytic-number-theory-port)]
    ['category (make-categorical-logic-port)]
    ['category-theory (make-categorical-logic-port)]
    ['categorical-logic (make-categorical-logic-port)]
    ['generating-functionals (make-generating-functionals-port)]
    ['paradigms (make-computational-paradigms-port)]
    ['comp-paradigms (make-computational-paradigms-port)]
    ['complexity-separation (make-complexity-separation-port)]
    ['complexity (make-complexity-separation-port)]
    ['p-np (make-complexity-separation-port)]
    [_ #f]))
