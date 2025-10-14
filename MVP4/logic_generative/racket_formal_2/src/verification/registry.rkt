#lang racket
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.

(require racket/list
         json
         (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt"))

(provide start-registry!
         load-latex-labels!
         reg-add-l!
         reg-add-bool!
         reg-write!
         reg-write-coverage!)

(define current-reg '())
(define latex-labels '())

(define (load-latex-labels! [root "../../latex"]) ; relative to this file's dir
  (define labels '())
  (define dirs (list root (build-path root "sections")))
  (for ([d (in-list dirs)])
    (with-handlers ([exn:fail? (λ (_) (void))])
      (for ([e (in-list (directory-list d))])
        (define p (build-path d e))
        (when (and (file-exists? p) (regexp-match? #rx"\\.tex$" (~a p)))
          (with-handlers ([exn:fail? (λ (_) (void))])
            (for ([line (in-lines (open-input-file p))])
              (when (regexp-match? #rx"\\\\label\\{([^}]+)\\}" line)
                (define m (regexp-match #rx"\\\\label\\{([^}]+)\\}" line))
                (set! labels (cons (second m) labels))))))))
  (set! latex-labels labels)
  labels))


(define (start-registry!) (set! current-reg '()))

(define (sexpr-of-witness w)
  (cond
    [(semiring-element? w) (~a (semiring-element-value w))]
    [else (~a w)]))

(define (pretty-of-expr e)
  (cond
    [(abstract-op? e)
     (define op (abstract-op-operator e))
     (define args (abstract-op-operands e))
     (case op
       [(implies) (format "(~a ⇒ ~a)" (pretty-of-expr (first args)) (pretty-of-expr (second args)))]
       [(and) (format "(~a ∧ ~a)" (pretty-of-expr (first args)) (pretty-of-expr (second args)))]
       [(or) (format "(~a ∨ ~a)" (pretty-of-expr (first args)) (pretty-of-expr (second args)))]
       [(Eq) (format "~a = ~a" (pretty-of-expr (first args)) (pretty-of-expr (second args)))]
       [(Trace) (format "Tr(~a;~a)" (pretty-of-expr (first args)) (pretty-of-expr (second args)))]
       [(TraceLipschitz) (format "Lip(~a,~a;~a)"
                                 (pretty-of-expr (first args)) (pretty-of-expr (second args)) (pretty-of-expr (third args)))]
       [(TraceResolvent) (format "Tr((~a − ~a)^{-1})" (pretty-of-expr (first args)) (pretty-of-expr (second args)))]
       [(SelfAdjoint) (format "~a = ~a^†" (pretty-of-expr (first args)) (pretty-of-expr (first args)))]
       [(Compose) (format "(~a ∘ ~a)" (pretty-of-expr (first args)) (pretty-of-expr (second args)))]
       [(DaggerOf) (format "(~a)^†" (pretty-of-expr (first args)))]
       [(prop) (pretty-of-expr (first args))]
       [else (~a e)])]
    [(abstract-const? e) (~a (abstract-const-value e))]
    [else (~a e)]))

(define (pretty-of-witness w)
  (if (semiring-element? w)
      (pretty-of-expr (semiring-element-value w))
      (~a w)))

(define (latex-of-expr e)
  (cond
    [(abstract-op? e)
     (define op (abstract-op-operator e))
     (define args (abstract-op-operands e))
     (case op
       [(implies) (format "(\\,~a \\Rightarrow ~a\\,)" (latex-of-expr (first args)) (latex-of-expr (second args)))]
       [(and) (format "(\\,~a \\land ~a\\,)" (latex-of-expr (first args)) (latex-of-expr (second args)))]
       [(or) (format "(\\,~a \\lor ~a\\,)" (latex-of-expr (first args)) (latex-of-expr (second args)))]
       [(Eq) (format "~a = ~a" (latex-of-expr (first args)) (latex-of-expr (second args)))]
       [(Trace) (format "\\mathrm{Tr}(~a;~a)" (latex-of-expr (first args)) (latex-of-expr (second args)))]
       [(TraceLipschitz) (format "\\mathrm{Lip}(~a,~a;~a)"
                                 (latex-of-expr (first args)) (latex-of-expr (second args)) (latex-of-expr (third args)))]
       [(TraceResolvent) (format "\\mathrm{Tr}((~a-~a)^{-1})" (latex-of-expr (first args)) (latex-of-expr (second args)))]
       [(SelfAdjoint) (format "~a = ~a^{\\dagger}" (latex-of-expr (first args)) (latex-of-expr (first args)))]
       [(Compose) (format "(~a \\circ ~a)" (latex-of-expr (first args)) (latex-of-expr (second args)))]
       [(DaggerOf) (format "(~a)^{\\dagger}" (latex-of-expr (first args)))]
       [(TraceNatural) (format "\\mathrm{NatTr}(~a;~a,~a)"
                               (latex-of-expr (first args)) (latex-of-expr (second args)) (latex-of-expr (third args)))]
       [(UTrans) (format "\\mathcal{U}_{~a\\to~a}" (latex-of-expr (first args)) (latex-of-expr (second args)))]
       [(RCUniversal) (format "\\mathrm{RC}_{\\mathrm{univ}}(~a)" (latex-of-expr (first args)))]
        [(SchemeIndependent) (format "\\mathrm{SchemeIndep}(~a)" (latex-of-expr (first args)))]
        [(CallanSymanzik) (format "\\mathrm{CS}(~a)" (latex-of-expr (first args)))]
        [(WardIdentity) (format "\\mathrm{Ward}(~a)" (latex-of-expr (first args)))]
        [(BRSTNilpotent) (format "\\mathrm{BRST}(~a)" (latex-of-expr (first args)))]
        [(GaugeInvariant) (format "\\mathrm{GaugeInv}(~a)" (latex-of-expr (first args)))]
        [(ReflectionPositivity) (format "\\mathrm{ReflPos}(~a)" (latex-of-expr (first args)))]
        [(SpectralCondition) (format "\\mathrm{Spectral}(~a)" (latex-of-expr (first args)))]
        [(ClusterDecomposition) (format "\\mathrm{Cluster}(~a)" (latex-of-expr (first args)))]
        [(MassGapFromLipschitz) (format "\\mathrm{MassGap}(~a)" (latex-of-expr (first args)))]
        [(ExpDecayConnected) (format "\\mathrm{ExpDecay}(~a)" (latex-of-expr (second args)))]
        [(XiCompleted) (format "\\Xi_{\\mathrm{comp}}(~a)" (latex-of-expr (first args)))]
        [(NegDLogXi) (format "-\\frac{d}{ds}\\log\\,\\Xi(~a)" (latex-of-expr (first args)))]
        [(prop) (latex-of-expr (first args))]
        [else (~a e)])]
    [(abstract-const? e) (~a (abstract-const-value e))]
    [else (~a e)]))

(define (latex-of-witness w)
  (if (semiring-element? w)
      (latex-of-expr (semiring-element-value w))
      (~a w)))

(define (find-labels keywords)
  (define out '())
  (for ([lab (in-list latex-labels)])
    (when (for/or ([k (in-list keywords)]) (regexp-match? (pregexp (regexp-quote (~a k))) lab))
      (set! out (cons lab out))))
  (reverse out))

(define (reg-add-l! id domain type antecedents witness #:keywords [keywords '()])
  (define entry (hash 'id (~a id)
                      'domain (~a domain)
                      'type (~a type)
                      'antecedents (for/list ([a antecedents]) (~a a))
                      'ok #t
                      'expr (sexpr-of-witness witness)
                      'pretty (pretty-of-witness witness)
                      'latex (latex-of-witness witness)
                      'labels (find-labels keywords)))
  (set! current-reg (append current-reg (list entry))))

(define (reg-add-bool! id domain type antecedents ok)
  (define entry (hash 'id (~a id)
                      'domain (~a domain)
                      'type (~a type)
                      'antecedents (for/list ([a antecedents]) (~a a))
                      'ok (and ok #t)))
  (set! current-reg (append current-reg (list entry))))

(define (reg-write! [path "tools/proof-registry.json"]) 
  (define (->json v)
    (cond
      [(or (string? v) (boolean? v) (number? v)) v]
      [(symbol? v) (~a v)]
      [(list? v) (map ->json v)]
      [else (~a v)]))
  (define (jsonify-entry e)
    (define out (make-hash))
    (for ([(k v) (in-hash e)])
      (hash-set! out (~a k) (->json v)))
    out)
  (define arr (for/list ([e current-reg]) (jsonify-entry e)))
  (call-with-output-file path
    (λ (out)
      (displayln (jsexpr->string arr) out))
    #:exists 'truncate))

(define (reg-write-coverage! [path "tools/proof-registry-coverage.txt"]) 
  (call-with-output-file path
    (λ (out)
      (for ([e current-reg])
        (fprintf out "~a\t~a\t~a\t~a\n"
                 (hash-ref e 'id) (hash-ref e 'domain)
                 (hash-ref e 'type) (string-join (hash-ref e 'labels) ", "))))
    #:exists 'truncate))
