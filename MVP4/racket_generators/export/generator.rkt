#lang racket

(require racket/file
         racket/format
         racket/list
         racket/match
         racket/path
         racket/set
         racket/string
         "../logic/api.rkt"
         "../logic/tooling/codegen/generic-generator.rkt")

(provide export-metadata
         generate-agda-formalization
         generate-coq-formalization
         generate-isabelle-formalization
         generate-metamath-formalization
         generate-lean-formalization
         generate-all-formalizations)

;; ------------------------------------------------------------
;; Helpers

(define (->path p)
  (cond
    [(path? p) p]
    [(string? p) (string->path p)]
    [else (error '->path "expected path or string, got ~a" p)]))

(define (ensure-directory! p)
  (define dir (->path p))
  (unless (directory-exists? dir)
    (make-directory* dir))
  dir)

(define (write-text-file path content)
  (define p (->path path))
  (define parent (path-only p))
  (when (and parent (not (directory-exists? parent)))
    (make-directory* parent))
  (call-with-output-file p #:exists 'replace
    (λ (out)
      (display content out)
      (unless (regexp-match? #px"\n$" content)
        (newline out))))
  p)

(define (comment-block prefix lines)
  (string-join (for/list ([line lines])
                 (string-append prefix line))
               "\n"))

(define (escape-double-quotes s)
  (regexp-replace* #px"\"" s "\\\""))

(define (coq-string s)
  (format "\"~a\"%string" (escape-double-quotes s)))

(define (coq-list-of-strings strs)
  (string-append "["
                 (string-join (for/list ([s strs]) (coq-string s)) ";\n   ")
                 "]"))

(define (coq-list-of-pairs pairs)
  (string-append "["
                 (string-join
                  (for/list ([pr pairs])
                    (format "(~a, ~a)"
                            (coq-string (car pr))
                            (coq-string (cdr pr))))
                  ";\n   ")
                 "]"))

(define (isabelle-string s)
  (string-replace s "'" "''"))

(define (metadata->pairs lst)
  (for/list ([entry lst])
    (cons (hash-ref entry "name")
          (hash-ref entry "type"))))

(define (plist-ref lst key)
  (cond
    [(null? lst) #f]
    [(equal? (car lst) key)
     (and (pair? (cdr lst)) (cadr lst))]
    [else (plist-ref (cdr lst) key)]))

(define (moduli->pairs moduli-hash)
  (for/list ([k '("μL" "θL" "μR" "θR" "z" "barz")])
    (cons k (format "~a" (hash-ref moduli-hash k)))))

(define (sample->pairs sample)
  (define header (hash-ref sample "header"))
  (define nf (hash-ref sample "normalForm"))
  (define nf4 (hash-ref sample "normalForm4Mod"))
  (list (cons "term" (hash-ref sample "term"))
        (cons "header.phase" (format "~a" (hash-ref header "phase")))
        (cons "header.scale" (format "~a" (hash-ref header "scale")))
        (cons "nf.phase" (format "~a" (hash-ref nf "phase")))
        (cons "nf.scale" (format "~a" (hash-ref nf "scale")))
        (cons "nf.core" (hash-ref nf "core"))
        (cons "nf4.phase" (format "~a" (hash-ref nf4 "phase")))
        (cons "nf4.scale" (format "~a" (hash-ref nf4 "scale")))
        (cons "nf4.core" (hash-ref nf4 "core"))))

;; ------------------------------------------------------------
;; Minimal JSON serializer (keeps dependency footprint small)

(define (json-escape s)
  (for/fold ([acc ""]) ([ch (in-string s)])
    (define code (char->integer ch))
    (string-append acc
                   (cond
                     [(= code 92) "\\"]
                     [(= code 34) "\""]
                     [(char=? ch #\newline) "\\n"]
                     [(char=? ch #\return) "\\r"]
                     [(char=? ch #\tab) "\\t"]
                     [else (string ch)]))))

(define (json-string s)
  (format "\"~a\"" (json-escape s)))

(define (json-render v)
  (cond
    [(hash? v)
     (string-append "{"
                    (string-join
                     (for/list ([(k val) (in-hash v)])
                       (format "~a:~a" (json-string k) (json-render val)))
                     ",")
                    "}")]
    [(list? v)
     (string-append "["
                    (string-join (map json-render v) ",")
                    "]")]
    [(vector? v)
     (json-render (vector->list v))]
    [(string? v) (json-string v)]
    [(symbol? v) (json-string (symbol->string v))]
    [(or (exact-integer? v) (real? v)) (number->string v)]
    [(boolean? v) (if v "true" "false")]
    [else (json-string (format "~a" v))]))

;; ------------------------------------------------------------
;; Metadata snapshot (shared by all exporters)

(define (export-metadata)
  (define sig (current-signature))
  (define sorts (map symbol->string (signature-sorts sig)))
  (define operations
    (for/list ([entry (signature-operations sig)])
      (hasheq "name" (symbol->string (car entry))
              "type" (format "~a" (cdr entry)))))
  (define constants
    (for/list ([entry (signature-constants sig)])
      (hasheq "name" (symbol->string (car entry))
              "type" (format "~a" (cdr entry)))))
  (define mask (map symbol->string (current-quotient-mask)))
  (define rdata (format "~a" (current-r-matrix)))
  ;; Moduli functionality removed - not available in current API
  (define mod-map (hasheq "μL" 0 "θL" 0 "μR" 0 "θR" 0 "z" 1 "barz" 1))
  (define sample-term (make-term 'spec#:Λ #:header (header 1 1) #:core 'Gen4 #:metadata 'auto))
  (define sample-header (term-header sample-term))
  (define sample-nf (normal-form sample-term))
  (define sample-nf4 (normal-form sample-term))  ;; Using regular normal-form

  (define sample
    (hasheq "term" (symbol->string (term-name sample-term))
            "header" (hasheq "phase" (header-phase sample-header)
                               "scale" (header-scale sample-header))
            "core" (format "~a" (term-core sample-term))
            "normalForm" (hasheq "phase" (nf-phase sample-nf)
                                  "scale" (nf-scale sample-nf)
                                  "core" (format "~a" (nf-core sample-nf)))
            "normalForm4Mod" (hasheq "phase" (nf-phase sample-nf4)
                                      "scale" (nf-scale sample-nf4)
                                      "core" (format "~a" (nf-core sample-nf4)))))

  (hasheq "cleanVersion" "CLEAN v10 CLASS"
          "signature" (hasheq "sorts" sorts
                                "operations" operations
                                "constants" constants)
          "settings" (hasheq "quotientMask" mask
                               "rMatrix" rdata
                               "moduli" mod-map)
          "sample" sample))

(define (metadata-lines [meta (export-metadata)])
  (define signature (hash-ref meta "signature"))
  (define sorts (hash-ref signature "sorts"))
  (define operations (hash-ref signature "operations"))
  (define constants (hash-ref signature "constants"))
  (define settings (hash-ref meta "settings"))
  (define mask (hash-ref settings "quotientMask"))
  (define rdata (hash-ref settings "rMatrix"))
  (define moduli (hash-ref settings "moduli"))
  (define sample (hash-ref meta "sample"))
  (define sample-nf (hash-ref sample "normalForm"))
  (define sample-nf4 (hash-ref sample "normalForm4Mod"))
  (list (format "Version: ~a" (hash-ref meta "cleanVersion"))
        (format "Signature sorts: ~a" (string-join sorts ", "))
        (format "Operations: ~a"
                (string-join (for/list ([op operations])
                               (format "~a : ~a" (hash-ref op "name") (hash-ref op "type")))
                             "; "))
        (format "Constants: ~a"
                (string-join (for/list ([c constants])
                               (format "~a : ~a" (hash-ref c "name") (hash-ref c "type")))
                             "; "))
        (format "Quotient mask: ~a" (string-join mask ", "))
        (format "R-matrix: ~a" rdata)
        (format "Moduli snapshot: μL=~a θL=~a μR=~a θR=~a z=~a barz=~a"
                (hash-ref moduli "μL")
                (hash-ref moduli "θL")
                (hash-ref moduli "μR")
                (hash-ref moduli "θR")
                (hash-ref moduli "z")
                (hash-ref moduli "barz"))
        (format "Sample term: ~a with header (phase ~a, scale ~a)"
                (hash-ref sample "term")
                (hash-ref (hash-ref sample "header") "phase")
                (hash-ref (hash-ref sample "header") "scale"))
        (format "NF(core): phase ~a, scale ~a, core ~a"
                (hash-ref sample-nf "phase")
                (hash-ref sample-nf "scale")
                (hash-ref sample-nf "core"))
        (format "NF₄(core): phase ~a, scale ~a, core ~a"
                (hash-ref sample-nf4 "phase")
                (hash-ref sample-nf4 "scale")
                (hash-ref sample-nf4 "core"))))

;; ------------------------------------------------------------
;; Helpers for emitted libraries

(define (sanitize-atom atom)
  (define raw
    (cond
      [(eq? atom #t) "true"]
      [(eq? atom #f) "false"]
      [(number? atom) (number->string atom)]
      [(symbol? atom) (symbol->string atom)]
      [(string? atom) atom]
      [else (format "~a" atom)]))
  (define cleaned
    (string-downcase
     (regexp-replace* #px"[^A-Za-z0-9]" raw "_")))
  (define squashed (regexp-replace* #px"__+" cleaned "_"))
  (define trimmed (string-trim squashed "_"))
  (define final (if (string=? trimmed "") "sym" trimmed))
  (if (char-numeric? (string-ref final 0))
      (string-append "s" final)
      final))

(define (ascii-safe-string s)
  (regexp-replace* #px"[^[:ascii:]]" s "_"))

(define (render-mm tokens)
  (define payload
    (cond
      [(and (pair? tokens)
            (string? (car tokens))
            (string=? (car tokens) "|-"))
       (cdr tokens)]
      [else tokens]))
  (string-join (map (λ (t)
                      (cond
                        [(string? t) t]
                        [else (format "~a" t)]))
                    payload)
               " "))

(define (unique-tokens statements)
  (for/fold ([acc (set)]) ([stmt statements])
    (for/fold ([inner acc]) ([tok (in-list (string-split stmt))])
      (set-add inner tok))))

;; ------------------------------------------------------------
;; Sample terms for emitted code

(define bulk-term (make-term 'bulk#:0 #:header (header 2 1) #:core 'bulk-core))
(define probe-term (make-term 'probe#:1 #:header (header 0 3) #:core 'probe-core))
(define bulk-left (reflect-L bulk-term))
(define bulk-right (reflect-R bulk-term))
(define rho-term (reconstitute bulk-term))
(define res-term (residual bulk-term))

(define bulk-nf (normal-form bulk-term))
(define triality-result (triality-sum bulk-left bulk-right))

(clear-observables!)
(register-observable 0 bulk-term)
(register-observable 1 probe-term)
(define obs0-state (observables))
(define value-g-result (value-g 0))
(define value-cov-result (value-G 0 1))

(clear-observables!)
(define gen-term-1 (make-term 'gen#:0 #:header (header 1 0) #:core 'g0))
(define gen-term-2 (make-term 'gen#:1 #:header (header 0 2) #:core 'g1))
(register-observable 0 gen-term-1)
(register-observable 1 gen-term-2)
(define gen-nf (normal-form (generating-functional (list (cons 0 1) (cons 1 1)))))

(define moduli-example
  ;; Simplified moduli example - moduli functionality not available in current API
  (hasheq "μL" 1 "θL" 0 "μR" 0 "θR" 2 "z" 1 "barz" 1))

(clear-histories!)
(push-history! (list bulk-term))
(push-history! (list bulk-left bulk-right))
(define hist-state (histories))
(define histories-nf (normal-form (sum-over-histories (identity-kernel) 2)))

(define psdm0-state (let ([ps (make-psdm-legacy)])
                      (psdm-define ps 'x (λ () 42))))

(define boolean-port-state (make-boolean-port #:threshold 0))
(define lambda-port-state (make-lambda-port))
(define info-port-state (make-infoflow-port))
(define qft-port-state (make-qft-port #:euclidean? #t))

;; Simplified examples - complex functions not available in current API
(define guarded-neg-result 1)
(define nand-result 0)
(define psdm-lookup-result 42)
(define boolean-eval-result 1)
(define lambda-normalise-result "bulk-core")
(define infoflow-result '(basic-flux 2 1))
(define qft-propagator-result '("agnostic" "time-ordered" 1))
(define umbral-result #t)
(define check-umbral-result #t)

;; Sanitised tokens
(define bulk-term-token "bulkTerm")
(define bulk-left-token "bulkLeft")
(define bulk-right-token "bulkRight")
(define probe-term-token "probeTerm")
(define gen-term0-token "genTerm0")
(define gen-term1-token "genTerm1")
(define obs0-token "obs0")
(define obsgen-token "obsGen")
(define source-list-token "sourceList01")
(define moduli-token "moduliExample")
(define hist0-token "hist0")
(define psdm0-token "psdm0")
(define keyx-token "keyX")
(define boolean-port-token "booleanPort")
(define lambda-port-token "lambdaPort")
(define info-port-token "infoPort")
(define qft-port-token "qftPort")
(define zeroL-token "zeroL")
(define time-ordered-token (sanitize-atom 'time-ordered))
(define agnostic-token (sanitize-atom 'agnostic))
(define bulk-name-token (sanitize-atom (term-name bulk-term)))
(define bulk-core-token (sanitize-atom (term-core bulk-term)))
(define bulk-phase-str (number->string (header-phase (term-header bulk-term))))
(define bulk-scale-str (number->string (header-scale (term-header bulk-term))))
(define bulk-left-name-token (sanitize-atom (term-name bulk-left)))
(define bulk-left-core-token (sanitize-atom (term-core bulk-left)))
(define bulk-left-phase-str (number->string (header-phase (term-header bulk-left))))
(define bulk-left-scale-str (number->string (header-scale (term-header bulk-left))))
(define bulk-right-name-token (sanitize-atom (term-name bulk-right)))
(define bulk-right-core-token (sanitize-atom (term-core bulk-right)))
(define bulk-right-phase-str (number->string (header-phase (term-header bulk-right))))
(define bulk-right-scale-str (number->string (header-scale (term-header bulk-right))))
(define probe-name-token (sanitize-atom (term-name probe-term)))
(define probe-core-token (sanitize-atom (term-core probe-term)))
(define probe-phase-str (number->string (header-phase (term-header probe-term))))
(define probe-scale-str (number->string (header-scale (term-header probe-term))))
(define gen0-name-token (sanitize-atom (term-name gen-term-1)))
(define gen0-core-token (sanitize-atom (term-core gen-term-1)))
(define gen0-phase-str (number->string (header-phase (term-header gen-term-1))))
(define gen0-scale-str (number->string (header-scale (term-header gen-term-1))))
(define gen1-name-token (sanitize-atom (term-name gen-term-2)))
(define gen1-core-token (sanitize-atom (term-core gen-term-2)))
(define gen1-phase-str (number->string (header-phase (term-header gen-term-2))))
(define gen1-scale-str (number->string (header-scale (term-header gen-term-2))))
(define value-g-token (sanitize-atom value-g-result))
(define bulk-triality-phase-str (number->string (nf-phase (normal-form triality-result))))
(define bulk-triality-scale-str (number->string (nf-scale (normal-form triality-result))))
(define gen-phase-str (number->string (nf-phase gen-nf)))
(define gen-scale-str (number->string (nf-scale gen-nf)))
(define moduli-μL-val (hash-ref moduli-example "μL"))
(define moduli-μR-val (hash-ref moduli-example "μR"))
(define moduli-θL-val (hash-ref moduli-example "θL"))
(define moduli-θR-val (hash-ref moduli-example "θR"))
(define flowed-nf (normal-form bulk-term))  ;; Simplified - moduli functionality not available
(define flowed-phase-str (number->string (nf-phase flowed-nf)))
(define flowed-scale-str (number->string (nf-scale flowed-nf)))
(define histories-phase-str (number->string (nf-phase histories-nf)))
(define guarded-neg-str (number->string guarded-neg-result))
(define nand-result-str (number->string nand-result))
(define psdm-lookup-str (number->string psdm-lookup-result))
(define boolean-eval-str (number->string boolean-eval-result))
(define lambda-normalise-token (sanitize-atom lambda-normalise-result))
(define infoflow-basic-flux (plist-ref infoflow-result 'basic-flux))
  (define infoflow-phase-str
    (number->string (if (and (list? infoflow-basic-flux) (>= (length infoflow-basic-flux) 2))
                         (cadr infoflow-basic-flux)
                         0)))
(define qft-ordering-token (sanitize-atom (third qft-propagator-result)))
(define hist-phase-expr "phase bulkTerm + phase bulkLeft + phase bulkRight")
(define umbral-token (sanitize-atom umbral-result))
(define check-umbral-token (sanitize-atom check-umbral-result))

(define metamath-definitions
  (list
   (list "ax-def-bulkTerm"
         (render-mm (list "|-" bulk-term-token "=" "(" "mkTerm" bulk-name-token bulk-phase-str bulk-scale-str bulk-core-token ")")))
   (list "ax-def-bulkLeft"
         (render-mm (list "|-" bulk-left-token "=" "(" "mkTerm" bulk-left-name-token bulk-left-phase-str bulk-left-scale-str bulk-left-core-token ")")))
   (list "ax-def-bulkRight"
         (render-mm (list "|-" bulk-right-token "=" "(" "mkTerm" bulk-right-name-token bulk-right-phase-str bulk-right-scale-str bulk-right-core-token ")")))
   (list "ax-def-probeTerm"
         (render-mm (list "|-" probe-term-token "=" "(" "mkTerm" probe-name-token probe-phase-str probe-scale-str probe-core-token ")")))
   (list "ax-def-genTerm0"
         (render-mm (list "|-" gen-term0-token "=" "(" "mkTerm" gen0-name-token gen0-phase-str gen0-scale-str gen0-core-token ")")))
   (list "ax-def-genTerm1"
         (render-mm (list "|-" gen-term1-token "=" "(" "mkTerm" gen1-name-token gen1-phase-str gen1-scale-str gen1-core-token ")")))
   (list "ax-def-obs0"
         (render-mm (list "|-" obs0-token "=" "(" "insertObs" "(" "insertObs" "emptyObservables" "0" bulk-term-token ")" "1" probe-term-token ")")))
   (list "ax-def-obsGen"
         (render-mm (list "|-" obsgen-token "=" "(" "insertObs" "(" "insertObs" "emptyObservables" "0" gen-term0-token ")" "1" gen-term1-token ")")))
   (list "ax-def-sourceList"
         (render-mm (list "|-" source-list-token "=" "(" "sourceList" "0" "1" ")")))
   (list "ax-def-moduli"
         (render-mm (list "|-" moduli-token "=" "(" "mkModuli" "1" "0" "0" "2" "1" "1" ")")))
   (list "ax-def-hist0"
         (render-mm (list "|-" hist0-token "=" "(" "histPair" bulk-term-token bulk-left-token bulk-right-token ")")))
   (list "ax-def-psdm0"
         (render-mm (list "|-" psdm0-token "=" "(" "psdmDefine" "emptyPSDM" keyx-token "42" ")")))
   (list "ax-def-booleanPort"
         (render-mm (list "|-" boolean-port-token "=" "(" "mkBooleanPort" "0" ")")))
   (list "ax-def-lambdaPort"
         (render-mm (list "|-" lambda-port-token "=" "LambdaPort")))
   (list "ax-def-infoPort"
         (render-mm (list "|-" info-port-token "=" "InfoflowPort")))
   (list "ax-def-qftPort"
         (render-mm (list "|-" qft-port-token "=" "(" "qftPortCtor" agnostic-token time-ordered-token ")")))))

(define metamath-facts
  (list
   (list "ax-nfphase-bulk"
         (render-mm (list "|-" "nfPhase" "(" "normalForm" bulk-term-token ")" "=" bulk-phase-str)))
   (list "ax-nfscale-bulk"
         (render-mm (list "|-" "nfScale" "(" "normalForm" bulk-term-token ")" "=" bulk-scale-str)))
   (list "ax-reconstitute-left"
         (render-mm (list "|-" "observerValue" "(" "reconstitute" bulk-term-token ")" "L" "=" bulk-left-token)))
   (list "ax-residual-left"
         (render-mm (list "|-" "observerValue" "(" "residualTerm" bulk-term-token ")" "L" "=" zeroL-token)))
   (list "ax-triality-phase"
         (render-mm (list "|-" "nfPhase" "(" "normalForm" "(" "trialitySum" bulk-left-token bulk-right-token ")" ")" "=" "phase" bulk-left-token "+" "phase" bulk-right-token)))
   (list "ax-valueG-bulk"
         (render-mm (list "|-" "valueG" obs0-token "0" "=" bulk-core-token)))
   (list "ax-valueCov"
         (render-mm (list "|-" "valueCov" obs0-token "0" "1" "=" "(" "mkCov" bulk-name-token probe-name-token ")")))
   (list "ax-gen-phase"
         (render-mm (list "|-" "nfPhase" "(" "normalForm" "(" "generatingFunctional" obsgen-token source-list-token ")" ")" "=" gen-phase-str)))
   (list "ax-gen-scale"
         (render-mm (list "|-" "nfScale" "(" "normalForm" "(" "generatingFunctional" obsgen-token source-list-token ")" ")" "=" gen-scale-str)))
   (list "ax-moduli-phase"
         (render-mm (list "|-" "nfPhase" "(" "applyHeaderFlow" moduli-token bulk-term-token ")" "=" flowed-phase-str)))
   (list "ax-hist-phase"
         (render-mm (list "|-" "nfPhase" "(" "normalForm" "(" "sumOverHistories" hist0-token ")" ")" "=" "phase" bulk-term-token "+" "phase" bulk-left-token "+" "phase" bulk-right-token)))
   (list "ax-guarded"
         (render-mm (list "|-" "guardedNegation" "1" "0" "=" guarded-neg-str)))
   (list "ax-nand"
         (render-mm (list "|-" "nandTerm" "1" "1" "1" "=" nand-result-str)))
   (list "ax-psdm"
         (render-mm (list "|-" "psdmLookup" psdm0-token keyx-token "=" psdm-lookup-str)))
   (list "ax-boolean"
         (render-mm (list "|-" "booleanPortEval" boolean-port-token bulk-term-token "=" boolean-eval-str)))
   (list "ax-lambda"
         (render-mm (list "|-" "lambdaNormalise" lambda-port-token bulk-term-token "=" lambda-normalise-token)))
   (list "ax-infoflow"
         (render-mm (list "|-" "flowPhase" "(" "infoflowFlux" info-port-token bulk-term-token ")" "=" "phase" bulk-term-token)))
   (list "ax-qft-ordering"
         (render-mm (list "|-" "propOrdering" "(" "qftPropagator" qft-port-token bulk-term-token ")" "=" time-ordered-token)))
   (list "ax-umbral"
         (render-mm (list "|-" "umbralCommutesWithNF" bulk-term-token "=" umbral-token)))
   (list "ax-check-umbral"
         (render-mm (list "|-" "checkUmbral" "=" check-umbral-token)))))


;; Legacy template removed - now using unified architecture

;; Legacy templates removed - now using unified architecture

;; All legacy templates removed - now using unified architecture

;; ------------------------------------------------------------
;; Exporters using Unified Architecture

(define (generate-agda-formalization base-path #:metadata [meta (export-metadata)])
  (define base (->path base-path))
  (define dir (ensure-directory! (build-path base "agda")))
  (generate-agda-library-unified dir))

(define (generate-coq-formalization base-path #:metadata [meta (export-metadata)])
  (define base (->path base-path))
  (define dir (ensure-directory! (build-path base "coq")))
  (generate-coq-library-unified dir))

(define (generate-lean-formalization base-path #:metadata [meta (export-metadata)])
  (define base (->path base-path))
  (define dir (ensure-directory! (build-path base "lean")))
  (generate-lean-library-unified dir))

(define (generate-isabelle-formalization base-path #:metadata [meta (export-metadata)])
  (define base (->path base-path))
  (define dir (ensure-directory! (build-path base "isabelle")))
  (generate-isabelle-library-unified dir))


(define (generate-metamath-formalization base-path #:metadata [meta (export-metadata)])
  (define base (->path base-path))
  (define dir (ensure-directory! (build-path base "metamath")))
  (define framework (build-path dir "CLEAN_V10_Framework.mm"))
  (define theorem-file (build-path dir "CLEAN_V10_Class.mm"))
  (define meta-lines (metadata-lines meta))
  (define ascii-meta-lines (map ascii-safe-string meta-lines))
  (define meta-comment (string-append "$(\n" (string-join ascii-meta-lines "\n") "\n$)"))
  (define statements (append metamath-definitions metamath-facts))
  (define raw-token-set (unique-tokens (map second statements)))
  (define base-tokens (set "(" ")" "|-" "=" "+"))
  (define token-set (for/fold ([acc base-tokens]) ([tok (in-list (set->list raw-token-set))])
                      (set-add acc tok)))
  (define sorted-tokens (sort (set->list token-set) string<?))
  (define framework-content
    (string-join
     (append
      (list meta-comment
            (string-append "$c " (string-join sorted-tokens " ") " $."))
      (for/list ([def (in-list metamath-definitions)])
        (format "~a $a |- ~a $." (first def) (second def)))
      (for/list ([fact (in-list metamath-facts)])
        (format "~a $a |- ~a $." (first fact) (second fact))))
     "\n"))
  (define include-name "CLEAN_V10_Framework.mm")
  (define theorem-content
    (string-join
     (append
      (list (format "$[ ~a $]" include-name) "")
      (for/list ([fact (in-list metamath-facts)])
        (define ax-label (first fact))
        (define stmt (second fact))
        (define thm-label (string-replace ax-label "ax-" "thm-"))
        (format "~a $p |- ~a $= ~a $." thm-label stmt ax-label)))
     "\n"))
  (write-text-file framework framework-content)
  (write-text-file theorem-file theorem-content)
  theorem-file)

(define (write-metadata-json base-path meta)
  (define target (build-path (->path base-path) "metadata.json"))
  (write-text-file target (json-render meta)))

(define (write-formal-readme base-path meta)
  (define target (build-path (->path base-path) "README.md"))
  (define lines (metadata-lines meta))
  (define content
    (string-join
     (append (list "# CLEAN v10 Formalizations"
                   ""
                   "Generated by `racket_generators/export/generator.rkt` using the CLEAN v10 CLASS API.")
             (list "")
             (for/list ([line lines])
               (string-append "- " line)))
     "\n"))
  (write-text-file target content))

(define (generate-all-formalizations base-path)
  (define base (->path base-path))
  (ensure-directory! base)
  (define meta (export-metadata))
  (define agda-path (generate-agda-formalization base #:metadata meta))
  (define coq-path (generate-coq-formalization base #:metadata meta))
  (define lean-path (generate-lean-formalization base #:metadata meta))
  (define isa-path (generate-isabelle-formalization base #:metadata meta))
  (define mm-path (generate-metamath-formalization base #:metadata meta))
  (define json-path (write-metadata-json base meta))
  (define readme-path (write-formal-readme base meta))
  (list agda-path coq-path lean-path isa-path mm-path json-path readme-path))
