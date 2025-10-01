#lang racket

(require "../../../core/signature.rkt"
         "../../../core/nf.rkt")

(provide metamath-port?
         make-metamath-port
         metamath-port-signature
         metamath-port-label
         metamath-encode-term
         metamath-normalise
         metamath-statement?
         metamath-statement-label
         metamath-statement-hypotheses
         metamath-statement-conclusion)

(struct metamath-port (signature label)
  #:transparent)

(struct metamath-statement (label hypotheses conclusion)
  #:transparent)

(define (make-metamath-port #:signature [sig (current-signature)]
                            #:label [label 'CLEAN-V10])
  (metamath-port sig label))

(define (metamath-encode-term term)
  (format "(~a PHASE ~a SCALE ~a CORE ~a)"
          (term-name term)
          (car (term-header term))
          (cdr (term-header term))
          (term-core term)))

(define (metamath-normalise port term #:label [label #f] #:hypotheses [hyps '()])
  (define nf (normal-form term))
  (define conclusion
    (list 'wff
          (format "(~a_PHASE ~a)"
                  (term-name term)
                  (nf-phase nf))
          (format "(~a_SCALE ~a)"
                  (term-name term)
                  (nf-scale nf))
          (format "(~a_CORE ~a)"
                  (term-name term)
                  (nf-core nf))
          (format "(~a_NF (~a ~a ~a))"
                  (metamath-port-label port)
                  (nf-phase nf)
                  (nf-scale nf)
                  (nf-core nf))))
  (metamath-statement (or label (format "~a_nf" (term-name term)))
                      hyps
                      conclusion))
