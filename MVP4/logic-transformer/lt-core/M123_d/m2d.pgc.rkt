#lang typed/racket
(require "m3d.graph.rkt" "m2d.semiring-optimized.rkt" "m2d.pgc-core.rkt")
(provide PGC MatchX Exists And Or Not Top
         MatchX? Exists? And? Or? Not? Top?
         pgc-top pgc-match pgc-exists pgc-and pgc-or pgc-not
         GuardEnv initial-guard
         satisfies? satisfies^ pgc-eval
         ;; Re-export semiring functionality
         Semiring Semiring? Logic Logic?
         logic/boolean-top logic/boolean-maybe
         logic/log-exp
         BoolRig KleeneRig TropicalRig ExpLogRig)

;; satisfaction (guarded) — now uses semiring-based evaluation
;; The old implementation is replaced by the semiring-based system
;; This maintains backward compatibility while providing the new functionality

;; Backward compatibility: default satisfies? function using boolean-top logic with global observer
(: satisfies? (-> TGraph GuardEnv PGC Boolean))
(define (satisfies? G γ φ)
  (satisfies^ logic/boolean-top 'global G γ φ))
