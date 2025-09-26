#lang typed/racket
;; PGC Core Definitions - Shared PGC constructors
;; This module provides the core PGC constructors that can be used across modules

(require "m3d.graph.rkt")

(provide ;; PGC AST (positive & guarded)
         PGC MatchX Exists And Or Not Top
         MatchX? Exists? And? Or? Not? Top?
         pgc-top pgc-match pgc-exists pgc-and pgc-or pgc-not
         GuardEnv initial-guard)

;; PGC AST (positive & guarded)
(struct Top () #:transparent)
(struct MatchX ([pat : TGraph]) #:transparent)
(struct Exists ([i : Submono] [Y : TGraph] [phi : PGC]) #:transparent)
(struct And ([l : PGC] [r : PGC]) #:transparent)
(struct Or  ([l : PGC] [r : PGC]) #:transparent)
(struct Not ([φ : PGC]) #:transparent)

(define-type PGC (U Top MatchX Exists And Or Not))
(define pgc-top (Top))
(: pgc-match (-> TGraph PGC)) (define (pgc-match X) (MatchX X))
(: pgc-exists (-> Submono TGraph PGC PGC))
(define (pgc-exists i Y phi) (Exists i Y phi))
(: pgc-and (-> PGC PGC PGC)) (define (pgc-and a b) (And a b))
(: pgc-or  (-> PGC PGC PGC)) (define (pgc-or a b) (Or a b))
(: pgc-not (-> PGC PGC)) (define (pgc-not φ) (Not φ))

;; guards (mono into host)
(struct GuardEnv ([rho : Submono]) #:transparent)
(: initial-guard (-> GuardEnv)) (define (initial-guard) (GuardEnv (Submono (set) (set))))

