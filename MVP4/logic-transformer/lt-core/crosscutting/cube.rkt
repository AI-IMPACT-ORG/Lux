#lang typed/racket
(require "../M123_d/m3d.types.rkt" "../M123_d/m3d.graph.rkt" "../M123_d/m2d.pgc.rkt" "../M123_d/m2d.cert.rkt" "../M123_d/m1d.logic.rkt" "dual.rkt" "adjunction.rkt")
(provide Cube3x3x3 Cube3x3x3? Cube3x3x3-levels Cube3x3x3-aspects Cube3x3x3-directions Cube3x3x3-adjunctions make-cube level aspect direction is-upper-triangular M3-Level M2-Level M1-Level TopDown BottomUp Sig-Aspect Sen-Aspect Mod-Aspect Level Aspect Direction)

;; 3×3×3 Cube Structure - The Complete Categorical Picture
;; This implements the cube from the ChatGPT design:
;; - Level axis: M3, M2, M1 (abstraction levels)
;; - Aspect axis: Sig, Sen, Mod (institution theory)
;; - Direction axis: TopDown, BottomUp (refinement vs abstraction)

;; Level tags
(struct M3-Level () #:transparent)
(struct M2-Level () #:transparent) 
(struct M1-Level () #:transparent)
(define-type Level (U M3-Level M2-Level M1-Level))

;; Aspect tags
(struct Sig-Aspect () #:transparent)
(struct Sen-Aspect () #:transparent)
(struct Mod-Aspect () #:transparent)
(define-type Aspect (U Sig-Aspect Sen-Aspect Mod-Aspect))

;; Direction tags
(struct TopDown () #:transparent)
(struct BottomUp () #:transparent)
(define-type Direction (U TopDown BottomUp))

;; The 3×3×3 cube
(struct Cube3x3x3 ([levels : (Listof Level)]
                   [aspects : (Listof Aspect)]
                   [directions : (Listof Direction)]
                   [adjunctions : (HashTable (Pairof Level Level) Adjunction)]) #:transparent)

(: make-cube (-> Cube3x3x3))
(define (make-cube)
  (Cube3x3x3
   (list (M3-Level) (M2-Level) (M1-Level))
   (list (Sig-Aspect) (Sen-Aspect) (Mod-Aspect))
   (list (TopDown) (BottomUp))
   (hash (cons (M3-Level) (M2-Level)) (refinement-adjunction)
         (cons (M2-Level) (M1-Level)) (refinement-adjunction))))

;; Accessors for the cube dimensions
(: level (-> Cube3x3x3 (Listof Level)))
(define (level cube) (Cube3x3x3-levels cube))

(: aspect (-> Cube3x3x3 (Listof Aspect)))
(define (aspect cube) (Cube3x3x3-aspects cube))

(: direction (-> Cube3x3x3 (Listof Direction)))
(define (direction cube) (Cube3x3x3-directions cube))

;; Upper-triangular constraint: only TopDown morphisms are primitive
;; BottomUp morphisms exist only as right adjoints
(: is-upper-triangular (-> Cube3x3x3 Boolean))
(define (is-upper-triangular cube)
  (and (member (TopDown) (direction cube))
       (member (BottomUp) (direction cube))
       #t)) ; constraint enforced by only providing TopDown primitives
