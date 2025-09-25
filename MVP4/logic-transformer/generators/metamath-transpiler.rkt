#lang racket

(require "../lt-core/main.rkt")

(define axioms-path "../formal/metamath/TranspiledAxioms.mm")
(define checks-path "../formal/metamath/TranspiledCrosschecks.mm")

(define-values (sample-graph _sample-top _residual) (host-bundle))
(define T (TGraph-T sample-graph))

(define ports (sort (hash-keys (TypeGraph-ports T)) symbol<?))
(define kinds (sort (hash-keys (TypeGraph-kinds T)) symbol<?))
(define sigma6-arity (arity-of T Sigma6))
(define sigma6-m (Arity-m sigma6-arity))
(define sigma6-n (Arity-n sigma6-arity))

(define (render-symbol-list syms)
  (string-join (map symbol->string syms) ", "))

(define header-comment
  (format "$(\nAuto-generated from lt-core/host-bundle\nPorts (~a): {~a}\nEdge kinds (~a): {~a}\nSigma6 arity: (~a, ~a)\n$)\n\n"
          (length ports) (render-symbol-list ports)
          (length kinds) (render-symbol-list kinds)
          sigma6-m sigma6-n))

(define class-section
  "$( ==================== Class Layer : Green's Function ==================== $)\n$c GreenKernel GreenBoundary GreenPropagator GreenRenormalizer $.\nGreenKernel-def $a |- class GreenKernel $.\nGreenBoundary-def $a |- class GreenBoundary $.\nGreenPropagator-def $a |- class GreenPropagator $.\nGreenRenormalizer-def $a |- class GreenRenormalizer $.\n\n")

(define set-section
  (format "$( ==================== Set Layer : Typed Structures ==================== $)\n$c PortBundle EdgeBundle TypedSlots ModuliLattice $.\n$( Derived from ports {~a} $)\nPortBundle-def $a |- set PortBundle $.\n$( Derived from edge kinds {~a} $)\nEdgeBundle-def $a |- set EdgeBundle $.\n$( Slots per sigma6: ~a inbound, ~a outbound $)\nTypedSlots-def $a |- set TypedSlots $.\nModuliLattice-def $a |- set ModuliLattice $.\n\n"
          (render-symbol-list ports)
          (render-symbol-list kinds)
          sigma6-m sigma6-n))

(define wff-syntax
  "$( Syntax for Boolean/Digital layer $)\n$c TruthTop TruthBottom TruthJoin TruthMeet TruthNeg TruthImp $.\nTruthTop-wff $a wff TruthTop $.\nTruthBottom-wff $a wff TruthBottom $.\nTruthJoin-wff $a wff ( TruthJoin ph ps ) $.\nTruthMeet-wff $a wff ( TruthMeet ph ps ) $.\nTruthNeg-wff $a wff ( TruthNeg ph ) $.\nTruthImp-wff $a wff ( TruthImp ph ps ) $.\n\n")

(define wff-axioms
  "$( ==================== WFF Layer : Boolean / Digital Core ==================== $)\nTruthTop-axiom $a |- ( TruthImp ph ( TruthJoin ph TruthTop ) ) $.\nTruthBottom-axiom $a |- ( TruthImp ( TruthMeet ph TruthBottom ) TruthBottom ) $.\nTruthMerge-axiom $a |- ( TruthImp ( TruthMeet ph ps ) ( TruthMeet ps ph ) ) $.\nTruthSplit-axiom $a |- ( TruthImp ( TruthImp ph ps ) ( TruthImp ( TruthNeg ps ) ( TruthNeg ph ) ) ) $.\n")

(call-with-output-file axioms-path
  (lambda (out)
    (display header-comment out)
    (display "$[ BootstrapPaperFoundation.mm $]\n\n" out)
    (display class-section out)
    (display set-section out)
    (display wff-syntax out)
    (display wff-axioms out))
  #:exists 'replace)

(define crosscheck-content
  (string-append
   "$(\nCross-check suite auto-generated alongside TranspiledAxioms.mm\n$)\n\n"
   "$[ BootstrapPaperFoundation.mm $]\n"
   "$[ TranspiledAxioms.mm $]\n\n"
   "$( ==================== Class Layer Checks ==================== $)\n"
   "GreenKernel-check $p |- class GreenKernel $=\n  GreenKernel-def $.\n\n"
   "GreenBoundary-check $p |- class GreenBoundary $=\n  GreenBoundary-def $.\n\n"
   "GreenPropagator-check $p |- class GreenPropagator $=\n  GreenPropagator-def $.\n\n"
   "GreenRenormalizer-check $p |- class GreenRenormalizer $=\n  GreenRenormalizer-def $.\n\n"
   "$( ==================== Set Layer Checks ==================== $)\n"
   "PortBundle-check $p |- set PortBundle $=\n  PortBundle-def $.\n\n"
   "EdgeBundle-check $p |- set EdgeBundle $=\n  EdgeBundle-def $.\n\n"
   "TypedSlots-check $p |- set TypedSlots $=\n  TypedSlots-def $.\n\n"
   "ModuliLattice-check $p |- set ModuliLattice $=\n  ModuliLattice-def $.\n\n"
   "$( ==================== Syntax Checks ==================== $)\n"
   "TruthTop-wff-check $p wff TruthTop $=\n  TruthTop-wff $.\n\n"
   "TruthBottom-wff-check $p wff TruthBottom $=\n  TruthBottom-wff $.\n\n"
   "TruthJoin-wff-check $p wff ( TruthJoin ph ps ) $=\n  TruthJoin-wff $.\n\n"
   "TruthMeet-wff-check $p wff ( TruthMeet ph ps ) $=\n  TruthMeet-wff $.\n\n"
   "TruthNeg-wff-check $p wff ( TruthNeg ph ) $=\n  TruthNeg-wff $.\n\n"
   "TruthImp-wff-check $p wff ( TruthImp ph ps ) $=\n  TruthImp-wff $.\n\n"
   "$( ==================== Boolean Axiom Checks ==================== $)\n"
   "TruthTop-axiom-check $p |- ( TruthImp ph ( TruthJoin ph TruthTop ) ) $=\n  TruthTop-axiom $.\n\n"
   "TruthBottom-axiom-check $p |- ( TruthImp ( TruthMeet ph TruthBottom ) TruthBottom ) $=\n  TruthBottom-axiom $.\n\n"
   "TruthMerge-axiom-check $p |- ( TruthImp ( TruthMeet ph ps ) ( TruthMeet ps ph ) ) $=\n  TruthMerge-axiom $.\n\n"
   "TruthSplit-axiom-check $p |- ( TruthImp ( TruthImp ph ps ) ( TruthImp ( TruthNeg ps ) ( TruthNeg ph ) ) ) $=\n  TruthSplit-axiom $.\n\n"))

(call-with-output-file checks-path
  (lambda (out)
    (display crosscheck-content out))
  #:exists 'replace)

(displayln (format "Generated ~a" axioms-path))
(displayln (format "Generated ~a" checks-path))
