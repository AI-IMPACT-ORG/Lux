#lang typed/racket
;; RG Generator - Simplified Architecture Using RG Operator
;; This implements a dramatically simplified generator using the RG operator interpretation
;; The RG operator provides a unified framework for all transformations

(require "../lt-core/M123_d/m3d.types.rkt"
         "../lt-core/M123_d/m3d.graph.rkt"
         "../lt-core/M123_d/m2d.pgc.rkt"
         "../lt-core/M123_d/m2d.semiring-optimized.rkt"
         "../lt-core/M123_d/m3d.entropy.rkt"
         "api-surface/library-api.rkt"
         racket/match
         racket/format
         racket/string)

(provide ;; RG Generator Core
         RGGenerator RGGenerator?
         make-rg-generator
         generate-library-rg
         
         ;; RG Flow Operations
         rg-flow rg-flow-inverse
         rg-beta-function rg-anomaly-measure
         rg-entropy-measure rg-fixed-point
         
         ;; Simplified Generation
         generate-coq-rg generate-agda-rg generate-isabelle-rg
         
         ;; Modular Agda Generation
         generate-modular-agda-library
         generate-agda-m3-module generate-agda-m2-module generate-agda-m1-module generate-agda-rg-module)

;; ============================================================================
;; RG GENERATOR - UNIFIED FRAMEWORK
;; ============================================================================

;; RG Generator: Single operator for all transformations
(struct RGGenerator ([rg-flow : (-> Any Symbol Any)]           ; RG flow: UV → IR
                     [rg-beta : (-> Any Natural)]             ; Beta function: β(g)
                     [rg-anomaly : (-> Any Boolean)]          ; Anomaly cancellation
                     [rg-entropy : (-> Any Natural)]          ; Entropy production
                     [rg-fixed-point : (-> Any Boolean)]      ; Fixed point detection
                     [target-language : String])              ; Target language
  #:transparent)

;; Create RG generator for a target language
(: make-rg-generator (-> String RGGenerator))
(define (make-rg-generator target-language)
  (RGGenerator rg-flow
               rg-beta-function
               rg-anomaly-measure
               rg-entropy-measure
               rg-fixed-point
               target-language))

;; ============================================================================
;; RG FLOW OPERATIONS - THE CORE MATHEMATICS
;; ============================================================================

;; RG Flow: UV scale → IR scale (type coercion as RG flow)
(: rg-flow (-> Any Symbol Any))
(define (rg-flow value target-type)
  (cond
    [(eq? target-type 'HashTable) (cast-to-hash value)]
    [(eq? target-type 'Boolean) (cast-to-boolean value)]
    [(eq? target-type 'String) (cast-to-string value)]
    [(eq? target-type 'LibraryAPI) 
     (if (hash? value)
         (make-library-api "RGGeneratedLibrary" "1.0.0" "RG-generated library")
         (cast value LibraryAPI))]
    [(eq? target-type 'TGraph) (cast value TGraph)]
    [(eq? target-type 'PGC) (cast value PGC)]
    [else value]))

;; Inverse RG Flow: IR scale → UV scale
(: rg-flow-inverse (-> Any Symbol Any))
(define (rg-flow-inverse value source-type)
  ;; For now, use identity - in full implementation, this would be the inverse flow
  value)

;; RG Beta Function: β(g) = dg/dt (anomaly measure as beta function)
(: rg-beta-function (-> Any Natural))
(define (rg-beta-function system)
  (cond
    [(TGraph? system) (anomaly-measure (cast system TypeGraph))]
    [(hash? system) (hash-count (cast system (HashTable Symbol Any)))]
    [else 0]))

;; RG Anomaly Measure: A[g] (anomaly cancellation)
(: rg-anomaly-measure (-> Any Boolean))
(define (rg-anomaly-measure system)
  (cond
    [(TGraph? system) (is-normalized? (cast system TGraph))]
    [(hash? system) (hash-has-key? (cast system (HashTable Symbol Any)) 'optimized)]
    [else #t]))

;; RG Entropy Production: S[g(t)]
(: rg-entropy-measure (-> Any Natural))
(define (rg-entropy-measure system)
  (cond
    [(TGraph? system) (entropy-measure-cached (cast system TGraph))]
    [(hash? system) (hash-count (cast system (HashTable Symbol Any)))]
    [else 0]))

;; RG Fixed Point: β(g*) = 0
(: rg-fixed-point (-> Any Boolean))
(define (rg-fixed-point system)
  (= (rg-beta-function system) 0))

;; ============================================================================
;; SIMPLIFIED GENERATION USING RG OPERATOR
;; ============================================================================

;; Generate library using RG operator (unified approach)
(: generate-library-rg (-> RGGenerator Any String String Void))
(define (generate-library-rg generator mde-system library-name output-dir)
  (let* ([rg-flow (RGGenerator-rg-flow generator)]
         [target-lang (RGGenerator-target-language generator)]
         [;; RG Flow: MDE System → Target Language
          api-surface (rg-flow mde-system 'LibraryAPI)]
         [;; RG Beta Function: Check if system is at fixed point
          is-fixed-point (rg-fixed-point mde-system)]
         [;; RG Anomaly: Check anomaly cancellation
          anomaly-cancelled (rg-anomaly-measure mde-system)]
         [;; RG Entropy: Check entropy bounds
          entropy (rg-entropy-measure mde-system)]
         [;; Generate target language code
          generated-code (cond
                          [(string=? target-lang "coq") (generate-coq-rg (cast api-surface LibraryAPI))]
                          [(string=? target-lang "agda") (generate-agda-rg (cast api-surface LibraryAPI))]
                          [(string=? target-lang "isabelle") (generate-isabelle-rg (cast api-surface LibraryAPI))]
                          [else (error (format "Unsupported target language: ~a" target-lang))])])
    
    ;; RG Consistency Check
    (when (not (and is-fixed-point anomaly-cancelled (< entropy 100)))
      (printf "⚠️  RG Warning: System not at fixed point or anomaly not cancelled\n"))
    
    ;; Write generated code
    (let ([output-file (build-path output-dir (string-append library-name 
                                                             (cond
                                                               [(string=? target-lang "coq") ".v"]
                                                               [(string=? target-lang "agda") ".agda"]
                                                               [(string=? target-lang "isabelle") ".thy"]
                                                               [else ".txt"])))])
      (make-directory* output-dir)
      (call-with-output-file output-file
        (λ ([out : Output-Port]) (write-string generated-code out)))
      (printf "✅ RG Generated ~a library '~a' in ~a\n" target-lang library-name output-dir))))

;; ============================================================================
;; LANGUAGE-SPECIFIC RG GENERATORS
;; ============================================================================

;; Coq RG Generator - Enhanced with Complete MDE Pyramid
(: generate-coq-rg (-> LibraryAPI String))
(define (generate-coq-rg api)
  (let ([name (LibraryAPI-name api)]
        [version (LibraryAPI-version api)]
        [description (LibraryAPI-description api)]
        [modules (LibraryAPI-modules api)])
    (string-append
     "(* Coq Library Generated by RG Operator *)\n"
     "(* " description " *)\n"
     "(* Version: " version " *)\n\n"
     "Require Import Coq.Lists.List.\n"
     "Require Import Coq.Arith.Arith.\n"
     "Require Import Coq.Logic.FunctionalExtensionality.\n"
     "Require Import Coq.Logic.Classical.\n\n"
     "Module " name ".\n\n"
     "(* MDE Pyramid Components *)\n"
     "(* M3 Layer: Metametamodel Foundation *)\n"
     "Inductive TypeGraph : Type :=\n"
     "  | TG : list Symbol -> list Symbol -> TypeGraph.\n\n"
     "Inductive Arity : Type :=\n"
     "  | Ar : nat -> nat -> Arity.\n\n"
     "Inductive PortSort : Type :=\n"
     "  | Port : Symbol -> PortSort\n"
     "  | Pin : Symbol -> PortSort\n"
     "  | Input : Symbol -> PortSort\n"
     "  | Output : Symbol -> PortSort.\n\n"
     "Inductive EdgeKind : Type :=\n"
     "  | Sigma6 : EdgeKind\n"
     "  | Tensor : EdgeKind\n"
     "  | Wire : EdgeKind\n"
     "  | Unit : EdgeKind\n"
     "  | Cast : EdgeKind.\n\n"
     "Record ModuliSpace : Type :=\n"
     "  { mu1 mu2 mu3 mu4 : nat;\n"
     "    mu1_star mu2_star mu3_star mu4_star : nat;\n"
     "    lambda lambda_star : nat }.\n\n"
     "Inductive AnomalyFunc : Type :=\n"
     "  | Anomaly : nat -> AnomalyFunc.\n\n"
     "Definition anomaly_measure (a : AnomalyFunc) : nat :=\n"
     "  match a with\n"
     "  | Anomaly n => n\n"
     "  end.\n\n"
     "(* M2 Layer: Metamodel Structure *)\n"
     "Inductive PGC : Type :=\n"
     "  | PGC_True : PGC\n"
     "  | PGC_Implies : PGC -> PGC -> PGC\n"
     "  | PGC_And : PGC -> PGC -> PGC\n"
     "  | PGC_Or : PGC -> PGC -> PGC\n"
     "  | PGC_Not : PGC -> PGC.\n\n"
     "Inductive Certificate : Type :=\n"
     "  | Cert : PGC -> Certificate\n"
     "  | Witness : PGC -> Certificate.\n\n"
     "Inductive Semiring : Type :=\n"
     "  | Boolean : Semiring\n"
     "  | Natural : Semiring\n"
     "  | Tropical : Semiring.\n\n"
     "Inductive Logic : Type :=\n"
     "  | Classical : Logic\n"
     "  | Intuitionistic : Logic\n"
     "  | Linear : Logic.\n\n"
     "Inductive Satisfies : TypeGraph -> PGC -> Prop :=\n"
     "  | True_Sat : forall tg, Satisfies tg PGC_True\n"
     "  | Implies_Sat : forall tg p q, Satisfies tg p -> Satisfies tg q -> Satisfies tg (PGC_Implies p q)\n"
     "  | And_Sat : forall tg p q, Satisfies tg p -> Satisfies tg q -> Satisfies tg (PGC_And p q).\n\n"
     "(* M1 Layer: Model Logic *)\n"
     "Inductive TransformerLogic : Type :=\n"
     "  | TL : PGC -> TransformerLogic.\n\n"
     "Inductive InstanceGraph : Type :=\n"
     "  | IG : TypeGraph -> InstanceGraph.\n\n"
     "Inductive InstanceNode : Type :=\n"
     "  | IN : Symbol -> InstanceNode.\n\n"
     "Inductive InstanceEdge : Type :=\n"
     "  | IE : Symbol -> Symbol -> InstanceEdge.\n\n"
     "Definition godel_encode (tl : TransformerLogic) : nat :=\n"
     "  match tl with\n"
     "  | TL _ => 0\n"
     "  end.\n\n"
     "Definition instance_to_runtime (ig : InstanceGraph) : nat :=\n"
     "  match ig with\n"
     "  | IG _ => 1\n"
     "  end.\n\n"
     "Definition logic_convergence_point (tl : TransformerLogic) : TransformerLogic :=\n"
     "  match tl with\n"
     "  | TL p => TL p\n"
     "  end.\n\n"
     "(* RG Operator Functions *)\n"
     "Definition rg_flow (A : Type) (B : Type) (f : A -> B) : A -> B := f.\n\n"
     "Definition rg_beta_function (g : nat) : nat := g + 1.\n\n"
     "Definition rg_anomaly_measure (x : bool) : bool := negb x.\n\n"
     "Definition rg_entropy_measure (n : nat) : nat := n * 2.\n\n"
     "Definition rg_fixed_point (n : nat) : bool := (n =? 0).\n\n"
     "Definition rg_flow_inverse (A : Type) (B : Type) (f : A -> B) : A -> B := f.\n\n"
     "(* Generated from " (number->string (length modules)) " MDE modules *)\n"
     "End " name ".\n")))

;; Agda RG Generator - Enhanced with Modular MDE Components
(: generate-agda-rg (-> LibraryAPI String))
(define (generate-agda-rg api)
  (let ([name (LibraryAPI-name api)]
        [version (LibraryAPI-version api)]
        [description (LibraryAPI-description api)]
        [modules (LibraryAPI-modules api)])
    (string-append
     "-- Agda Library Generated by RG Operator\n"
     "-- " description "\n"
     "-- Version: " version "\n\n"
     "module " name " where\n\n"
     "-- Import MDE Pyramid Modules\n"
     "open import " name ".M3.Metametamodel\n"
     "open import " name ".M2.Metamodel\n"
     "open import " name ".M1.Model\n"
     "open import " name ".RG.Operators\n\n"
     "-- Main Library Module\n"
     "module " name " where\n"
     "  -- Re-export all MDE components\n"
     "  open " name ".M3.Metametamodel public\n"
     "  open " name ".M2.Metamodel public\n"
     "  open " name ".M1.Model public\n"
     "  open " name ".RG.Operators public\n\n"
     "-- Generated from " (number->string (length modules)) " MDE modules\n")))

;; Generate Agda M3 Module
(: generate-agda-m3-module (-> String String))
(define (generate-agda-m3-module library-name)
  (string-append
   "module " library-name ".M3.Metametamodel where\n\n"
   "-- M3 Layer: Metametamodel Foundation\n"
   "-- Maximum detail level - foundation types and signatures\n\n"
   "data TypeGraph : Set where\n"
   "  TG : List Symbol → List Symbol → TypeGraph\n\n"
   "data Arity : Set where\n"
   "  Ar : ℕ → ℕ → Arity\n\n"
   "data PortSort : Set where\n"
   "  Port : Symbol → PortSort\n"
   "  Pin : Symbol → PortSort\n"
   "  Input : Symbol → PortSort\n"
   "  Output : Symbol → PortSort\n\n"
   "data EdgeKind : Set where\n"
   "  Sigma6 : EdgeKind\n"
   "  Tensor : EdgeKind\n"
   "  Wire : EdgeKind\n"
   "  Unit : EdgeKind\n"
   "  Cast : EdgeKind\n\n"
   "-- Moduli space parameters\n"
   "record ModuliSpace : Set where\n"
   "  field\n"
   "    mu1 mu2 mu3 mu4 : ℕ\n"
   "    mu1* mu2* mu3* mu4* : ℕ\n"
   "    lambda lambda* : ℕ\n\n"
   "-- Anomaly functional\n"
   "data AnomalyFunc : Set where\n"
   "  Anomaly : ℕ → AnomalyFunc\n\n"
   "anomaly-measure : AnomalyFunc → ℕ\n"
   "anomaly-measure (Anomaly n) = n\n"))

;; Generate Agda M2 Module
(: generate-agda-m2-module (-> String String))
(define (generate-agda-m2-module library-name)
  (string-append
   "module " library-name ".M2.Metamodel where\n\n"
   "-- M2 Layer: Metamodel Structure\n"
   "-- Intermediate detail level - structure and certificates\n\n"
   "open import " library-name ".M3.Metametamodel\n\n"
   "data PGC : Set where\n"
   "  PGC-True : PGC\n"
   "  PGC-Implies : PGC → PGC → PGC\n"
   "  PGC-And : PGC → PGC → PGC\n"
   "  PGC-Or : PGC → PGC → PGC\n"
   "  PGC-Not : PGC → PGC\n\n"
   "data Certificate : Set where\n"
   "  Cert : PGC → Certificate\n"
   "  Witness : PGC → Certificate\n\n"
   "-- Semiring-based evaluation\n"
   "data Semiring : Set where\n"
   "  Boolean : Semiring\n"
   "  Natural : Semiring\n"
   "  Tropical : Semiring\n\n"
   "data Logic : Set where\n"
   "  Classical : Logic\n"
   "  Intuitionistic : Logic\n"
   "  Linear : Logic\n\n"
   "-- Satisfaction relation\n"
   "data _⊨_ : TypeGraph → PGC → Set where\n"
   "  True-Sat : ∀ {tg} → tg ⊨ PGC-True\n"
   "  Implies-Sat : ∀ {tg p q} → tg ⊨ p → tg ⊨ q → tg ⊨ PGC-Implies p q\n"))

;; Generate Agda M1 Module
(: generate-agda-m1-module (-> String String))
(define (generate-agda-m1-module library-name)
  (string-append
   "module " library-name ".M1.Model where\n\n"
   "-- M1 Layer: Model Logic\n"
   "-- Minimal detail level - single transformer logic\n\n"
   "open import " library-name ".M2.Metamodel\n\n"
   "data TransformerLogic : Set where\n"
   "  TL : PGC → TransformerLogic\n\n"
   "data InstanceGraph : Set where\n"
   "  IG : TypeGraph → InstanceGraph\n\n"
   "data InstanceNode : Set where\n"
   "  IN : Symbol → InstanceNode\n\n"
   "data InstanceEdge : Set where\n"
   "  IE : Symbol → Symbol → InstanceEdge\n\n"
   "-- Gödel encoding for runtime\n"
   "godel-encode : TransformerLogic → ℕ\n"
   "godel-encode (TL p) = 0  -- Simplified encoding\n\n"
   "-- Instance to runtime transformation\n"
   "instance-to-runtime : InstanceGraph → ℕ\n"
   "instance-to-runtime (IG tg) = 1  -- Simplified transformation\n\n"
   "-- Logic convergence point\n"
   "logic-convergence-point : TransformerLogic → TransformerLogic\n"
   "logic-convergence-point (TL p) = TL p\n"))

;; Generate Agda RG Operators Module
(: generate-agda-rg-module (-> String String))
(define (generate-agda-rg-module library-name)
  (string-append
   "module " library-name ".RG.Operators where\n\n"
   "-- RG Operator Functions\n"
   "-- Renormalization Group operators for type coercion and flow\n\n"
   "open import " library-name ".M1.Model\n\n"
   "-- RG Flow: UV scale → IR scale (type coercion as RG flow)\n"
   "rg-flow : {A B : Set} → (A → B) → A → B\n"
   "rg-flow f = f\n\n"
   "-- RG Beta Function: β(g) = dg/dt (anomaly measure)\n"
   "rg-beta-function : ℕ → ℕ\n"
   "rg-beta-function g = suc g\n\n"
   "-- RG Anomaly: A[g] + δL = 0 (anomaly cancellation)\n"
   "rg-anomaly-measure : Bool → Bool\n"
   "rg-anomaly-measure x = not x\n\n"
   "-- RG Entropy: S[g] (entropy production)\n"
   "rg-entropy-measure : ℕ → ℕ\n"
   "rg-entropy-measure n = n + n\n\n"
   "-- RG Fixed Point: β(g*) = 0 (fixed point detection)\n"
   "rg-fixed-point : ℕ → Bool\n"
   "rg-fixed-point zero = true\n"
   "rg-fixed-point (suc _) = false\n\n"
   "-- RG Flow Inverse: IR scale → UV scale\n"
   "rg-flow-inverse : {A B : Set} → (A → B) → A → B\n"
   "rg-flow-inverse f = f\n"))

;; Isabelle RG Generator - Enhanced with Complete MDE Pyramid
(: generate-isabelle-rg (-> LibraryAPI String))
(define (generate-isabelle-rg api)
  (let ([name (LibraryAPI-name api)]
        [version (LibraryAPI-version api)]
        [description (LibraryAPI-description api)]
        [modules (LibraryAPI-modules api)])
    (string-append
     "(* Isabelle Library Generated by RG Operator *)\n"
     "(* " description " *)\n"
     "(* Version: " version " *)\n\n"
     "theory " name "\n"
     "  imports Main\n"
     "begin\n\n"
     "(* MDE Pyramid Components *)\n"
     "(* M3 Layer: Metametamodel Foundation *)\n"
     "datatype TypeGraph = TG \"string list\" \"string list\"\n\n"
     "datatype Arity = Ar nat nat\n\n"
     "datatype PortSort = Port string | Pin string | Input string | Output string\n\n"
     "datatype EdgeKind = Sigma6 | Tensor | Wire | Unit | Cast\n\n"
     "record ModuliSpace = \n"
     "  mu1 :: nat\n"
     "  mu2 :: nat\n"
     "  mu3 :: nat\n"
     "  mu4 :: nat\n"
     "  mu1_star :: nat\n"
     "  mu2_star :: nat\n"
     "  mu3_star :: nat\n"
     "  mu4_star :: nat\n"
     "  lambda :: nat\n"
     "  lambda_star :: nat\n\n"
     "datatype AnomalyFunc = Anomaly nat\n\n"
     "definition anomaly_measure :: \"AnomalyFunc ⇒ nat\" where\n"
     "  \"anomaly_measure a = (case a of Anomaly n ⇒ n)\"\n\n"
     "(* M2 Layer: Metamodel Structure *)\n"
     "datatype PGC = PGC_True | PGC_Implies PGC PGC | PGC_And PGC PGC | PGC_Or PGC PGC | PGC_Not PGC\n\n"
     "datatype Certificate = Cert PGC | Witness PGC\n\n"
     "datatype Semiring = Boolean | Natural | Tropical\n\n"
     "datatype Logic = Classical | Intuitionistic | Linear\n\n"
     "inductive Satisfies :: \"TypeGraph ⇒ PGC ⇒ bool\" where\n"
     "  True_Sat: \"Satisfies tg PGC_True\" |\n"
     "  Implies_Sat: \"Satisfies tg p ⟹ Satisfies tg q ⟹ Satisfies tg (PGC_Implies p q)\" |\n"
     "  And_Sat: \"Satisfies tg p ⟹ Satisfies tg q ⟹ Satisfies tg (PGC_And p q)\"\n\n"
     "(* M1 Layer: Model Logic *)\n"
     "datatype TransformerLogic = TL PGC\n\n"
     "datatype InstanceGraph = IG TypeGraph\n\n"
     "datatype InstanceNode = IN string\n\n"
     "datatype InstanceEdge = IE string string\n\n"
     "definition godel_encode :: \"TransformerLogic ⇒ nat\" where\n"
     "  \"godel_encode tl = (case tl of TL _ ⇒ 0)\"\n\n"
     "definition instance_to_runtime :: \"InstanceGraph ⇒ nat\" where\n"
     "  \"instance_to_runtime ig = (case ig of IG _ ⇒ 1)\"\n\n"
     "definition logic_convergence_point :: \"TransformerLogic ⇒ TransformerLogic\" where\n"
     "  \"logic_convergence_point tl = (case tl of TL p ⇒ TL p)\"\n\n"
     "(* RG Operator Functions *)\n"
     "definition rg_flow :: \"('a ⇒ 'b) ⇒ 'a ⇒ 'b\" where\n"
     "  \"rg_flow f = f\"\n\n"
     "definition rg_beta_function :: \"nat ⇒ nat\" where\n"
     "  \"rg_beta_function g = Suc g\"\n\n"
     "definition rg_anomaly_measure :: \"bool ⇒ bool\" where\n"
     "  \"rg_anomaly_measure x = (¬ x)\"\n\n"
     "definition rg_entropy_measure :: \"nat ⇒ nat\" where\n"
     "  \"rg_entropy_measure n = n + n\"\n\n"
     "definition rg_fixed_point :: \"nat ⇒ bool\" where\n"
     "  \"rg_fixed_point n = (n = 0)\"\n\n"
     "definition rg_flow_inverse :: \"('a ⇒ 'b) ⇒ 'a ⇒ 'b\" where\n"
     "  \"rg_flow_inverse f = f\"\n\n"
     "(* Generated from " (number->string (length modules)) " MDE modules *)\n"
     "end\n")))

;; ============================================================================
;; RG GENERATOR CONVENIENCE FUNCTIONS
;; ============================================================================

;; Generate Coq library using RG operator
(: generate-coq-library-rg (-> String String Void))
(define (generate-coq-library-rg library-name output-dir)
  (let ([generator (make-rg-generator "coq")]
        [mde-system (hash 'name library-name 'version "1.0.0" 'description "RG-generated library")])
    (generate-library-rg generator mde-system library-name output-dir)
    (void)))

;; Generate Agda library using RG operator
(: generate-agda-library-rg (-> String String Void))
(define (generate-agda-library-rg library-name output-dir)
  (let ([generator (make-rg-generator "agda")]
        [mde-system (hash 'name library-name 'version "1.0.0" 'description "RG-generated library")])
    (generate-library-rg generator mde-system library-name output-dir)
    (void)))

;; Generate Isabelle library using RG operator
(: generate-isabelle-library-rg (-> String String Void))
(define (generate-isabelle-library-rg library-name output-dir)
  (let ([generator (make-rg-generator "isabelle")]
        [mde-system (hash 'name library-name 'version "1.0.0" 'description "RG-generated library")])
    (generate-library-rg generator mde-system library-name output-dir)
    (void)))

;; ============================================================================
;; MODULAR AGDA GENERATION FUNCTIONS
;; ============================================================================

(: generate-modular-agda-library (-> String String String String String))
(define (generate-modular-agda-library library-name version description output-dir)
  (let ([main-module (generate-agda-rg (make-library-api library-name version description))]
        [m3-module (generate-agda-m3-module library-name)]
        [m2-module (generate-agda-m2-module library-name)]
        [m1-module (generate-agda-m1-module library-name)]
        [rg-module (generate-agda-rg-module library-name)])
    
    ;; Write main module
    (with-output-to-file (string-append output-dir "/" library-name ".agda")
      (λ () (display main-module))
      #:exists 'replace)
    
    ;; Write M3 module
    (with-output-to-file (string-append output-dir "/" library-name ".M3.Metametamodel.agda")
      (λ () (display m3-module))
      #:exists 'replace)
    
    ;; Write M2 module
    (with-output-to-file (string-append output-dir "/" library-name ".M2.Metamodel.agda")
      (λ () (display m2-module))
      #:exists 'replace)
    
    ;; Write M1 module
    (with-output-to-file (string-append output-dir "/" library-name ".M1.Model.agda")
      (λ () (display m1-module))
      #:exists 'replace)
    
    ;; Write RG module
    (with-output-to-file (string-append output-dir "/" library-name ".RG.Operators.agda")
      (λ () (display rg-module))
      #:exists 'replace)
    
    (string-append "Generated modular Agda library: " library-name)))
