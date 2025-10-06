#lang racket

;; @logic/gen Package Configuration
;; Defines the package structure and dependencies

(define pkg-desc
  (hash
   'name "logic-gen"
   'version "0.1.0"
   'description "Generator-focused CLEAN language specification"
   'authors '("Rutger Boels")
   'dependencies '("base" "rackunit" "syntax-parse")
   'build-deps '()
   'test-deps '("rackunit")
   'tags '("logic" "generators" "clean" "formal-methods")
   'homepage "https://github.com/rutgerboels/BootstrapPaper"
   'license "MIT"))

;; Package structure
(define package-structure
  '("lang/reader.rkt"
    "lang/surface.rkt"
    "core.rkt"
    "truth.rkt"
    "rg.rkt"
    "ports/boolean.rkt"
    "examples/demo.gen"
    "tests/test-suite.rkt"))

;; Dependencies
(define dependencies
  '("base"
    "rackunit"
    "syntax-parse"
    "racket/contract"
    "racket/match"
    "racket/function"
    "racket/math"))

;; Test dependencies
(define test-dependencies
  '("rackunit"))

;; Build configuration
(define build-config
  (hash
   'compile-omit-paths '("tests" "examples")
   'test-omit-paths '("examples")
   'doc-omit-paths '("tests")))

;; Collection info
(define collection-info
  (hash
   'name "logic-gen"
   'version "0.1.0"
   'description "Generator-focused CLEAN language"
   'authors '("Rutger Boels")
   'dependencies dependencies
   'build-deps '()
   'test-deps test-dependencies))

;; Export the configuration
(provide pkg-desc
         package-structure
         dependencies
         test-dependencies
         build-config
         collection-info)

