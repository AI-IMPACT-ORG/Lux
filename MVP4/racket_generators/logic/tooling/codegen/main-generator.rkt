#lang racket

(require "generic-generator.rkt"
         "language-configs.rkt"
         "language-extensions.rkt"
         "test-harness-generator.rkt"
         racket/cmdline
         racket/file
         racket/path)

(provide (all-defined-out))

;; ============================================================================
;; MAIN GENERATOR ENTRY POINT
;; ============================================================================

;; Command line interface for generator
(define (main)
  (define target-lang #f)
  (define output-dir #f)
  (define verbose? #f)
  (define test? #f)
  (define deploy? #f)
  (define validate? #f)
  (define tests? #f) ; Added for test harness generation
  
  (command-line
   #:program "main-generator"
   #:once-each
   [("-t" "--target") LANG "Target language (coq|agda|lean|isabelle|all)" 
    (set! target-lang (string->symbol LANG))]
   [("-o" "--output") DIR "Output directory" 
    (set! output-dir DIR)]
   [("-v" "--verbose") "Verbose output" 
    (set! verbose? #t)]
   [("--test") "Test compilation after generation" 
    (set! test? #t)]
   [("--deploy") "Create deployment files" 
    (set! deploy? #t)]
   [("--validate") "Validate language configurations" 
    (set! validate? #t)]
   [("--tests") "Generate test harnesses" 
    (set! tests? #t)]
   #:args ()
   (void))
  
  ;; Validate configurations if requested
  (when validate?
    (validate-all-configurations))
  
  ;; Generate test harnesses if requested
  (when tests?
    (generate-all-test-harnesses (or output-dir "formal")))
  
  ;; Default values
  (when (not target-lang)
    (set! target-lang 'all))
  (when (not output-dir)
    (set! output-dir "formal"))
  
  ;; Generate libraries
  (generate-libraries target-lang output-dir verbose? test? deploy? tests?))

;; Generate libraries for specified target(s)
(define (generate-libraries target-lang output-dir verbose? test? deploy? tests?)
  (define base-output-dir (build-path output-dir))
  (make-directory* base-output-dir)
  
  (case target-lang
    ['all (generate-all-languages base-output-dir verbose? test? deploy? tests?)]
    ['coq (generate-single-language 'coq base-output-dir verbose? test? deploy? tests?)]
    ['agda (generate-single-language 'agda base-output-dir verbose? test? deploy? tests?)]
    ['lean (generate-single-language 'lean base-output-dir verbose? test? deploy? tests?)]
    ['isabelle (generate-single-language 'isabelle base-output-dir verbose? test? deploy? tests?)]
    [else (error (format "Unknown target language: ~a" target-lang))]))

;; Generate all languages
(define (generate-all-languages base-output-dir verbose? test? deploy? tests?)
  (for-each (λ (lang) (generate-single-language lang base-output-dir verbose? test? deploy? tests?))
            '(coq agda lean isabelle)))

;; Generate single language
(define (generate-single-language target-lang base-output-dir verbose? test? deploy? tests?)
  (define config (get-language-config target-lang))
  (define output-dir (build-path base-output-dir (symbol->string target-lang)))
  
  (when verbose?
    (displayln (format "🚀 Generating CLEAN v10 ~a Library..." (symbol->string target-lang))))
  
  ;; Generate the library
  (generate-library config output-dir verbose?)
  
  ;; Generate test harness if requested
  (when tests?
    (generate-test-harness config output-dir))
  
  ;; Create deployment files if requested
  (when deploy?
    (create-deployment-files config output-dir))
  
  ;; Test compilation if requested
  (when test?
    (test-compilation config output-dir))
  
  (when verbose?
    (displayln (format "✅ CLEAN v10 ~a Library generated successfully!" (symbol->string target-lang)))
    (displayln (format "📁 Output directory: ~a" output-dir))))

;; Run main if called directly
(module+ main (main))
