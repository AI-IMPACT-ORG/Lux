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
  (define tests? #f)
  (define dry-run? #f) ; New option for dry run
  
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
   [("--dry-run") "Show what would be generated without creating files" 
    (set! dry-run? #t)]
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
  (if dry-run?
      (dry-run-generation target-lang output-dir verbose? test? deploy? tests?)
      (generate-libraries target-lang output-dir verbose? test? deploy? tests?)))

;; Dry run generation - show what would be generated without creating files
(define (dry-run-generation target-lang output-dir verbose? test? deploy? tests?)
  (displayln "🔍 DRY RUN MODE - No files will be created")
  (displayln (format "Target: ~a" target-lang))
  (displayln (format "Output: ~a" output-dir))
  (displayln (format "Options: verbose=~a, test=~a, deploy=~a, tests=~a" verbose? test? deploy? tests?))
  
  (define languages (if (eq? target-lang 'all) '(coq agda lean isabelle) (list target-lang)))
  
  (for-each (λ (lang)
              (define config (get-language-config lang))
              (displayln (format "📋 Would generate ~a library:" lang))
              (displayln (format "  - Files: ~a" (lang-config-ext config)))
              (displayln (format "  - Prefix: ~a" (lang-config-file-prefix config)))
              (displayln (format "  - Arrow: ~a" (lang-config-arrow config)))
              (displayln (format "  - Lambda: ~a" (lang-config-lambda config))))
            languages)
  
  (displayln "✅ Dry run completed"))

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

;; Generate all languages with progress reporting
(define (generate-all-languages base-output-dir verbose? test? deploy? tests?)
  (define languages '(coq agda lean isabelle))
  (define total (length languages))
  (define current 0)
  
  (when verbose?
    (displayln (format "📊 Generating ~a languages..." total)))
  
  (for-each (λ (lang) 
              (set! current (add1 current))
              (when verbose?
                (displayln (format "📈 Progress: ~a/~a (~a%)" 
                                   current total 
                                   (round (* 100 (/ current total))))))
              (generate-single-language lang base-output-dir verbose? test? deploy? tests?))
            languages)
  
  (when verbose?
    (displayln "🎉 All languages completed!")))

;; Generate single language with better error handling
(define (generate-single-language target-lang base-output-dir verbose? test? deploy? tests?)
  (with-handlers ([exn:fail? (λ (e) 
                                (displayln (format "❌ Error generating ~a: ~a" target-lang (exn-message e)))
                                (when verbose? (displayln (format "Stack trace: ~a" (exn-continuation-marks e)))))]
                  [exn:fail:contract? (λ (e) 
                                         (displayln (format "❌ Contract error in ~a: ~a" target-lang (exn-message e))))])
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
      (displayln (format "📁 Output directory: ~a" output-dir)))))

;; Run main if called directly
(module+ main (main))
