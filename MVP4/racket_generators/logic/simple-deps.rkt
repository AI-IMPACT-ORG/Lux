#lang racket

;; Simple CLEAN v10 Dependency Analysis
(require racket/file racket/path racket/string)

;; Extract require statements from a file
(define (extract-requires file-path)
  (define content (file->string file-path))
  (define lines (string-split content "\n"))
  (define requires '())
  
  (for ([line lines])
    (when (string-contains? line "require")
      (define trimmed (string-trim line))
      (when (string-prefix? trimmed "(require")
        (define matches (regexp-match* #px"\"([^\"]+\\.rkt)\"" trimmed))
        (for ([match matches])
          (set! requires (cons (cadr match) requires)))))
  requires)

;; Find all .rkt files
(define (find-racket-files root-path)
  (define files '())
  (for ([path (in-directory root-path)])
    (when (and (file-exists? path)
               (string-suffix? (path->string path) ".rkt")
               (not (string-contains? (path->string path) "archive")))
      (set! files (cons (path->string path) files))))
  files)

;; Categorize by layer
(define (categorize-file file-path)
  (cond
    [(string-contains? file-path "core/") "core"]
    [(string-contains? file-path "class/domain/DomainPortAPI") "domain-api"]
    [(string-contains? file-path "class/domain/") "domain-ports"]
    [(string-contains? file-path "tests/layers/core/") "test-core"]
    [(string-contains? file-path "tests/layers/domain-api/") "test-domain-api"]
    [(string-contains? file-path "tests/layers/domain-ports/") "test-domain-ports"]
    [(string-contains? file-path "tests/layers/integration/") "test-integration"]
    [(string-contains? file-path "tests/layers/") "test-utilities"]
    [(string-contains? file-path "class/") "class"]
    [(string-contains? file-path "tooling/") "tooling"]
    [else "root"]))

;; Main analysis
(define (analyze-dependencies)
  (displayln "=== CLEAN v10 Dependency Analysis ===")
  (displayln "")
  
  (define files (find-racket-files "."))
  (displayln (format "Found ~a files" (length files)))
  
  (define layer-counts (make-hash))
  (define dependencies '())
  
  (for ([file files])
    (define layer (categorize-file file))
    (hash-set! layer-counts layer (add1 (hash-ref layer-counts layer 0)))
    
    (define requires (extract-requires file))
    (for ([req requires])
      (set! dependencies (cons (list file req) dependencies))))
  
  (displayln "\n=== Layer Distribution ===")
  (for ([(layer count) layer-counts])
    (displayln (format "~a: ~a files" layer count)))
  
  (displayln "\n=== Dependencies ===")
  (displayln (format "Total dependencies: ~a" (length dependencies)))
  
  (displayln "\n=== Files by Layer ===")
  (for ([file files])
    (define layer (categorize-file file))
    (define short-name (path->string (file-name-from-path file)))
    (displayln (format "~a (~a)" short-name layer)))
  
  (displayln "\n=== Dependency Details ===")
  (for ([dep dependencies])
    (define from-file (path->string (file-name-from-path (car dep))))
    (define to-file (path->string (file-name-from-path (cadr dep))))
    (displayln (format "~a -> ~a" from-file to-file)))
  
  (displayln "\n=== Analysis Complete ==="))

;; Run analysis
(analyze-dependencies)

