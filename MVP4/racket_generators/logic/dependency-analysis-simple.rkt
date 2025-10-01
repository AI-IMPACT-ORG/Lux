#lang racket

;; CLEAN v10 Dependency Analysis Tool - Simplified Version
;; Analyzes module dependencies and creates reports

(require racket/file
         racket/path
         racket/string
         racket/list
         racket/set)

(provide analyze-dependencies
         generate-dependency-report
         find-circular-dependencies)

;; Extract require statements from a Racket file
(define (extract-requires file-path)
  "Extract all require statements from a Racket file"
  (define content (file->string file-path))
  (define lines (string-split content "\n"))
  
  (define requires '())
  (for ([line lines])
    (when (string-contains? line "require")
      (define trimmed (string-trim line))
      (when (and (string-prefix? trimmed "(require")
                 (not (string-contains? trimmed "provide")))
        ;; Simple extraction - look for quoted strings
        (define matches (regexp-match* #px"\"([^\"]+\\.rkt)\"" trimmed))
        (for ([match matches])
          (set! requires (cons (cadr match) requires)))))
  requires)

;; Find all Racket files recursively
(define (find-racket-files root-path)
  "Find all .rkt files recursively, excluding archives"
  (define files '())
  (for ([path (in-directory root-path)])
    (when (and (file-exists? path)
               (string-suffix? (path->string path) ".rkt")
               (not (string-contains? (path->string path) "archive")))
      (set! files (cons (path->string path) files))))
  files)

;; Build dependency graph
(define (build-dependency-graph root-path)
  "Build a dependency graph from all Racket files"
  (define files (find-racket-files root-path))
  (define graph (make-hash))
  
  ;; Initialize graph
  (for ([file files])
    (hash-set! graph file (set)))
  
  ;; Add dependencies
  (for ([file files])
    (define requires (extract-requires file))
    (for ([req requires])
      (define resolved-path (resolve-module-path req file root-path))
      (when resolved-path
        (define current-deps (hash-ref graph file))
        (hash-set! graph file (set-add current-deps resolved-path)))))
  
  graph)

;; Resolve module path to actual file path
(define (resolve-module-path module-path current-file root-path)
  "Resolve a module path to an actual file path"
  (define current-dir (path-only current-file))
  (define resolved-path (build-path current-dir module-path))
  
  (cond
    [(file-exists? resolved-path) (path->string resolved-path)]
    [(file-exists? (build-path root-path module-path)) 
     (path->string (build-path root-path module-path))]
    [else #f]))

;; Categorize file by architectural layer
(define (categorize-file-by-layer file-path)
  "Categorize a file by its architectural layer"
  (cond
    [(string-contains? file-path "core/") 'core]
    [(string-contains? file-path "class/domain/DomainPortAPI") 'domain-api]
    [(string-contains? file-path "class/domain/") 'domain-ports]
    [(string-contains? file-path "tests/layers/core/") 'test-core]
    [(string-contains? file-path "tests/layers/domain-api/") 'test-domain-api]
    [(string-contains? file-path "tests/layers/domain-ports/") 'test-domain-ports]
    [(string-contains? file-path "tests/layers/integration/") 'test-integration]
    [(string-contains? file-path "tests/layers/") 'test-utilities]
    [(string-contains? file-path "class/") 'class]
    [(string-contains? file-path "tooling/") 'tooling]
    [else 'root]))

;; Generate dependency report
(define (generate-dependency-report graph output-file)
  "Generate a comprehensive dependency analysis report"
  (define out (open-output-file output-file #:exists 'replace))
  
  (fprintf out "# CLEAN v10 Dependency Analysis Report\n\n")
  (fprintf out "Generated: ~a\n\n" (date->string (current-date)))
  
  ;; Basic statistics
  (fprintf out "## Basic Statistics\n\n")
  (fprintf out "- Total files: ~a\n" (hash-count graph))
  (fprintf out "- Total dependencies: ~a\n" 
            (for/sum ([file (hash-keys graph)])
              (set-count (hash-ref graph file))))
  
  ;; Layer analysis
  (fprintf out "\n## Layer Analysis\n\n")
  (define layer-counts (make-hash))
  
  (for ([file (hash-keys graph)])
    (define layer (categorize-file-by-layer file))
    (hash-set! layer-counts layer (add1 (hash-ref layer-counts layer 0))))
  
  (for ([(layer count) layer-counts])
    (fprintf out "### ~a Layer: ~a files\n" (symbol->string layer) count))
  
  ;; File-by-file dependencies
  (fprintf out "\n## File Dependencies\n\n")
  (for ([file (sort (hash-keys graph) string<?)])
    (define deps (hash-ref graph file))
    (define short-name (path->string (file-name-from-path file)))
    (fprintf out "### ~a\n" short-name)
    (fprintf out "**Layer:** ~a\n" (symbol->string (categorize-file-by-layer file)))
    (if (set-empty? deps)
        (fprintf out "No dependencies\n\n")
        (begin
          (fprintf out "Dependencies (~a):\n" (set-count deps))
          (for ([dep (set->list deps)])
            (define dep-short (path->string (file-name-from-path dep)))
            (fprintf out "- ~a (~a)\n" dep-short (symbol->string (categorize-file-by-layer dep))))
          (fprintf out "\n"))))
  
  (close-output-port out))

;; Find circular dependencies (simplified)
(define (find-circular-dependencies graph)
  "Find circular dependencies in the dependency graph"
  (define cycles '())
  
  ;; Simple cycle detection - check if A depends on B and B depends on A
  (for ([file-a (hash-keys graph)])
    (define deps-a (hash-ref graph file-a))
    (for ([file-b (set->list deps-a)])
      (define deps-b (hash-ref graph file-b))
      (when (set-member? deps-b file-a)
        (set! cycles (cons (list file-a file-b) cycles)))))
  
  cycles)

;; Main analysis function
(define (analyze-dependencies root-path)
  "Perform comprehensive dependency analysis"
  (displayln "=== CLEAN v10 Dependency Analysis ===")
  (displayln "")
  
  (displayln "1. Building dependency graph...")
  (define graph (build-dependency-graph root-path))
  (displayln (format "   Found ~a files" (hash-count graph)))
  
  (displayln "2. Detecting circular dependencies...")
  (define cycles (find-circular-dependencies graph))
  (displayln (format "   Found ~a circular dependencies" (length cycles)))
  
  (displayln "3. Generating report...")
  (generate-dependency-report graph "dependency-analysis-report.md")
  (displayln "   Report generated: dependency-analysis-report.md")
  
  (displayln "")
  (displayln "=== Analysis Complete ===")
  
  (list graph cycles))

;; Utility function
(define (file-name-from-path path)
  "Extract file name from path"
  (define path-obj (string->path path))
  (path->string (file-name-from-path path-obj)))

;; Main execution
(module+ main
  (analyze-dependencies "."))
