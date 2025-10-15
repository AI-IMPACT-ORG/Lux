#lang racket

;; CLEAN v10 Dependency Analysis Tool
;; Analyzes module dependencies, creates dependency graphs, and identifies architectural patterns

(require racket/file
         racket/path
         racket/string
         racket/list
         racket/set
         racket/graph
         racket/draw)

(provide analyze-dependencies
         create-dependency-graph
         generate-dependency-report
         visualize-dependencies
         find-circular-dependencies
         analyze-layer-dependencies
         generate-dot-graph)

;; ===== DEPENDENCY EXTRACTION =====

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
        ;; Extract module paths from require statement
        (define module-paths (extract-module-paths trimmed))
        (set! requires (append requires module-paths))))
  requires)

;; Extract module paths from a require statement
(define (extract-module-paths require-line)
  "Extract module paths from a require statement"
  (define paths '())
  (define in-quotes #f)
  (define current-path "")
  
  (for ([char (string->list require-line)])
    (case char
      [(#\") (set! in-quotes (not in-quotes))]
      [(#\space #\newline #\tab)
       (when (and (not in-quotes) (not (string-empty? current-path)))
         (when (string-contains? current-path ".rkt")
           (set! paths (cons current-path paths)))
         (set! current-path ""))]
      [else (when in-quotes (set! current-path (string-append current-path (string char))))]))
  
  (when (not (string-empty? current-path))
    (when (string-contains? current-path ".rkt")
      (set! paths (cons current-path paths))))
  
  paths)

;; ===== DEPENDENCY GRAPH CONSTRUCTION =====

;; Build dependency graph from file analysis
(define (build-dependency-graph root-path)
  "Build a dependency graph from all Racket files in the directory"
  (define files (find-racket-files root-path))
  (define graph (make-hash))
  
  ;; Initialize graph with all files
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

;; ===== CIRCULAR DEPENDENCY DETECTION =====

;; Find circular dependencies using DFS
(define (find-circular-dependencies graph)
  "Find circular dependencies in the dependency graph"
  (define visited (make-hash))
  (define recursion-stack (make-hash))
  (define cycles '())
  
  (define (dfs node)
    (hash-set! visited node #t)
    (hash-set! recursion-stack node #t)
    
    (define dependencies (hash-ref graph node))
    (for ([dep dependencies])
      (cond
        [(not (hash-ref visited dep #f))
         (dfs dep)]
        [(hash-ref recursion-stack dep #f)
         (set! cycles (cons (list node dep) cycles))]))
    
    (hash-set! recursion-stack node #f))
  
  (for ([node (hash-keys graph)])
    (when (not (hash-ref visited node #f))
      (dfs node)))
  
  cycles)

;; ===== LAYER ANALYSIS =====

;; Analyze dependencies by architectural layers
(define (analyze-layer-dependencies graph)
  "Analyze dependencies between architectural layers"
  (define layers (make-hash))
  
  ;; Categorize files by layer
  (for ([file (hash-keys graph)])
    (define layer (categorize-file-by-layer file))
    (when (not (hash-has-key? layers layer))
      (hash-set! layers layer (set)))
    (hash-set! layers layer (set-add (hash-ref layers layer) file)))
  
  ;; Analyze inter-layer dependencies
  (define layer-deps (make-hash))
  (for ([layer (hash-keys layers)])
    (hash-set! layer-deps layer (make-hash)))
  
  (for ([file (hash-keys graph)])
    (define file-layer (categorize-file-by-layer file))
    (define dependencies (hash-ref graph file))
    
    (for ([dep dependencies])
      (define dep-layer (categorize-file-by-layer dep))
      (when (not (equal? file-layer dep-layer))
        (define current-deps (hash-ref layer-deps file-layer))
        (hash-set! current-deps dep-layer 
                   (add1 (hash-ref current-deps dep-layer 0))))))
  
  (list layers layer-deps))

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

;; ===== VISUALIZATION =====

;; Generate DOT format for Graphviz
(define (generate-dot-graph graph output-file)
  "Generate DOT format graph for visualization"
  (define out (open-output-file output-file #:exists 'replace))
  
  (fprintf out "digraph CLEAN_v10_Dependencies {\n")
  (fprintf out "  rankdir=TB;\n")
  (fprintf out "  node [shape=box, style=filled];\n")
  (fprintf out "  edge [color=gray];\n\n")
  
  ;; Define node colors by layer
  (fprintf out "  // Node definitions\n")
  (for ([file (hash-keys graph)])
    (define layer (categorize-file-by-layer file))
    (define color (layer-color layer))
    (define short-name (path->string (file-name-from-path file)))
    (fprintf out "  \"~a\" [fillcolor=~a, label=\"~a\"];\n" 
              (string-replace file "\\" "/") color short-name))
  
  (fprintf out "\n  // Dependencies\n")
  (for ([file (hash-keys graph)])
    (define dependencies (hash-ref graph file))
    (for ([dep dependencies])
      (fprintf out "  \"~a\" -> \"~a\";\n" 
                (string-replace file "\\" "/")
                (string-replace dep "\\" "/"))))
  
  (fprintf out "}\n")
  (close-output-port out))

;; Get color for layer
(define (layer-color layer)
  "Get color for a layer"
  (case layer
    [(core) "lightblue"]
    [(domain-api) "lightgreen"]
    [(domain-ports) "lightyellow"]
    [(class) "lightcoral"]
    [(test-core) "lightsteelblue"]
    [(test-domain-api) "lightgreen"]
    [(test-domain-ports) "lightyellow"]
    [(test-integration) "lightpink"]
    [(test-utilities) "lightgray"]
    [(tooling) "lightcyan"]
    [else "white"]))

;; ===== REPORTING =====

;; Generate comprehensive dependency report
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
  (define layer-analysis (analyze-layer-dependencies graph))
  (define layers (car layer-analysis))
  (define layer-deps (cadr layer-analysis))
  
  (for ([layer (hash-keys layers)])
    (fprintf out "### ~a Layer\n" (symbol->string layer))
    (fprintf out "- Files: ~a\n" (set-count (hash-ref layers layer)))
    (fprintf out "- Files: ~a\n\n" 
              (string-join (map path->string (set->list (hash-ref layers layer))) ", "))
    
    ;; Inter-layer dependencies
    (define deps (hash-ref layer-deps layer))
    (when (> (hash-count deps) 0)
      (fprintf out "Dependencies to other layers:\n")
      (for ([(dep-layer count) deps])
        (fprintf out "- ~a: ~a dependencies\n" (symbol->string dep-layer) count))
      (fprintf out "\n")))
  
  ;; Circular dependencies
  (fprintf out "## Circular Dependencies\n\n")
  (define cycles (find-circular-dependencies graph))
  (if (empty? cycles)
      (fprintf out "✅ No circular dependencies found!\n\n")
      (begin
        (fprintf out "⚠️ Found ~a circular dependencies:\n\n" (length cycles))
        (for ([cycle cycles])
          (fprintf out "- ~a → ~a\n" (car cycle) (cadr cycle)))
        (fprintf out "\n")))
  
  ;; File-by-file dependencies
  (fprintf out "## File Dependencies\n\n")
  (for ([file (sort (hash-keys graph) string<?)])
    (define deps (hash-ref graph file))
    (fprintf out "### ~a\n" (path->string (file-name-from-path file)))
    (if (set-empty? deps)
        (fprintf out "No dependencies\n\n")
        (begin
          (fprintf out "Dependencies:\n")
          (for ([dep (set->list deps)])
            (fprintf out "- ~a\n" (path->string (file-name-from-path dep))))
          (fprintf out "\n"))))
  
  (close-output-port out))

;; ===== MAIN ANALYSIS FUNCTION =====

;; Main dependency analysis function
(define (analyze-dependencies root-path)
  "Perform comprehensive dependency analysis"
  (displayln "=== CLEAN v10 Dependency Analysis ===")
  (displayln "")
  
  (displayln "1. Building dependency graph...")
  (define graph (build-dependency-graph root-path))
  (displayln (format "   Found ~a files" (hash-count graph)))
  
  (displayln "2. Analyzing layers...")
  (define layer-analysis (analyze-layer-dependencies graph))
  (displayln "   Layer analysis complete")
  
  (displayln "3. Detecting circular dependencies...")
  (define cycles (find-circular-dependencies graph))
  (displayln (format "   Found ~a circular dependencies" (length cycles)))
  
  (displayln "4. Generating reports...")
  (generate-dependency-report graph "dependency-analysis-report.md")
  (generate-dot-graph graph "dependency-graph.dot")
  (displayln "   Reports generated")
  
  (displayln "")
  (displayln "=== Analysis Complete ===")
  (displayln "Files generated:")
  (displayln "- dependency-analysis-report.md")
  (displayln "- dependency-graph.dot")
  
  (list graph layer-analysis cycles))

;; ===== UTILITY FUNCTIONS =====

;; Get file name from path
(define (file-name-from-path path)
  "Extract file name from path"
  (define path-obj (string->path path))
  (path->string (file-name-from-path path-obj)))

;; Main execution
(module+ main
  (analyze-dependencies "."))
