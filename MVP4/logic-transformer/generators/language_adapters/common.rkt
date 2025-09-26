#lang typed/racket

(require racket/list
         racket/string
         "../../lt-core/main.rkt"
         "../../lt-core/M123_d/m3d.graph.rkt"
         "../../lt-core/M123_d/m3d.types.rkt")

(provide EdgeSpec EdgeSpec-name EdgeSpec-inputs EdgeSpec-outputs
         EdgeSpec-src EdgeSpec-dst
         SampleSpec SampleSpec-ports SampleSpec-edges SampleSpec-node-count SampleSpec-edge-count
         sample-spec
         default-moduli
         symbol->lower snake->pascal snake->camel
         find-edge-spec)
 
(: string-empty? (-> String Boolean))
(define (string-empty? s)
  (= (string-length s) 0))

(struct EdgeSpec ([name : Symbol]
                  [inputs : Natural]
                  [outputs : Natural]
                  [src : (Listof Symbol)]
                  [dst : (Listof Symbol)]) #:transparent)

(struct SampleSpec ([ports : (Listof Symbol)]
                    [edges : (Listof EdgeSpec)]
                    [node-count : Natural]
                    [edge-count : Natural]) #:transparent)

(: symbol->lower (-> Symbol String))
(define (symbol->lower s)
  (string-downcase (symbol->string s)))

(: sanitize-token (-> Symbol String))
(define (sanitize-token s)
  (string-replace (symbol->string s) "_" "-"))

(: split-token (-> Symbol (Listof String)))
(define (split-token s)
  (let* ([raw (sanitize-token s)]
         [segments (regexp-split #rx"[-]+" raw)]
         [digits (regexp-split #rx"(?<=\\D)(?=\\d)|(?<=\\d)(?=\\D)" (string-join segments "-"))]
        [segments2 (filter (lambda ([x : String]) (not (string-empty? x))) digits)])
    segments2))

(: capitalize (-> String String))
(define (capitalize str)
  (if (string-empty? str)
      str
      (string-append (string-upcase (substring str 0 1))
                     (string-downcase (substring str 1)))))

(: snake->pascal (-> Symbol String))
(define (snake->pascal s)
  (string-join (map capitalize (split-token s)) ""))

(: snake->camel (-> Symbol String))
(define (snake->camel s)
  (match (split-token s)
    ['() ""]
    [(cons first rest)
     (string-append (string-downcase first) (string-join (map capitalize rest) ""))]))

(: edge-spec (-> TypeGraph Symbol EdgeSpec))
(define (edge-spec tg kind)
  (define arity (hash-ref (TypeGraph-arity tg) kind))
  (define src (vector->list (hash-ref (TypeGraph-srcS tg) kind)))
  (define dst (vector->list (hash-ref (TypeGraph-dstS tg) kind)))
  (EdgeSpec kind
            (Arity-m arity)
            (Arity-n arity)
            src
            dst))

(: extract-sample (-> SampleSpec))
(define (extract-sample)
  (define-values (graph _top _rest) (host-bundle))
  (define tg (TGraph-T graph))
  (define ports (sort (hash-keys (TypeGraph-ports tg)) symbol<?))
  (define kinds (sort (hash-keys (TypeGraph-kinds tg)) symbol<?))
  (define edges (map (lambda ([k : Symbol]) (edge-spec tg k)) kinds))
  (SampleSpec ports
              edges
              (hash-count (TGraph-nodes graph))
              (hash-count (TGraph-edges graph))))

(define sample-spec (extract-sample))

(define default-moduli '(1 2 3 4 1 2 3 4 1 1))

(: find-edge-spec (-> (Listof EdgeSpec) Symbol EdgeSpec))
(define (find-edge-spec edges sym)
  (match edges
    ['() (error 'find-edge-spec (format "Edge ~a not found" sym))]
    [(cons edge rest)
     (if (symbol=? (EdgeSpec-name edge) sym)
         edge
         (find-edge-spec rest sym))]))
