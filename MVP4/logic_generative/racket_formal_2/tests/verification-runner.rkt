#lang racket
;; Lux verification runner
;;
;; Flags:
;;  --json          Emit JSON summary
;;  --strict        Exit non-zero on any failure
;;  --heavy-scan    Run heavyweight checks one-by-one with timeouts
;;  --timeout <n>   Per-check timeout (seconds; default 60)
;;
;; Env:
;;  LUX_SUMMARY_HEAVY=1  Include heavy checks in summary mode
;;  LUX_VERBOSE=1        Enable optional prints inside evidence modules

(require racket/cmdline
         racket/format
         racket/list
         json
         (file "../src/verification/verify.rkt"))

(define as-json? #f)
(define strict? #f)
(define heavy-scan? #f)
(define per-timeout 60)
(command-line
  #:program "verification-runner"
  #:once-each
  ["--json" "Emit JSON summary" (set! as-json? #t)]
  ["--strict" "Exit non-zero on any failure" (set! strict? #t)]
  ["--heavy-scan" "Run heavy checks one-by-one with timeouts" (set! heavy-scan? #t)]
  ["--timeout" secs "Per-check timeout seconds (default 60)"
   (set! per-timeout (string->number secs))])

;; Run a thunk with a timeout (seconds). Returns a pair (status . elapsed)
;; status ∈ 'ok | 'fail | 'timeout
(define (run-with-timeout thunk timeout-secs)
  (define cust (make-custodian))
  (define start (current-inexact-milliseconds))
  (define result (box 'fail))
  (define th (parameterize ([current-custodian cust])
               (thread (λ ()
                         (with-handlers ([exn:fail? (λ (_) (set-box! result 'fail))])
                           (define v (thunk))
                           (set-box! result (if v 'ok 'fail)))))))
  (define done (sync/timeout timeout-secs (thread-dead-evt th)))
  (define elapsed (/ (- (current-inexact-milliseconds) start) 1000.0))
  (cond
    [done (custodian-shutdown-all cust)
          (cons (unbox result) elapsed)]
    [else (begin (kill-thread th)
                 (custodian-shutdown-all cust)
                 (cons 'timeout elapsed))]))

;; Heavy-scan mode: iterate verify:heavy-checks
(define (run-heavy-scan)
  (displayln (format "=== Lux heavy-check scan (timeout ~a s) ===" per-timeout))
  (define failures 0)
  (for ([kv (in-list (heavy-checks))])
    (define name (car kv))
    (define thunk (cdr kv))
    (define res (run-with-timeout thunk per-timeout))
    (define status (car res))
    (define secs (cdr res))
    (displayln (format "~a: ~a (~a s)" name status (~r secs #:precision 2)))
    (when (or (eq? status 'fail) (eq? status 'timeout))
      (displayln (format "Stopping at ~a due to ~a" name status))
      (exit 1)))
  (newline)
  (displayln (format "heavy-scan failures: ~a" failures))
  (= failures 0))


(define results (if heavy-scan?
                    '()
                    (verify-summary)))
(define ok? (if heavy-scan?
               (run-heavy-scan)
               (andmap cdr results)))

(define (print-human)
  (displayln "=== Lux verification runner (summary) ===")
  (for ([kv results])
    (define name (symbol->string (car kv)))
    (define pass (if (cdr kv) "ok" "fail"))
    (displayln (format "~a: ~a" name pass)))
  (newline)
  (displayln "--- gap report ---")
  (define (get n) (cdr (assoc n results)))
  (displayln (format "contraction: ~a" (if (get 'gap-contraction) "ok" "fail")))
  (displayln (format "DNF idempotence: ~a" (if (get 'dnf-idempotent) "ok" "fail")))
  (displayln (format "DNF transport invariance: ~a" (if (get 'dnf-transport-invariant) "ok" "fail"))))
  (newline)
  (displayln "=== Gap propagation (by port) ===")
  (let ([gp (gap-propagation-snapshot)])
    (for ([kv gp])
      (define port (car kv))
      (define items (map car (cdr kv)))
      (displayln (format "~a: ~a" port items)))))

(define (print-json)
  (define j (make-hash))
  (hash-set! j 'ok ok?)
  (hash-set! j 'results (for/list ([kv results])
                          (hash 'name (symbol->string (car kv))
                                'ok (cdr kv))))
  (hash-set! j 'gap (hash 'contraction (cdr (assoc 'gap-contraction results))
                          'dnf-idempotent (cdr (assoc 'dnf-idempotent results))
                          'dnf-transport-invariant (cdr (assoc 'dnf-transport-invariant results))))
  (displayln (jsexpr->string j)))

(if heavy-scan?
    (void)
    (if as-json? (print-json) (print-human)))
(exit (if strict?
          (if ok? 0 1)
          0))
