;; CORRECTED Green's sum: G_N = I_B ⊕_B K ⊕_B K² ⊕_B ... ⊕_B K^N
(define (greens-sum kernel N)
  (unless (and (integer? N) (>= N 0))
    (error 'greens-sum "N must be non-negative integer, got ~a" N))
  (cond
    [(= N 0) (identity-kernel)]
    [(= N 1) kernel]
    [else
     ;; G_N = I + K + K² + ... + K^N
     ;; Compute sum by accumulating powers correctly
     (let-values ([(result current)
                   (for/fold ([result (identity-kernel)]
                              [current kernel])
                             ([i (in-range N)])
                     (values (kernel-compose result current)
                             (kernel-compose current kernel)))])
       result)]))
