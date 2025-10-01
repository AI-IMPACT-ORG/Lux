#lang racket

(require "coq.rkt")

(provide generate-coq-library)

;; Generate the complete Coq library using layered architecture
(define (generate-coq-library [output-dir "coq-output"])
  (displayln "🚀 Generating CLEAN v10 Coq Library with Layered Architecture...")
  (displayln "")
  
  ;; Generate the complete library using the new layered architecture
  (emit-coq-library output-dir)
  
  (displayln "")
  (displayln "✅ CLEAN v10 Coq Library generated successfully!")
  (displayln (format "📁 Output directory: ~a" output-dir))
  (displayln "")
  (displayln "🎯 Architecture Features:")
  (displayln "  • Clean layered architecture with internal lib/ and external api/")
  (displayln "  • Central API gatekeeper preventing symbol conflicts")
  (displayln "  • CLEAN_ prefixed symbols for clear namespace")
  (displayln "  • Internal modules not exported directly")
  (displayln "  • Clean separation of concerns")
  (displayln "")
  (displayln "🔧 To compile:")
  (displayln (format "  cd ~a && coqc lib/Core.v" output-dir))
  (displayln (format "  cd ~a && coqc lib/Observers.v" output-dir))
  (displayln (format "  cd ~a && coqc lib/Triality.v" output-dir))
  (displayln (format "  cd ~a && coqc lib/GuardedNegation.v" output-dir))
  (displayln (format "  cd ~a && coqc lib/DomainMaps.v" output-dir))
  (displayln (format "  cd ~a && coqc api/CLEAN.v" output-dir))
  (displayln (format "  cd ~a && coqc CLEAN.v" output-dir)))

;; Main execution
(module+ main
  (generate-coq-library))