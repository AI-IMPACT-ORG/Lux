# lux language

`lux` is the language front-end name for the CLEAN V2/V10 foundational system.

- Reader: `lux/lang/reader.rkt` implements `#lang lux` and injects the unified API from `racket_formal_2/src/main.rkt`.
- Usage example:

```
#lang lux

(define t (semiring-element 2 B))
(define nf (NF-B t))
(displayln nf)
```

During the transition, the implementation delegates to `racket_formal/src/*` while `racket_formal_2` introduces a clearer architecture.

