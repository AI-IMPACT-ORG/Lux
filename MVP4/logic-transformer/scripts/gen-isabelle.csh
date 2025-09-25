#!/bin/csh
set -e
set HOST="lt-examples/tiny-host.rkt"
echo "[isabelle] generating..."
racket -l- -- "lt-core/m2t/gen.rkt" --target isabelle --host $HOST --out targets/isabelle/build
ls -1 targets/isabelle/build/*.thy



