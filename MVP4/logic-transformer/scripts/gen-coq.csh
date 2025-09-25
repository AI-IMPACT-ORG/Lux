#!/bin/csh
set HOST="lt-examples/transformer-host.rkt"
echo "[coq] generating M3-M2-M1 pyramid..."
mkdir -p targets/coq/build
racket "lt-core/m2t/gen.rkt" --target coq --host $HOST --out targets/coq/build
echo "[coq] generated files:"
ls -1 targets/coq/build/*.v
echo "[coq] M3-M2-M1 pyramid generation complete!"

