#!/bin/csh
set -e
set HOST="lt-examples/tiny-host.rkt"
echo "[agda] generating..."
racket -l- -- "lt-core/m2t/gen.rkt" --target agda --host $HOST --out targets/agda/build
ls -1 targets/agda/build/*.agda



