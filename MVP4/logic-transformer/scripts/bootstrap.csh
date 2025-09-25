#!/bin/csh
set -e
echo "[bootstrap] installing racket packages..."
raco pkg install --auto --skip-installed scribble typed-racket rackunit
echo "[bootstrap] building core..."
raco make lt-core/main.rkt
echo "[bootstrap] ok"



