#!/bin/csh
set -e
echo "[test] running unit tests..."
raco test -x lt-tests
echo "[test] ok"



