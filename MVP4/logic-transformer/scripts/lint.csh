#!/bin/csh
set -e
echo "[lint] racket fmt (check only)"
raco fmt --check lt-core lt-examples lt-tests lt-docs
echo "[lint] ok"



