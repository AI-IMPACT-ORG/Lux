#!/bin/csh

# Logic Transformer Coq Library Generator
# Generates a ready-to-use Coq library with R_ prefix

set HOST="lt-examples/transformer-host.rkt"
set OUT="targets/coq-library"

echo "[coq-library] generating ready-to-use Coq library..."

# Create output directory
mkdir -p $OUT

# Generate the library
racket lt-core/m2t/gen-library.rkt coq $HOST $OUT

echo "[coq-library] ready-to-use Coq library generated in $OUT/"
echo ""
echo "To use the library:"
echo "1. cd $OUT"
echo "2. coqc R_LogicTransformer.v"
echo "3. In your Coq file: Require Import LogicTransformer."
echo ""
echo "Files generated:"
ls -la $OUT/R_*.v $OUT/R_*.md $OUT/_CoqProject

