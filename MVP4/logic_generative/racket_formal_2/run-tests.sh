#!/usr/bin/env bash
# (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.
set -euo pipefail

cd "$(dirname "$0")"/tests

echo "Running CLEAN test suite (compat)..."
racket -e '(require "clean-test-suite.rkt") (run-clean-test-suite)'

echo "Running spec-aligned comprehensive suite (compat)..."
racket -e '(require "spec-aligned-comprehensive-tests.rkt") (run-spec-aligned-comprehensive-test-suite)'

echo "Running Lux verification runner..."
racket -e '(require "verification-runner.rkt")'

echo "Running proofs integration (side-car) ..."
racket -e '(require "proofs-integration.rkt") (run-proofs-integration)'

echo "Done."
