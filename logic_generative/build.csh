#!/bin/csh

# @logic/gen Build and Test Script
# Provides commands for building, testing, and running the generator language

set SCRIPT_DIR = `dirname $0`
set LOGIC_GEN_DIR = "$SCRIPT_DIR"

echo "=== @logic/gen Build and Test Script ==="
echo "Logic Gen Directory: $LOGIC_GEN_DIR"

# Function to run tests
alias run-tests 'cd $LOGIC_GEN_DIR && raco test tests/test-suite.rkt'

# Function to run tests with verbose output
alias run-tests-verbose 'cd $LOGIC_GEN_DIR && raco test tests/test-suite.rkt --verbosity high'

# Function to run examples
alias run-examples 'cd $LOGIC_GEN_DIR && raco test examples/'

# Function to install package
alias install-pkg 'cd $LOGIC_GEN_DIR && raco pkg install --auto .'

# Function to uninstall package
alias uninstall-pkg 'raco pkg remove logic-gen'

# Function to build documentation
alias build-docs 'cd $LOGIC_GEN_DIR && raco setup --doc logic-gen'

# Function to clean build artifacts
alias clean-build 'cd $LOGIC_GEN_DIR && raco setup --clean logic-gen'

# Function to run REPL
alias run-repl 'cd $LOGIC_GEN_DIR && racket -I logic-gen'

# Function to run demo
alias run-demo 'cd $LOGIC_GEN_DIR && racket examples/demo.gen'

# Function to check syntax
alias check-syntax 'cd $LOGIC_GEN_DIR && raco setup --check-pkg-deps logic-gen'

# Function to show package info
alias show-info 'cd $LOGIC_GEN_DIR && raco pkg show logic-gen'

# Main command dispatcher
if ($#argv == 0) then
    echo "Usage: $0 <command>"
    echo ""
    echo "Available commands:"
    echo "  test           - Run test suite"
    echo "  test-verbose    - Run test suite with verbose output"
    echo "  examples       - Run examples"
    echo "  install        - Install package"
    echo "  uninstall      - Uninstall package"
    echo "  docs           - Build documentation"
    echo "  clean          - Clean build artifacts"
    echo "  repl           - Start REPL"
    echo "  demo           - Run demo example"
    echo "  check          - Check syntax and dependencies"
    echo "  info           - Show package information"
    echo ""
    echo "Examples:"
    echo "  $0 test        - Run all tests"
    echo "  $0 install     - Install the package"
    echo "  $0 demo        - Run the demo"
    exit 1
endif

switch ($1)
case "test":
    run-tests
    breaksw
case "test-verbose":
    run-tests-verbose
    breaksw
case "examples":
    run-examples
    breaksw
case "install":
    install-pkg
    breaksw
case "uninstall":
    uninstall-pkg
    breaksw
case "docs":
    build-docs
    breaksw
case "clean":
    clean-build
    breaksw
case "repl":
    run-repl
    breaksw
case "demo":
    run-demo
    breaksw
case "check":
    check-syntax
    breaksw
case "info":
    show-info
    breaksw
default:
    echo "Unknown command: $1"
    echo "Run '$0' without arguments to see available commands"
    exit 1
    breaksw
endsw

