# Archived Old Test Files

**Archive Date**: 2025-01-01 14:37:36
**Reason**: Migration to new layered test architecture

## Archived Files

### Root-Level Test Files
- `api-extension-tests.rkt` - API extension tests
- `comprehensive-logic-tests.rkt` - Comprehensive logic tests  
- `institutional-tests.rkt` - Institution theory tests
- `subinstitution-tests.rkt` - Subinstitution tests

### Clean Module Test Files
- `clean/comprehensive-tests-v10.rkt` - CLEAN v10 comprehensive tests
- `clean/comprehensive-tests.rkt` - General comprehensive tests

### Class Module Test Files
- `clean/class/domain/unified-port-tests.rkt` - Unified port tests
- `clean/class/tests/unified-test-framework.rkt` - Unified test framework

### Core Module Test Files
- `clean/core/tests/debug-tests.rkt` - Debug tests
- `clean/core/tests/rg-blocking-tests.rkt` - RG blocking tests

## Migration Notes

These files have been replaced by the new layered test architecture located in:
- `clean/tests/layers/core/core-layer-tests.rkt`
- `clean/tests/layers/domain-api/domain-api-layer-tests.rkt`
- `clean/tests/layers/domain-ports/domain-ports-layer-tests.rkt`
- `clean/tests/layers/integration/integration-layer-tests.rkt`
- `clean/tests/layers/layered-test-runner.rkt`
- `clean/tests/layers/strengthened-test-demo.rkt`
- `clean/tests/layers/test-utilities.rkt`

## Recovery

If you need to restore any of these files, they can be moved back from this archive directory.

## Status

All old test files have been successfully archived and the new layered test architecture is fully functional.
