# Archived Outdated Files

**Archive Date**: 2025-01-01 14:40:02
**Reason**: Cleanup of outdated and duplicate files after test harness strengthening

## Archived Files

### Duplicate API Files
- `api-minimal.rkt` - Duplicate of `api.rkt` with minor differences

### Outdated Kernel Files
- `clean/core/kernel-backup.rkt` - Backup version of kernel.rkt (outdated)
- `clean/core/kernel-corrected.rkt` - Corrected version of kernel.rkt (outdated)

### Legacy Individual Domain Port Files
- `clean/class/domain/boolean-logic/` - Legacy boolean logic domain port
- `clean/class/domain/lambda-calculus/` - Legacy lambda calculus domain port  
- `clean/class/domain/qft/` - Legacy quantum field theory domain port
- `clean/class/domain/infoflow/` - Legacy information flow domain port
- `clean/class/domain/analytic-number-theory/` - Legacy analytic number theory port
- `clean/class/domain/computational-complexity/` - Legacy computational complexity port
- `clean/class/domain/formal-mathematics/` - Legacy formal mathematics port
- `clean/class/domain/operating-systems/` - Legacy operating systems port

## Migration Notes

These files have been superseded by:

### Current Active Files
- `api.rkt` - Main API file (kept, not the minimal version)
- `clean/core/kernel.rkt` - Current active kernel implementation
- `clean/class/domain/unified-port.rkt` - Unified domain port implementation
- `clean/class/domain/DomainPortAPI.rkt` - Clean interface layer
- `clean/tests/layers/` - New layered test architecture

### Why These Files Were Archived

1. **Duplicate Files**: `api-minimal.rkt` was a duplicate of `api.rkt`
2. **Outdated Versions**: Kernel backup/corrected files were superseded by current `kernel.rkt`
3. **Legacy Domain Ports**: Individual domain port files were not being used and superseded by `unified-port.rkt`
4. **No Dependencies**: None of these files were imported or used by active code

## Recovery

If you need to restore any of these files:

```bash
# Restore a specific file
mv archive/outdated-files-20251001_144002/filename clean/path/

# Restore all files
mv archive/outdated-files-20251001_144002/* clean/path/
```

## Status

All outdated files have been successfully archived. The codebase now contains only active, current files with no duplicates or legacy code.
