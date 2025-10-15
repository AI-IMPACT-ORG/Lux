$(
  clean/app/classification.mm - Classification bridge stubs
  ---------------------------------------------------------
  Provides lightweight assumptions for higher-level classification files
  to request the renormalisation semiring adapters without importing the
  core module directly.
$)

$[ ../core/renormalisation.mm $]

$c ClassBulkContext ClassPhaseContext ClassGuardContext $.

wClassBulkContext $a wff ClassBulkContext $.
wClassPhaseContext $a wff ClassPhaseContext $.
wClassGuardContext $a wff ClassGuardContext $.

class-bulk-assume $a |- ( ClassBulkContext -> BulkSemiring ) $.
class-phase-assume $a |- ( ClassPhaseContext -> PhaseSemiring ) $.
class-guard-assume $a |- ( ClassGuardContext -> GuardSemiring ) $.

