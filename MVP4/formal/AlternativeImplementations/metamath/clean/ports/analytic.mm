$(
  clean/ports/analytic.mm - Analytic bridge stubs
  ------------------------------------------------
  These hypotheses expose the renormalisation adapters to analytic port
  developments without coupling them directly to the core renormalisation
  module.
$)

$[ ../core/renormalisation.mm $]

$c AnalyticBulkContext AnalyticPhaseContext AnalyticGuardContext $.

wAnalyticBulkContext $a wff AnalyticBulkContext $.
wAnalyticPhaseContext $a wff AnalyticPhaseContext $.
wAnalyticGuardContext $a wff AnalyticGuardContext $.

analytic-bulk-assume $a |- ( AnalyticBulkContext -> BulkSemiring ) $.
analytic-phase-assume $a |- ( AnalyticPhaseContext -> PhaseSemiring ) $.
analytic-guard-assume $a |- ( AnalyticGuardContext -> GuardSemiring ) $.

