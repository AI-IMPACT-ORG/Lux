$(
Auto-generated from lt-core/host-bundle
Ports (3): {input, output, port}
Edge kinds (3): {sigma6, tensor, wire}
Sigma6 arity: (3, 3)
$)

$[ BootstrapPaperFoundation.mm $]

$( ==================== Class Layer : Green's Function ==================== $)
$c GreenKernel GreenBoundary GreenPropagator GreenRenormalizer $.
GreenKernel-def $a |- class GreenKernel $.
GreenBoundary-def $a |- class GreenBoundary $.
GreenPropagator-def $a |- class GreenPropagator $.
GreenRenormalizer-def $a |- class GreenRenormalizer $.

$( ==================== Set Layer : Typed Structures ==================== $)
$c PortBundle EdgeBundle TypedSlots ModuliLattice $.
$( Derived from ports {input, output, port} $)
PortBundle-def $a |- set PortBundle $.
$( Derived from edge kinds {sigma6, tensor, wire} $)
EdgeBundle-def $a |- set EdgeBundle $.
$( Slots per sigma6: 3 inbound, 3 outbound $)
TypedSlots-def $a |- set TypedSlots $.
ModuliLattice-def $a |- set ModuliLattice $.

$( Syntax for Boolean/Digital layer $)
$c TruthTop TruthBottom TruthJoin TruthMeet TruthNeg TruthImp $.
TruthTop-wff $a wff TruthTop $.
TruthBottom-wff $a wff TruthBottom $.
TruthJoin-wff $a wff ( TruthJoin ph ps ) $.
TruthMeet-wff $a wff ( TruthMeet ph ps ) $.
TruthNeg-wff $a wff ( TruthNeg ph ) $.
TruthImp-wff $a wff ( TruthImp ph ps ) $.

$( ==================== WFF Layer : Boolean / Digital Core ==================== $)
TruthTop-axiom $a |- ( TruthImp ph ( TruthJoin ph TruthTop ) ) $.
TruthBottom-axiom $a |- ( TruthImp ( TruthMeet ph TruthBottom ) TruthBottom ) $.
TruthMerge-axiom $a |- ( TruthImp ( TruthMeet ph ps ) ( TruthMeet ps ph ) ) $.
TruthSplit-axiom $a |- ( TruthImp ( TruthImp ph ps ) ( TruthImp ( TruthNeg ps ) ( TruthNeg ph ) ) ) $.
