$(
Cross-check suite auto-generated alongside TranspiledAxioms.mm
$)

$[ BootstrapPaperFoundation.mm $]
$[ TranspiledAxioms.mm $]

$( ==================== Class Layer Checks ==================== $)
GreenKernel-check $p |- class GreenKernel $=
  GreenKernel-def $.

GreenBoundary-check $p |- class GreenBoundary $=
  GreenBoundary-def $.

GreenPropagator-check $p |- class GreenPropagator $=
  GreenPropagator-def $.

GreenRenormalizer-check $p |- class GreenRenormalizer $=
  GreenRenormalizer-def $.

$( ==================== Set Layer Checks ==================== $)
PortBundle-check $p |- set PortBundle $=
  PortBundle-def $.

EdgeBundle-check $p |- set EdgeBundle $=
  EdgeBundle-def $.

TypedSlots-check $p |- set TypedSlots $=
  TypedSlots-def $.

ModuliLattice-check $p |- set ModuliLattice $=
  ModuliLattice-def $.

$( ==================== Syntax Checks ==================== $)
TruthTop-wff-check $p wff TruthTop $=
  TruthTop-wff $.

TruthBottom-wff-check $p wff TruthBottom $=
  TruthBottom-wff $.

TruthJoin-wff-check $p wff ( TruthJoin ph ps ) $=
  TruthJoin-wff $.

TruthMeet-wff-check $p wff ( TruthMeet ph ps ) $=
  TruthMeet-wff $.

TruthNeg-wff-check $p wff ( TruthNeg ph ) $=
  TruthNeg-wff $.

TruthImp-wff-check $p wff ( TruthImp ph ps ) $=
  TruthImp-wff $.

$( ==================== Boolean Axiom Checks ==================== $)
TruthTop-axiom-check $p |- ( TruthImp ph ( TruthJoin ph TruthTop ) ) $=
  TruthTop-axiom $.

TruthBottom-axiom-check $p |- ( TruthImp ( TruthMeet ph TruthBottom ) TruthBottom ) $=
  TruthBottom-axiom $.

TruthMerge-axiom-check $p |- ( TruthImp ( TruthMeet ph ps ) ( TruthMeet ps ph ) ) $=
  TruthMerge-axiom $.

TruthSplit-axiom-check $p |- ( TruthImp ( TruthImp ph ps ) ( TruthImp ( TruthNeg ps ) ( TruthNeg ph ) ) ) $=
  TruthSplit-axiom $.

