$(
Version: CLEAN v10 CLASS
Signature sorts: L, B, R, I
Operations: _B : (B B -> B); _B : (B B -> B); __L : (L L -> L); __R : (R R -> R); __L : (L -> B); __R : (R -> B); __L : (B -> L); __R : (B -> R); ad_0 : (B -> B); ad_1 : (B -> B); ad_2 : (B -> B); ad_3 : (B -> B); starB : (B -> B); starL : (L -> L); starR : (R -> R)
Constants: 0_B : B; 1_B : B; 0_L : L; 1_L : L; 0_R : R; 1_R : R; _ : B; bar_ : B; z : B; barz : B; _ : B; Gen4 : (B B B B -> B)
Quotient mask: phase
R-matrix: identity
Moduli snapshot: _L=0 _L=0 _R=0 _R=0 z=1 barz=1
Sample term: spec#:_ with header (phase 1, scale 1)
NF(core): phase 1, scale 1, core Gen4
NF_(core): phase 1, scale 1, core Gen4
$)
$c ( ) + 0 0.0 1 1.0 2 2.0 3 42 = InfoflowPort L LambdaPort agnostic applyHeaderFlow booleanPort booleanPortEval bulkLeft bulkRight bulkTerm bulk_0 bulk_0_l bulk_0_r bulk_core checkUmbral emptyObservables emptyPSDM flowPhase g0 g1 genTerm0 genTerm1 gen_0 gen_1 generatingFunctional guardedNegation hist0 histPair infoPort infoflowFlux insertObs keyX l_boundary lambdaNormalise lambdaPort mkBooleanPort mkCov mkModuli mkTerm moduliExample nandTerm nfPhase nfScale normalForm obs0 obsGen observerValue phase probeTerm probe_1 probe_core propOrdering psdm0 psdmDefine psdmLookup qftPort qftPortCtor qftPropagator r_boundary reconstitute residualTerm sourceList sourceList01 sumOverHistories time_ordered trialitySum true umbralCommutesWithNF valueCov valueG zeroL |- $.
ax-def-bulkTerm $a |- bulkTerm = ( mkTerm bulk_0 2 1 bulk_core ) $.
ax-def-bulkLeft $a |- bulkLeft = ( mkTerm bulk_0_l 2 0.0 l_boundary ) $.
ax-def-bulkRight $a |- bulkRight = ( mkTerm bulk_0_r 0.0 1 r_boundary ) $.
ax-def-probeTerm $a |- probeTerm = ( mkTerm probe_1 0 3 probe_core ) $.
ax-def-genTerm0 $a |- genTerm0 = ( mkTerm gen_0 1 0 g0 ) $.
ax-def-genTerm1 $a |- genTerm1 = ( mkTerm gen_1 0 2 g1 ) $.
ax-def-obs0 $a |- obs0 = ( insertObs ( insertObs emptyObservables 0 bulkTerm ) 1 probeTerm ) $.
ax-def-obsGen $a |- obsGen = ( insertObs ( insertObs emptyObservables 0 genTerm0 ) 1 genTerm1 ) $.
ax-def-sourceList $a |- sourceList01 = ( sourceList 0 1 ) $.
ax-def-moduli $a |- moduliExample = ( mkModuli 1 0 0 2 1 1 ) $.
ax-def-hist0 $a |- hist0 = ( histPair bulkTerm bulkLeft bulkRight ) $.
ax-def-psdm0 $a |- psdm0 = ( psdmDefine emptyPSDM keyX 42 ) $.
ax-def-booleanPort $a |- booleanPort = ( mkBooleanPort 0 ) $.
ax-def-lambdaPort $a |- lambdaPort = LambdaPort $.
ax-def-infoPort $a |- infoPort = InfoflowPort $.
ax-def-qftPort $a |- qftPort = ( qftPortCtor agnostic time_ordered ) $.
ax-nfphase-bulk $a |- nfPhase ( normalForm bulkTerm ) = 2 $.
ax-nfscale-bulk $a |- nfScale ( normalForm bulkTerm ) = 1 $.
ax-reconstitute-left $a |- observerValue ( reconstitute bulkTerm ) L = bulkLeft $.
ax-residual-left $a |- observerValue ( residualTerm bulkTerm ) L = zeroL $.
ax-triality-phase $a |- nfPhase ( normalForm ( trialitySum bulkLeft bulkRight ) ) = phase bulkLeft + phase bulkRight $.
ax-valueG-bulk $a |- valueG obs0 0 = bulk_core $.
ax-valueCov $a |- valueCov obs0 0 1 = ( mkCov bulk_0 probe_1 ) $.
ax-gen-phase $a |- nfPhase ( normalForm ( generatingFunctional obsGen sourceList01 ) ) = 1.0 $.
ax-gen-scale $a |- nfScale ( normalForm ( generatingFunctional obsGen sourceList01 ) ) = 2.0 $.
ax-moduli-phase $a |- nfPhase ( applyHeaderFlow moduliExample bulkTerm ) = 2 $.
ax-hist-phase $a |- nfPhase ( normalForm ( sumOverHistories hist0 ) ) = phase bulkTerm + phase bulkLeft + phase bulkRight $.
ax-guarded $a |- guardedNegation 1 0 = 1 $.
ax-nand $a |- nandTerm 1 1 1 = 0 $.
ax-psdm $a |- psdmLookup psdm0 keyX = 42 $.
ax-boolean $a |- booleanPortEval booleanPort bulkTerm = 1 $.
ax-lambda $a |- lambdaNormalise lambdaPort bulkTerm = bulk_core $.
ax-infoflow $a |- flowPhase ( infoflowFlux infoPort bulkTerm ) = phase bulkTerm $.
ax-qft-ordering $a |- propOrdering ( qftPropagator qftPort bulkTerm ) = time_ordered $.
ax-umbral $a |- umbralCommutesWithNF bulkTerm = true $.
ax-check-umbral $a |- checkUmbral = true $.
