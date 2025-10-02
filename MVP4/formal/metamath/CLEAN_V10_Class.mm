$[ CLEAN_V10_Framework.mm $]

thm-nfphase-bulk $p |- nfPhase ( normalForm bulkTerm ) = 2 $= ax-nfphase-bulk $.
thm-nfscale-bulk $p |- nfScale ( normalForm bulkTerm ) = 1 $= ax-nfscale-bulk $.
thm-reconstitute-left $p |- observerValue ( reconstitute bulkTerm ) L = bulkLeft $= ax-reconstitute-left $.
thm-residual-left $p |- observerValue ( residualTerm bulkTerm ) L = zeroL $= ax-residual-left $.
thm-triality-phase $p |- nfPhase ( normalForm ( trialitySum bulkLeft bulkRight ) ) = phase bulkLeft + phase bulkRight $= ax-triality-phase $.
thm-valueG-bulk $p |- valueG obs0 0 = bulk_core $= ax-valueG-bulk $.
thm-valueCov $p |- valueCov obs0 0 1 = ( mkCov bulk_0 probe_1 ) $= ax-valueCov $.
thm-gen-phase $p |- nfPhase ( normalForm ( generatingFunctional obsGen sourceList01 ) ) = 1.0 $= ax-gen-phase $.
thm-gen-scale $p |- nfScale ( normalForm ( generatingFunctional obsGen sourceList01 ) ) = 2.0 $= ax-gen-scale $.
thm-moduli-phase $p |- nfPhase ( applyHeaderFlow moduliExample bulkTerm ) = 2 $= ax-moduli-phase $.
thm-hist-phase $p |- nfPhase ( normalForm ( sumOverHistories hist0 ) ) = phase bulkTerm + phase bulkLeft + phase bulkRight $= ax-hist-phase $.
thm-guarded $p |- guardedNegation 1 0 = 1 $= ax-guarded $.
thm-nand $p |- nandTerm 1 1 1 = 0 $= ax-nand $.
thm-psdm $p |- psdmLookup psdm0 keyX = 42 $= ax-psdm $.
thm-boolean $p |- booleanPortEval booleanPort bulkTerm = 1 $= ax-boolean $.
thm-lambda $p |- lambdaNormalise lambdaPort bulkTerm = bulk_core $= ax-lambda $.
thm-infoflow $p |- flowPhase ( infoflowFlux infoPort bulkTerm ) = phase bulkTerm $= ax-infoflow $.
thm-qft-ordering $p |- propOrdering ( qftPropagator qftPort bulkTerm ) = time_ordered $= ax-qft-ordering $.
thm-umbral $p |- umbralCommutesWithNF bulkTerm = true $= ax-umbral $.
thm-check-umbral $p |- checkUmbral = true $= ax-check-umbral $.
