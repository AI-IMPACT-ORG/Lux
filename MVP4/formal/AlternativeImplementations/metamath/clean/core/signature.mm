$(
  clean/core/signature.mm - Symbol declarations only
  -------------------------------------------------
  Minimal catalogue of CLEAN generators.  Witness lemmas were removed
  pending full proofs, so downstream files import only the raw `Op`
  statements provided below.
$)

$[ base.mm $]

$c Op Sigma10 IotaL IotaR NuL NuR BulkSum Ad0 Ad1 Ad2 Ad3 GaugePhi GaugePhiBar GaugeZ GaugeZBar GaugeLambda Basepoint0 Basepoint1 Basepoint2 Basepoint3 Gen4 TrialityL TrialityR TrialityB ConjB ConjL ConjR CopyB EraseB TensorL GuardNeg GuardNAND BraidBB DeltaB CumulantB $.

$v op $.

vop $f term op $.
wOp $a wff Op op xs ys $.

cSigma10 $a term Sigma10 $.
cIotaL $a term IotaL $.
cIotaR $a term IotaR $.
cNuL $a term NuL $.
cNuR $a term NuR $.
cBulkSum $a term BulkSum $.
cAd0 $a term Ad0 $.
cAd1 $a term Ad1 $.
cAd2 $a term Ad2 $.
cAd3 $a term Ad3 $.
cGaugePhi $a term GaugePhi $.
cGaugePhiBar $a term GaugePhiBar $.
cGaugeZ $a term GaugeZ $.
cGaugeZBar $a term GaugeZBar $.
cGaugeLambda $a term GaugeLambda $.
cBasepoint0 $a term Basepoint0 $.
cBasepoint1 $a term Basepoint1 $.
cBasepoint2 $a term Basepoint2 $.
cBasepoint3 $a term Basepoint3 $.
cGen4 $a term Gen4 $.
cTrialityL $a term TrialityL $.
cTrialityR $a term TrialityR $.
cTrialityB $a term TrialityB $.
cConjB $a term ConjB $.
cConjL $a term ConjL $.
cConjR $a term ConjR $.
cCopyB $a term CopyB $.
cEraseB $a term EraseB $.
cTensorL $a term TensorL $.
cGuardNeg $a term GuardNeg $.
cGuardNAND $a term GuardNAND $.
cBraidBB $a term BraidBB $.
cDeltaB $a term DeltaB $.
cCumulantB $a term CumulantB $.

$( Generator boundary declarations. $)
ax-op-iotaL $a |- Op IotaL ( VecCons L VecNil ) ( VecCons B VecNil ) $.
ax-op-iotaR $a |- Op IotaR ( VecCons R VecNil ) ( VecCons B VecNil ) $.
ax-op-nuL $a |- Op NuL ( VecCons B VecNil ) ( VecCons L VecNil ) $.
ax-op-nuR $a |- Op NuR ( VecCons B VecNil ) ( VecCons R VecNil ) $.
ax-op-bulksum $a |- Op BulkSum ( VecAppend ( VecCons B VecNil ) ( VecCons B VecNil ) ) ( VecCons B VecNil ) $.
ax-op-ad0 $a |- Op Ad0 ( VecCons B VecNil ) ( VecCons B VecNil ) $.
ax-op-ad1 $a |- Op Ad1 ( VecCons B VecNil ) ( VecCons B VecNil ) $.
ax-op-ad2 $a |- Op Ad2 ( VecCons B VecNil ) ( VecCons B VecNil ) $.
ax-op-ad3 $a |- Op Ad3 ( VecCons B VecNil ) ( VecCons B VecNil ) $.
ax-op-gaugephi $a |- Op GaugePhi ( VecCons I VecNil ) ( VecCons B VecNil ) $.
ax-op-gaugephibar $a |- Op GaugePhiBar ( VecCons I VecNil ) ( VecCons B VecNil ) $.
ax-op-gaugez $a |- Op GaugeZ ( VecCons I VecNil ) ( VecCons B VecNil ) $.
ax-op-gaugezbar $a |- Op GaugeZBar ( VecCons I VecNil ) ( VecCons B VecNil ) $.
ax-op-gaugelambda $a |- Op GaugeLambda ( VecCons I VecNil ) ( VecCons B VecNil ) $.
ax-op-basepoint0 $a |- Op Basepoint0 ( VecCons I VecNil ) ( VecCons B VecNil ) $.
ax-op-basepoint1 $a |- Op Basepoint1 ( VecCons I VecNil ) ( VecCons B VecNil ) $.
ax-op-basepoint2 $a |- Op Basepoint2 ( VecCons I VecNil ) ( VecCons B VecNil ) $.
ax-op-basepoint3 $a |- Op Basepoint3 ( VecCons I VecNil ) ( VecCons B VecNil ) $.
ax-op-gen4 $a |- Op Gen4 ( VecCons B ( VecCons B ( VecCons B ( VecCons B VecNil ) ) ) ) ( VecCons B VecNil ) $.
ax-op-trialityL $a |- Op TrialityL ( VecCons B VecNil ) ( VecCons L VecNil ) $.
ax-op-trialityR $a |- Op TrialityR ( VecCons B VecNil ) ( VecCons R VecNil ) $.
ax-op-trialityB $a |- Op TrialityB ( VecAppend ( VecCons L VecNil ) ( VecCons R VecNil ) ) ( VecCons B VecNil ) $.
ax-op-conjB $a |- Op ConjB ( VecCons B VecNil ) ( VecCons B VecNil ) $.
ax-op-conjL $a |- Op ConjL ( VecCons L VecNil ) ( VecCons L VecNil ) $.
ax-op-conjR $a |- Op ConjR ( VecCons R VecNil ) ( VecCons R VecNil ) $.
ax-op-copyB $a |- Op CopyB ( VecCons B VecNil ) ( VecCons B ( VecCons B VecNil ) ) $.
ax-op-eraseB $a |- Op EraseB ( VecCons B VecNil ) ( VecCons I VecNil ) $.
ax-op-tensorL $a |- Op TensorL ( VecAppend ( VecCons L VecNil ) ( VecCons L VecNil ) ) ( VecCons L VecNil ) $.
ax-op-guardNeg $a |- Op GuardNeg ( VecAppend ( VecCons L VecNil ) ( VecCons L VecNil ) ) ( VecCons L VecNil ) $.
ax-op-guardNAND $a |- Op GuardNAND ( VecAppend ( VecCons L VecNil ) ( VecAppend ( VecCons L VecNil ) ( VecCons L VecNil ) ) ) ( VecCons L VecNil ) $.
ax-op-braidBB $a |- Op BraidBB ( VecAppend ( VecCons B VecNil ) ( VecCons B VecNil ) ) ( VecAppend ( VecCons B VecNil ) ( VecCons B VecNil ) ) $.
ax-op-deltaB $a |- Op DeltaB ( VecCons B VecNil ) ( VecCons B VecNil ) $.
ax-op-cumulantB $a |- Op CumulantB ( VecCons B VecNil ) ( VecCons B VecNil ) $.
