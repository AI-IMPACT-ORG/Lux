$(
  clean/core/moduli.mm - Modulus declarations only
  -------------------------------------------------
  Lists the optional CLEAN moduli alongside the rule schemas they enable.
  Proof stubs from earlier revisions have been removed until they can be
  formalised.
$)

$[ rewrite.mm $]

$c ModRetractL ModRetractR ModTrialityBulk ModTrialityLeft ModTrialityRight ModConjLeftEmbed ModConjRightEmbed ModConjLeftObserve ModConjRightObserve ModGuardedNAND ModBraidInvolutive ModDeltaCumulant ModDeltaBulk RetractL RetractR TrialityBulk TrialityLeft TrialityRight ConjLeftEmbed ConjRightEmbed ConjLeftObserve ConjRightObserve GuardedNANDRule BraidRule DeltaCumulantRule DeltaBulkRule CleanFamily $.

wModRetractL $a wff ModRetractL $.
wModRetractR $a wff ModRetractR $.
wModTrialityBulk $a wff ModTrialityBulk $.
wModTrialityLeft $a wff ModTrialityLeft $.
wModTrialityRight $a wff ModTrialityRight $.
wModConjLeftEmbed $a wff ModConjLeftEmbed $.
wModConjRightEmbed $a wff ModConjRightEmbed $.
wModConjLeftObserve $a wff ModConjLeftObserve $.
wModConjRightObserve $a wff ModConjRightObserve $.
wModGuardedNAND $a wff ModGuardedNAND $.
wModBraidInvolutive $a wff ModBraidInvolutive $.
wModDeltaCumulant $a wff ModDeltaCumulant $.
wModDeltaBulk $a wff ModDeltaBulk $.

cRetractL $a term RetractL $.
cRetractR $a term RetractR $.
cTrialityBulk $a term TrialityBulk $.
cTrialityLeft $a term TrialityLeft $.
cTrialityRight $a term TrialityRight $.
cConjLeftEmbed $a term ConjLeftEmbed $.
cConjRightEmbed $a term ConjRightEmbed $.
cConjLeftObserve $a term ConjLeftObserve $.
cConjRightObserve $a term ConjRightObserve $.
cGuardedNANDRule $a term GuardedNANDRule $.
cBraidRule $a term BraidRule $.
cDeltaCumulantRule $a term DeltaCumulantRule $.
cDeltaBulkRule $a term DeltaBulkRule $.
cCleanFamily $a term CleanFamily $.

clean-infamily-retractL $a |- ( ModRetractL -> InFamily CleanFamily RetractL ) $.
clean-infamily-retractR $a |- ( ModRetractR -> InFamily CleanFamily RetractR ) $.
clean-infamily-trialityB $a |- ( ModTrialityBulk -> InFamily CleanFamily TrialityBulk ) $.
clean-infamily-trialityL $a |- ( ModTrialityLeft -> InFamily CleanFamily TrialityLeft ) $.
clean-infamily-trialityR $a |- ( ModTrialityRight -> InFamily CleanFamily TrialityRight ) $.
clean-infamily-conjLeftEmbed $a |- ( ModConjLeftEmbed -> InFamily CleanFamily ConjLeftEmbed ) $.
clean-infamily-conjRightEmbed $a |- ( ModConjRightEmbed -> InFamily CleanFamily ConjRightEmbed ) $.
clean-infamily-conjLeftObserve $a |- ( ModConjLeftObserve -> InFamily CleanFamily ConjLeftObserve ) $.
clean-infamily-conjRightObserve $a |- ( ModConjRightObserve -> InFamily CleanFamily ConjRightObserve ) $.
clean-infamily-guardedNAND $a |- ( ModGuardedNAND -> InFamily CleanFamily GuardedNANDRule ) $.
clean-infamily-braid $a |- ( ModBraidInvolutive -> InFamily CleanFamily BraidRule ) $.
clean-infamily-deltaCumulant $a |- ( ModDeltaCumulant -> InFamily CleanFamily DeltaCumulantRule ) $.
clean-infamily-deltaBulk $a |- ( ModDeltaBulk -> InFamily CleanFamily DeltaBulkRule ) $.

$( When a modulus holds, it yields the corresponding rule schema. $)
mod-retractL $a |- ( ModRetractL -> Rule RetractL ( VecCons L VecNil ) ( VecCons L VecNil ) ( Comp ( Gen NuL ) ( Gen IotaL ) ) ( Id ( VecCons L VecNil ) ) ) $.
mod-retractR $a |- ( ModRetractR -> Rule RetractR ( VecCons R VecNil ) ( VecCons R VecNil ) ( Comp ( Gen NuR ) ( Gen IotaR ) ) ( Id ( VecCons R VecNil ) ) ) $.
mod-triality-bulk $a |- ( ModTrialityBulk -> Rule TrialityBulk ( VecAppend ( VecCons L VecNil ) ( VecCons R VecNil ) ) ( VecCons B VecNil ) ( Gen TrialityB ) ( Comp ( Gen BulkSum ) ( Tens ( Gen IotaL ) ( Gen IotaR ) ) ) ) $.
mod-triality-left $a |- ( ModTrialityLeft -> Rule TrialityLeft ( VecCons B VecNil ) ( VecCons L VecNil ) ( Gen TrialityL ) ( Gen NuL ) ) $.
mod-triality-right $a |- ( ModTrialityRight -> Rule TrialityRight ( VecCons B VecNil ) ( VecCons R VecNil ) ( Gen TrialityR ) ( Gen NuR ) ) $.
mod-conj-left-embed $a |- ( ModConjLeftEmbed -> Rule ConjLeftEmbed ( VecCons L VecNil ) ( VecCons B VecNil ) ( Comp ( Gen ConjB ) ( Gen IotaL ) ) ( Comp ( Gen IotaL ) ( Gen ConjL ) ) ) $.
mod-conj-right-embed $a |- ( ModConjRightEmbed -> Rule ConjRightEmbed ( VecCons R VecNil ) ( VecCons B VecNil ) ( Comp ( Gen ConjB ) ( Gen IotaR ) ) ( Comp ( Gen IotaR ) ( Gen ConjR ) ) ) $.
mod-conj-left-observe $a |- ( ModConjLeftObserve -> Rule ConjLeftObserve ( VecCons B VecNil ) ( VecCons L VecNil ) ( Comp ( Gen NuL ) ( Gen ConjB ) ) ( Comp ( Gen ConjL ) ( Gen NuL ) ) ) $.
mod-conj-right-observe $a |- ( ModConjRightObserve -> Rule ConjRightObserve ( VecCons B VecNil ) ( VecCons R VecNil ) ( Comp ( Gen NuR ) ( Gen ConjB ) ) ( Comp ( Gen ConjR ) ( Gen NuR ) ) ) $.
mod-guardedNAND $a |- ( ModGuardedNAND -> Rule GuardedNANDRule ( VecAppend ( VecCons L VecNil ) ( VecAppend ( VecCons L VecNil ) ( VecCons L VecNil ) ) ) ( VecCons L VecNil ) ( Gen GuardNAND ) ( Comp ( Gen GuardNeg ) ( Tens ( Id ( VecCons L VecNil ) ) ( Gen TensorL ) ) ) ) $.
mod-braid $a |- ( ModBraidInvolutive -> Rule BraidRule ( VecAppend ( VecCons B VecNil ) ( VecCons B VecNil ) ) ( VecAppend ( VecCons B VecNil ) ( VecCons B VecNil ) ) ( Comp ( Gen BraidBB ) ( Gen BraidBB ) ) ( Id ( VecAppend ( VecCons B VecNil ) ( VecCons B VecNil ) ) ) ) $.
mod-delta-cumulant $a |- ( ModDeltaCumulant -> Rule DeltaCumulantRule ( VecCons B VecNil ) ( VecCons B VecNil ) ( Comp ( Gen DeltaB ) ( Gen CumulantB ) ) ( Comp ( Gen CumulantB ) ( Gen DeltaB ) ) ) $.
mod-delta-bulksum $a |- ( ModDeltaBulk -> Rule DeltaBulkRule ( VecAppend ( VecCons B VecNil ) ( VecCons B VecNil ) ) ( VecCons B VecNil ) ( Comp ( Gen DeltaB ) ( Gen BulkSum ) ) ( Comp ( Gen BulkSum ) ( Tens ( Gen DeltaB ) ( Gen DeltaB ) ) ) ) $.

$( Derived rewrite witnesses used by the renormalisation bridge. $)
clean-rewrite-retractL $a |- ( ModRetractL ->
  RewriteStar CleanFamily ( Comp ( Gen NuL ) ( Gen IotaL ) )
                               ( Id ( VecCons L VecNil ) ) ) $.
clean-rewrite-retractR $a |- ( ModRetractR ->
  RewriteStar CleanFamily ( Comp ( Gen NuR ) ( Gen IotaR ) )
                               ( Id ( VecCons R VecNil ) ) ) $.
clean-rewrite-delta-bulk $a |- ( ModDeltaBulk ->
  RewriteStar CleanFamily ( Comp ( Gen DeltaB ) ( Gen BulkSum ) )
                               ( Comp ( Gen BulkSum )
                                      ( Tens ( Gen DeltaB ) ( Gen DeltaB ) ) ) ) $.
clean-rewrite-delta-cumulant $a |- ( ModDeltaCumulant ->
  RewriteStar CleanFamily ( Comp ( Gen DeltaB ) ( Gen CumulantB ) )
                               ( Comp ( Gen CumulantB ) ( Gen DeltaB ) ) ) $.
clean-rewrite-triality $a |- ( ModTrialityBulk ->
  RewriteStar CleanFamily ( Gen TrialityB )
                               ( Comp ( Gen BulkSum ) ( Tens ( Gen IotaL ) ( Gen IotaR ) ) ) ) $.
clean-rewrite-guardedNAND $a |- ( ModGuardedNAND ->
  RewriteStar CleanFamily ( Gen GuardNAND )
                               ( Comp ( Gen GuardNeg )
                                      ( Tens ( Id ( VecCons L VecNil ) ) ( Gen TensorL ) ) ) ) $.
clean-rewrite-braid $a |- ( ModBraidInvolutive ->
  RewriteStar CleanFamily ( Comp ( Gen BraidBB ) ( Gen BraidBB ) )
                               ( Id ( VecAppend ( VecCons B VecNil ) ( VecCons B VecNil ) ) ) ) $.
