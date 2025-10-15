$(
  clean/core/renormalisation.mm - Renormalisation adapters
  --------------------------------------------------------
  Abstracts the four CLEAN renormalisation rewrite witnesses into a
  parameterised semiring adapter and then instantiates three concrete
  adapters (bulk, phase, guard) that rely only on CLEAN rewrites.
$)

$[ moduli.mm $]

$c RenormSemiring BulkSemiring PhaseSemiring GuardSemiring $.
$c RenormZero RenormOne RenormPlus RenormTimes BulkZero BulkOne BulkPlus BulkTimes $.
$c PhaseZero PhaseOne PhasePlus PhaseTimes GuardZero GuardOne GuardPlus GuardTimes $.

cRenormZero $a term RenormZero $.
cRenormOne $a term RenormOne $.
cRenormPlus $a term RenormPlus $.
cRenormTimes $a term RenormTimes $.

cBulkZero $a term BulkZero $.
cBulkOne $a term BulkOne $.
cBulkPlus $a term BulkPlus $.
cBulkTimes $a term BulkTimes $.

cPhaseZero $a term PhaseZero $.
cPhaseOne $a term PhaseOne $.
cPhasePlus $a term PhasePlus $.
cPhaseTimes $a term PhaseTimes $.

cGuardZero $a term GuardZero $.
cGuardOne $a term GuardOne $.
cGuardPlus $a term GuardPlus $.
cGuardTimes $a term GuardTimes $.

wRenormSemiring $a wff RenormSemiring $.
wBulkSemiring $a wff BulkSemiring $.
wPhaseSemiring $a wff PhaseSemiring $.
wGuardSemiring $a wff GuardSemiring $.

$( Generic semiring adapter derived from renormalisation witnesses. $)
renorm-zero $a |- ( RenormSemiring ->
  RewriteStar CleanFamily RenormZero ( Id ( VecCons L VecNil ) ) ) $.
renorm-one $a |- ( RenormSemiring ->
  RewriteStar CleanFamily RenormOne ( Id ( VecCons R VecNil ) ) ) $.
renorm-plus $a |- ( RenormSemiring ->
  RewriteStar CleanFamily RenormPlus
    ( Comp ( Gen BulkSum ) ( Tens ( Gen DeltaB ) ( Gen DeltaB ) ) ) ) $.
renorm-times $a |- ( RenormSemiring ->
  RewriteStar CleanFamily RenormTimes ( Comp ( Gen CumulantB ) ( Gen DeltaB ) ) ) $.

renorm-intro $a |- ( RewriteStar CleanFamily RenormZero ( Id ( VecCons L VecNil ) ) ->
  ( RewriteStar CleanFamily RenormOne ( Id ( VecCons R VecNil ) ) ->
    ( RewriteStar CleanFamily RenormPlus ( Comp ( Gen BulkSum )
                                          ( Tens ( Gen DeltaB ) ( Gen DeltaB ) ) ) ->
      ( RewriteStar CleanFamily RenormTimes ( Comp ( Gen CumulantB ) ( Gen DeltaB ) ) ->
        RenormSemiring ) ) ) ) $.

$( Bulk adapter: canonical operations from delta/bulk rewrites. $)
bulk-zero-def $a |- BulkZero = Comp ( Gen NuL ) ( Gen IotaL ) $.
bulk-one-def $a |- BulkOne = Comp ( Gen NuR ) ( Gen IotaR ) $.
bulk-plus-def $a |- BulkPlus = Comp ( Gen DeltaB ) ( Gen BulkSum ) $.
bulk-times-def $a |- BulkTimes = Comp ( Gen DeltaB ) ( Gen CumulantB ) $.

bulk-intro $a |- ( RewriteStar CleanFamily BulkZero ( Id ( VecCons L VecNil ) ) ->
  ( RewriteStar CleanFamily BulkOne ( Id ( VecCons R VecNil ) ) ->
    ( RewriteStar CleanFamily BulkPlus ( Comp ( Gen BulkSum )
                                        ( Tens ( Gen DeltaB ) ( Gen DeltaB ) ) ) ->
      ( RewriteStar CleanFamily BulkTimes ( Comp ( Gen CumulantB ) ( Gen DeltaB ) ) ->
        BulkSemiring ) ) ) ) $.

bulk-zero $a |- ( BulkSemiring ->
  RewriteStar CleanFamily BulkZero ( Id ( VecCons L VecNil ) ) ) $.
bulk-one $a |- ( BulkSemiring ->
  RewriteStar CleanFamily BulkOne ( Id ( VecCons R VecNil ) ) ) $.
bulk-plus $a |- ( BulkSemiring ->
  RewriteStar CleanFamily BulkPlus ( Comp ( Gen BulkSum )
                                      ( Tens ( Gen DeltaB ) ( Gen DeltaB ) ) ) ) $.
bulk-times $a |- ( BulkSemiring ->
  RewriteStar CleanFamily BulkTimes ( Comp ( Gen CumulantB ) ( Gen DeltaB ) ) ) $.

$( Phase adapter: emphasises header flow composites and triality rewrites. $)
phase-zero-def $a |- PhaseZero = Comp ( Gen NuL ) ( Gen NuL ) $.
phase-one-def $a |- PhaseOne = Comp ( Gen NuR ) ( Gen NuR ) $.
phase-plus-def $a |- PhasePlus = Comp ( Gen DeltaB ) ( Gen DeltaB ) $.
phase-times-def $a |- PhaseTimes = Comp ( Gen CumulantB ) ( Gen CumulantB ) $.

phase-intro $a |- ( RewriteStar CleanFamily PhaseZero ( Id ( VecCons L VecNil ) ) ->
  ( RewriteStar CleanFamily PhaseOne ( Id ( VecCons R VecNil ) ) ->
    ( RewriteStar CleanFamily PhasePlus ( Comp ( Gen BulkSum )
                                          ( Tens ( Gen DeltaB ) ( Gen DeltaB ) ) ) ->
      ( RewriteStar CleanFamily PhaseTimes ( Comp ( Gen CumulantB ) ( Gen DeltaB ) ) ->
        ( RewriteStar CleanFamily ( Gen TrialityB )
                                   ( Comp ( Gen BulkSum )
                                          ( Tens ( Gen IotaL ) ( Gen IotaR ) ) ) ->
          PhaseSemiring ) ) ) ) ) $.

phase-zero $a |- ( PhaseSemiring ->
  RewriteStar CleanFamily PhaseZero ( Id ( VecCons L VecNil ) ) ) $.
phase-one $a |- ( PhaseSemiring ->
  RewriteStar CleanFamily PhaseOne ( Id ( VecCons R VecNil ) ) ) $.
phase-plus $a |- ( PhaseSemiring ->
  RewriteStar CleanFamily PhasePlus ( Comp ( Gen BulkSum )
                                       ( Tens ( Gen DeltaB ) ( Gen DeltaB ) ) ) ) $.
phase-times $a |- ( PhaseSemiring ->
  RewriteStar CleanFamily PhaseTimes ( Comp ( Gen CumulantB ) ( Gen DeltaB ) ) ) $.
phase-triality $a |- ( PhaseSemiring ->
  RewriteStar CleanFamily ( Gen TrialityB )
                               ( Comp ( Gen BulkSum ) ( Tens ( Gen IotaL ) ( Gen IotaR ) ) ) ) $.

$( Guard adapter: interfaces with guard and braid witnesses explicitly. $)
guard-zero-def $a |- GuardZero = Comp ( Gen NuL ) ( Gen GuardNeg ) $.
guard-one-def $a |- GuardOne = Comp ( Gen NuR ) ( Gen GuardNeg ) $.
guard-plus-def $a |- GuardPlus = Comp ( Gen DeltaB ) ( Gen GuardNAND ) $.
guard-times-def $a |- GuardTimes = Comp ( Gen DeltaB ) ( Gen BraidBB ) $.

guard-intro $a |- ( RewriteStar CleanFamily GuardZero ( Id ( VecCons L VecNil ) ) ->
  ( RewriteStar CleanFamily GuardOne ( Id ( VecCons R VecNil ) ) ->
    ( RewriteStar CleanFamily GuardPlus ( Comp ( Gen BulkSum )
                                          ( Tens ( Gen DeltaB ) ( Gen DeltaB ) ) ) ->
      ( RewriteStar CleanFamily GuardTimes ( Comp ( Gen CumulantB ) ( Gen DeltaB ) ) ->
        ( RewriteStar CleanFamily ( Gen GuardNAND )
                                   ( Comp ( Gen GuardNeg )
                                          ( Tens ( Id ( VecCons L VecNil ) ) ( Gen TensorL ) ) ) ->
          ( RewriteStar CleanFamily ( Comp ( Gen BraidBB ) ( Gen BraidBB ) )
                                    ( Id ( VecAppend ( VecCons B VecNil )
                                                     ( VecCons B VecNil ) ) ) ->
            GuardSemiring ) ) ) ) ) ) $.

guard-zero $a |- ( GuardSemiring ->
  RewriteStar CleanFamily GuardZero ( Id ( VecCons L VecNil ) ) ) $.
guard-one $a |- ( GuardSemiring ->
  RewriteStar CleanFamily GuardOne ( Id ( VecCons R VecNil ) ) ) $.
guard-plus $a |- ( GuardSemiring ->
  RewriteStar CleanFamily GuardPlus ( Comp ( Gen BulkSum )
                                       ( Tens ( Gen DeltaB ) ( Gen DeltaB ) ) ) ) $.
guard-times $a |- ( GuardSemiring ->
  RewriteStar CleanFamily GuardTimes ( Comp ( Gen CumulantB ) ( Gen DeltaB ) ) ) $.
guard-nand $a |- ( GuardSemiring ->
  RewriteStar CleanFamily ( Gen GuardNAND )
                               ( Comp ( Gen GuardNeg )
                                      ( Tens ( Id ( VecCons L VecNil ) ) ( Gen TensorL ) ) ) ) $.
guard-braid $a |- ( GuardSemiring ->
  RewriteStar CleanFamily ( Comp ( Gen BraidBB ) ( Gen BraidBB ) )
                               ( Id ( VecAppend ( VecCons B VecNil ) ( VecCons B VecNil ) ) ) ) $.
