$(
  clean/core/normalform.mm - Normal-form primitives only
  ----------------------------------------------------
  Declarations for headers, flows, and normal forms without the incomplete
  derived lemmas from earlier drafts.
$)

$[ base.mm $]

$c Sign Signed Header NormalForm PhaseFlow ScaleFlow MkSigned MkHeader MkNF MkPhaseFlow MkScaleFlow SignPart Magnitude PhaseL PhaseR ScaleL ScaleR HeaderOf CoreOf ActPhase ActScale ComposePhase ComposeScale IdPhaseFlow IdScaleFlow BulkPhase BulkScale Parametrise DeltaFlow CumulantFlow DeltaNF CumulantNF Plus Minus SignedZero $.


$v u h nf pf qf rg sh core $.

vu-normal $f term u $.
vh-normal $f term h $.
vnf-normal $f term nf $.
vpf-normal $f term pf $.
vqf-normal $f term qf $.
vrg-normal $f term rg $.
vsh-normal $f term sh $.
vcore-normal $f term core $.




wSign $a wff Sign s $.
wSigned $a wff Signed s $.
wHeader $a wff Header h $.
wNormalForm $a wff NormalForm nf $.
wPhaseFlow $a wff PhaseFlow pf $.
wScaleFlow $a wff ScaleFlow qf $.

cPlus $a term Plus $.
cMinus $a term Minus $.
cSignedZero $a term SignedZero $.

cMkSigned $a term ( MkSigned s m ) $.
cMkHeader $a term ( MkHeader s t m n ) $.
cMkNF $a term ( MkNF h core ) $.

cMkPhaseFlow $a term ( MkPhaseFlow pf ) $.
cMkScaleFlow $a term ( MkScaleFlow qf ) $.

cSignPart $a term ( SignPart s ) $.
cMagnitude $a term ( Magnitude s ) $.
cPhaseL $a term ( PhaseL h ) $.
cPhaseR $a term ( PhaseR h ) $.
cScaleL $a term ( ScaleL h ) $.
cScaleR $a term ( ScaleR h ) $.
cHeaderOf $a term ( HeaderOf nf ) $.
cCoreOf $a term ( CoreOf nf ) $.

cActPhase $a term ( ActPhase pf s ) $.
cActScale $a term ( ActScale qf m ) $.

cComposePhase $a term ( ComposePhase pf qf ) $.
cComposeScale $a term ( ComposeScale pf qf ) $.

cIdPhaseFlow $a term IdPhaseFlow $.
cIdScaleFlow $a term IdScaleFlow $.

cBulkPhase $a term ( BulkPhase h ) $.
cBulkScale $a term ( BulkScale h ) $.

cParametrise $a term ( Parametrise pf qf rg sh nf ) $.
cDeltaFlow $a term DeltaFlow $.
cCumulantFlow $a term CumulantFlow $.
cDeltaNF $a term ( DeltaNF nf ) $.
cCumulantNF $a term ( CumulantNF nf ) $.

$( Sign constructors. $)
ax-sign-plus $a |- Sign Plus $.
ax-sign-minus $a |- Sign Minus $.
ax-sign-zero $a |- Signed ( MkSigned Plus Zero ) $.

$( Signed packages a sign with a magnitude. $)
ax-signed-intro $a |- ( Sign s -> ( Nat m -> Signed ( MkSigned s m ) ) ) $.
ax-signed-sign $a |- SignPart ( MkSigned s m ) = s $.
ax-signed-magnitude $a |- Magnitude ( MkSigned s m ) = m $.

$( Header stores phase/scale pairs. $)
ax-header-intro $a |- ( Signed s -> ( Signed t -> ( Nat m -> ( Nat n -> Header ( MkHeader s t m n ) ) ) ) ) $.
ax-header-phaseL $a |- PhaseL ( MkHeader s t m n ) = s $.
ax-header-phaseR $a |- PhaseR ( MkHeader s t m n ) = t $.
ax-header-scaleL $a |- ScaleL ( MkHeader s t m n ) = m $.
ax-header-scaleR $a |- ScaleR ( MkHeader s t m n ) = n $.

$( Normal forms pair a header with an arbitrary core payload. $)
ax-nf-intro $a |- ( Header h -> NormalForm ( MkNF h core ) ) $.
ax-nf-header $a |- HeaderOf ( MkNF h core ) = h $.
ax-nf-core $a |- CoreOf ( MkNF h core ) = core $.

$( Phase and scale flows. $)
ax-phaseflow-intro $a |- PhaseFlow ( MkPhaseFlow pf ) $.
ax-scaleflow-intro $a |- ScaleFlow ( MkScaleFlow qf ) $.
ax-phaseflow-act $a |- ActPhase ( MkPhaseFlow pf ) s = ActPhase pf s $.
ax-scaleflow-act $a |- ActScale ( MkScaleFlow qf ) m = ActScale qf m $.

$( Composition of flows acts sequentially on phases and scales. $)
ax-composephase-act $a |- ActPhase ( ComposePhase pf qf ) s =
  ActPhase qf ( ActPhase pf s ) $.
ax-composescale-act $a |- ActScale ( ComposeScale pf qf ) m =
  ActScale qf ( ActScale pf m ) $.
ax-composephase-assoc $a |- ComposePhase pf ( ComposePhase qf rg ) =
  ComposePhase ( ComposePhase pf qf ) rg $.
ax-composescale-assoc $a |- ComposeScale pf ( ComposeScale qf rg ) =
  ComposeScale ( ComposeScale pf qf ) rg $.

$( Identity flows act as neutral elements for composition. $)
ax-id-phaseflow $a |- PhaseFlow IdPhaseFlow $.
ax-id-scaleflow $a |- ScaleFlow IdScaleFlow $.
ax-id-phaseflow-act $a |- ActPhase IdPhaseFlow s = s $.
ax-id-scaleflow-act $a |- ActScale IdScaleFlow m = m $.

$( Bulk header accessors. $)
ax-bulk-phase $a |- BulkPhase h = MkSigned ( SignPart ( PhaseL h ) ) ( Magnitude ( PhaseL h ) Add Magnitude ( PhaseR h ) ) $.
ax-bulk-scale $a |- BulkScale h = ( ScaleL h ) Add ( ScaleR h ) $.

$( Parametrisation adjusts the header via the supplied flows. $)
ax-parametrise $a |- Parametrise pf qf rg sh nf =
  MkNF
    ( MkHeader
        ( ActPhase pf ( PhaseL ( HeaderOf nf ) ) )
        ( ActPhase qf ( PhaseR ( HeaderOf nf ) ) )
        ( ActScale rg ( ScaleL ( HeaderOf nf ) ) )
        ( ActScale sh ( ScaleR ( HeaderOf nf ) ) ) )
    ( CoreOf nf ) $.

$( Delta/Cumulant flow placeholders. $)
ax-deltaflow $a |- ScaleFlow DeltaFlow $.
ax-cumulantflow $a |- ScaleFlow CumulantFlow $.
ax-deltaNF $a |- DeltaNF nf = Parametrise IdPhaseFlow IdPhaseFlow DeltaFlow DeltaFlow nf $.
ax-cumulantNF $a |- CumulantNF nf = Parametrise IdPhaseFlow IdPhaseFlow CumulantFlow CumulantFlow nf $.
