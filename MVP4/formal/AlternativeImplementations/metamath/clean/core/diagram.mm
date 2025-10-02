$(
  clean/core/diagram.mm - Diagram primitives only
  -----------------------------------------------
  Minimal constructors for CLEAN diagrams.  Derived identities were
  dropped while the port is being rebuilt, leaving only the basic
  `Diag` introduction axioms.
$)

$[ base.mm $]
$[ signature.mm $]

$c Diag Id Gen Comp Tens $.


$v d e f g xs1 xs2 ys1 ys2 $.

vd-diag $f term d $.
ve-diag $f term e $.
vf-diag $f term f $.
vg-diag $f term g $.

vxs1-diag $f term xs1 $.
vxs2-diag $f term xs2 $.
vys1-diag $f term ys1 $.
vys2-diag $f term ys2 $.


wDiag $a wff Diag d xs ys $.

cId $a term ( Id xs ) $.
cGen $a term ( Gen op ) $.
cComp $a term ( Comp f g ) $.
cTens $a term ( Tens f g ) $.

$( Identity diagrams inherit their boundary. $)
ax-diag-id $a |- ( Vec xs m -> Diag ( Id xs ) xs xs ) $.

$( Generators lift Op declarations into diagrams. $)
ax-diag-gen $a |- ( Op op xs ys -> Diag ( Gen op ) xs ys ) $.

$( Sequential composition stitches compatible diagrams. $)
ax-diag-comp $a |- ( Diag f ys zs -> ( Diag g xs ys -> Diag ( Comp f g ) xs zs ) ) $.

$( Monoidal tensor concatenates boundaries component-wise. $)
ax-diag-tens $a |- ( Diag f xs1 ys1 -> ( Diag g xs2 ys2 -> Diag ( Tens f g ) ( VecAppend xs1 xs2 ) ( VecAppend ys1 ys2 ) ) ) $.

$( Boundary projections recover the source/target vectors. $)
ax-diag-src $a |- ( Diag d xs ys -> Src ( BoundaryOf xs ys ) = xs ) $.
ax-diag-dst $a |- ( Diag d xs ys -> Dst ( BoundaryOf xs ys ) = ys ) $.

