$(
  clean/core/base.mm - foundational typing layer for the CLEAN v10 port
  ---------------------------------------------------------------------
  This file introduces the primitive syntactic categories used to mimic
  the Agda dependent typing discipline inside Metamath.  We work with a
  minimalist Hilbert-style propositional shell (implication only) and
  treat naturals, sorts, vectors, and boundaries as first-class term
  constructors guarded by explicit well-formedness predicates.

  The axioms below act as typing rules: they state how each constructor
  preserves lengths or sector invariants.  Later developments can build
  proofs on top of these clauses, or refine them into derivable theorems
  once additional logical infrastructure (e.g. quantifiers) is in place.
$)

$c wff term |- ( ) -> = Nat Sort Vec Boundary Len Succ Add VecNil VecCons VecAppend BoundaryOf Src Dst L B R I Zero $.

$v ph ps ch m n k xs ys zs s t b $.

wph $f wff ph $.
wps $f wff ps $.
wch $f wff ch $.

vm $f term m $.
vn $f term n $.
vk $f term k $.
vxs $f term xs $.
vys $f term ys $.
vzs $f term zs $.
vs $f term s $.
vt $f term t $.
vb $f term b $.

wi $a wff ( ph -> ps ) $.
weq $a wff m = n $.

ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
ax-2 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.

${
mp1 $e |- ph $.
mp2 $e |- ( ph -> ps ) $.
ax-mp $a |- ps $.
$}

wNat $a wff Nat m $.
wSort $a wff Sort s $.
wVec $a wff Vec xs m $.
wBoundary $a wff Boundary b xs ys $.

cZero $a term Zero $.
csucc $a term ( Succ m ) $.
cadd $a term ( m Add n ) $.
cvecnil $a term VecNil $.
cveccons $a term ( VecCons s xs ) $.
cvecappend $a term ( VecAppend xs ys ) $.
clen $a term ( Len xs ) $.
cboundaryof $a term ( BoundaryOf xs ys ) $.
csrc $a term ( Src b ) $.
cdst $a term ( Dst b ) $.

cL $a term L $.
cB $a term B $.
cR $a term R $.
cI $a term I $.

$( Sort universe typing axioms. $)
ax-sort-L $a |- Sort L $.
ax-sort-B $a |- Sort B $.
ax-sort-R $a |- Sort R $.
ax-sort-I $a |- Sort I $.

$( Natural number typing axioms. $)
ax-nat-zero $a |- Nat Zero $.
ax-nat-succ $a |- ( Nat m -> Nat ( Succ m ) ) $.
ax-nat-add $a |- ( Nat m -> ( Nat n -> Nat ( m Add n ) ) ) $.

$( Vector typing and structural axioms. $)
ax-vec-nil $a |- Vec VecNil Zero $.
ax-vec-cons $a |- ( Sort s -> ( Vec xs m -> Vec ( VecCons s xs ) ( Succ m ) ) ) $.
ax-vec-append $a |- ( Vec xs m -> ( Vec ys n -> Vec ( VecAppend xs ys ) ( m Add n ) ) ) $.

$( Vector length bookkeeping. $)
ax-len-nil $a |- Len VecNil = Zero $.
ax-len-cons $a |- ( Sort s -> ( Vec xs m -> Len ( VecCons s xs ) = Succ ( Len xs ) ) ) $.
ax-len-append $a |- ( Vec xs m -> ( Vec ys n -> Len ( VecAppend xs ys ) = ( Len xs ) Add ( Len ys ) ) ) $.

$( Boundary constructors mirror Agda's Boundary record. $)
ax-boundary-mk $a |- ( Vec xs m -> ( Vec ys n -> Boundary ( BoundaryOf xs ys ) xs ys ) ) $.
ax-src-mk $a |- ( Vec xs m -> ( Vec ys n -> Src ( BoundaryOf xs ys ) = xs ) ) $.
ax-dst-mk $a |- ( Vec xs m -> ( Vec ys n -> Dst ( BoundaryOf xs ys ) = ys ) ) $.
ax-boundary-src $a |- ( Boundary b xs ys -> Src b = xs ) $.
ax-boundary-dst $a |- ( Boundary b xs ys -> Dst b = ys ) $.

$( Equality sanity within the sort universe. $)
ax-sort-sanity $a |- ( Sort s -> ( Sort t -> ( s = t -> Sort s ) ) ) $.
