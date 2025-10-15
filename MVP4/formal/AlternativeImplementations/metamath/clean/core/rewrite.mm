$(
  clean/core/rewrite.mm - Rewrite interface stub
  -----------------------------------------------
  Provides only the predicates and closure axioms needed by higher layers.
  Proofs that previously referenced unfinished rule families were removed.
$)

$[ diagram.mm $]

$c Rule InFamily Rewrite RewriteStar $.


$v F r p q h $.

vF-rewrite $f term F $.
vr-rewrite $f term r $.
vp-rewrite $f term p $.
vq-rewrite $f term q $.
vh-rewrite $f term h $.



wRule $a wff Rule r xs ys f g $.
wFamily $a wff InFamily F r $.
wRewrite $a wff Rewrite F f g $.
wRewriteStar $a wff RewriteStar F f g $.

$( Rule families generate one-step rewrites. $)
ax-rewrite-step $a |- ( InFamily F r -> ( Rule r xs ys f g -> Rewrite F f g ) ) $.

$( Sequential context closure. $)
ax-rewrite-seq-left $a |- ( Rewrite F f g -> Rewrite F ( Comp f h ) ( Comp g h ) ) $.
ax-rewrite-seq-right $a |- ( Rewrite F f g -> Rewrite F ( Comp h f ) ( Comp h g ) ) $.

$( Monoidal context closure. $)
ax-rewrite-tens-left $a |- ( Rewrite F f g -> Rewrite F ( Tens f h ) ( Tens g h ) ) $.
ax-rewrite-tens-right $a |- ( Rewrite F f g -> Rewrite F ( Tens h f ) ( Tens h g ) ) $.

$( Reflexive-transitive closure. $)
ax-rewrite-refl $a |- RewriteStar F f f $.
ax-rewrite-trans $a |- ( Rewrite F f g -> ( RewriteStar F g h -> RewriteStar F f h ) ) $.
ax-rewrite-star-step $a |- ( Rewrite F f g -> RewriteStar F f g ) $.
ax-rewrite-star-seq-left $a |- ( RewriteStar F f g -> RewriteStar F ( Comp f h ) ( Comp g h ) ) $.
ax-rewrite-star-seq-right $a |- ( RewriteStar F f g -> RewriteStar F ( Comp h f ) ( Comp h g ) ) $.
ax-rewrite-star-tens-left $a |- ( RewriteStar F f g -> RewriteStar F ( Tens f h ) ( Tens g h ) ) $.
ax-rewrite-star-tens-right $a |- ( RewriteStar F f g -> RewriteStar F ( Tens h f ) ( Tens h g ) ) $.
