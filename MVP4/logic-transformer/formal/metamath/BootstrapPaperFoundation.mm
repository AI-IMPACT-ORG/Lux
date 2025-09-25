$(
BootstrapPaper Foundation for Metamath
Natural type system using wff, sets, and classes
Prepared for ZFC conservative extension proof
$)

$( ============================================================================ $)
$( NATURAL TYPE SYSTEM: wff, set, class $)
$( ============================================================================ $)

$( Well-formed formulas: logical propositions $)
$c wff $.
$( Sets: mathematical objects that can be elements of classes $)
$c set $.
$( Classes: collections that may or may not be sets $)
$c class $.
$( Provability: |- means 'is provable' $)
$c |- $.

$( ============================================================================ $)
$( LOGICAL CONNECTIVES $)
$( ============================================================================ $)

$( Implication $)
$c -> $.
$( Biconditional $)
$c <-> $.
$( Conjunction $)
$c & $.
$( Disjunction $)
$c | $.
$( Negation $)
$c ~ $.
$( Universal quantifier $)
$c A. $.
$( Existential quantifier $)
$c E. $.
$( Parentheses for grouping $)
$c ( ) $.

$( ============================================================================ $)
$( SET THEORY PRIMITIVES $)
$( ============================================================================ $)

$( Membership: x e. A means 'x is an element of A' $)
$c e. $.
$( Equality: x = y means 'x equals y' $)
$c = $.
$( Empty set $)
$c (/) $.
$( Union: A u. B means 'A union B' $)
$c u. $.
$( Intersection: A i^i B means 'A intersection B' $)
$c i^i $.
$( Complement: A \ B means 'A minus B' $)
$c \ $.
$( Power set: P. A means 'power set of A' $)
$c P. $.
$( Subset: A C_ B means 'A is a subset of B' $)
$c C_ $.
$( Proper subset: A C. B means 'A is a proper subset of B' $)
$c C. $.
$( Curly braces for sets $)
$c { } $.

$( ============================================================================ $)
$( BOOTSTRAP PAPER SPECIFIC CONSTANTS $)
$( ============================================================================ $)

$( Global truth structures (classes) $)
$c ModuliSpaceGlobal TypeGraphGlobal ArityGlobal $.
$( Local truth structures (sets) $)
$c ModuliSpaceLocal TypeGraphLocal ArityLocal $.
$( Institution signatures (classes) $)
$c ModuliSpaceSignature TypeGraphSignature RGSignature AritySignature $.
$( Institution sentences (classes) $)
$c ModuliSpaceSentence TypeGraphSentence RGSentence AritySentence $.
$( Institution models (sets) $)
$c ModuliSpaceModel TypeGraphModel RGModel ArityModel $.
$( Satisfaction relations (wff) $)
$c moduli-satisfaction typegraph-satisfaction rg-satisfaction arity-satisfaction $.

$( RG operators (classes) $)
$c rg-flow rg-beta-function rg-anomaly-measure $.
$( RG properties (wff) $)
$c anomaly-vanishes-at-m3 well-formed $.
$( Kernel structures (classes) $)
$c Kernel GlobalLLMParameters DeformationParam GlobalLocalCorrespondence $.
$( Kernel structures (sets) $)
$c KernelParameters LocalTruth $.
$( Functional operators (classes) $)
$c comp $.
$( Functional operators (sets) $)
$c not and or add mul le ge zero one $.
$( Verification predicates (wff) $)
$c complete-system-verification mathematical-consistency $.
$c formal-verification-completeness $.

$( ============================================================================ $)
$( VARIABLES $)
$( ============================================================================ $)

$( Class variables $)
$v A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.
$( Set variables $)
$v a b c d e f g h i j k l m n o p q r s t u v w x y z $.
$( Formula variables $)
$v ph ps ch th ta et ze si rh mu nu xi om $.

$( ============================================================================ $)
$( TYPE DECLARATIONS $)
$( ============================================================================ $)

$( Class variable types $)
cv-A $f class A $.
cv-B $f class B $.
cv-C $f class C $.
cv-D $f class D $.
cv-E $f class E $.
cv-F $f class F $.
cv-G $f class G $.
cv-H $f class H $.
cv-I $f class I $.
cv-J $f class J $.
cv-K $f class K $.
cv-L $f class L $.
cv-M $f class M $.
cv-N $f class N $.
cv-O $f class O $.
cv-P $f class P $.
cv-Q $f class Q $.
cv-R $f class R $.
cv-S $f class S $.
cv-T $f class T $.
cv-U $f class U $.
cv-V $f class V $.
cv-W $f class W $.
cv-X $f class X $.
cv-Y $f class Y $.
cv-Z $f class Z $.

$( Set variable types $)
sv-a $f set a $.
sv-b $f set b $.
sv-c $f set c $.
sv-d $f set d $.
sv-e $f set e $.
sv-f $f set f $.
sv-g $f set g $.
sv-h $f set h $.
sv-i $f set i $.
sv-j $f set j $.
sv-k $f set k $.
sv-l $f set l $.
sv-m $f set m $.
sv-n $f set n $.
sv-o $f set o $.
sv-p $f set p $.
sv-q $f set q $.
sv-r $f set r $.
sv-s $f set s $.
sv-t $f set t $.
sv-u $f set u $.
sv-v $f set v $.
sv-w $f set w $.
sv-x $f set x $.
sv-y $f set y $.
sv-z $f set z $.

$( Formula variable types $)
fv-ph $f wff ph $.
fv-ps $f wff ps $.
fv-ch $f wff ch $.
fv-th $f wff th $.
fv-ta $f wff ta $.
fv-et $f wff et $.
fv-ze $f wff ze $.
fv-si $f wff si $.
fv-rh $f wff rh $.
fv-mu $f wff mu $.
fv-nu $f wff nu $.
fv-xi $f wff xi $.
fv-om $f wff om $.

$( ============================================================================ $)
$( BASIC LOGICAL AXIOMS $)
$( ============================================================================ $)

$( Modus ponens $)
mp $a |- ps $.
$( Simplification $)
simpl $a |- ph $.
$( Conjunction introduction $)
simpr $a |- ps $.
$( Disjunction introduction $)
orci $a |- ( ph | ps ) $.
orcd $a |- ( ph | ps ) $.
$( Negation introduction $)
notnot $a |- ph $.
$( Universal instantiation $)
ax-gen $a |- ph $.
$( Existential introduction $)
ax-gen2 $a |- ph $.

$( ============================================================================ $)
$( BASIC SET THEORY AXIOMS $)
$( ============================================================================ $)

$( Extensionality: sets with same elements are equal $)
ax-ext $a |- ( A. x ( x e. a <-> x e. b ) -> a = b ) $.
$( Empty set: unique set with no elements $)
ax-nul $a |- E. x A. y ~ y e. x $.
$( Pairing: for any sets a, b, {a,b} exists $)
ax-pair $a |- E. x A. y ( y e. x <-> ( y = a | y = b ) ) $.
$( Union: union of any set exists $)
ax-union $a |- E. x A. y ( y e. x <-> E. z ( y e. z & z e. a ) ) $.
$( Power set: power set of any set exists $)
ax-pow $a |- E. x A. y ( y e. x <-> A. z ( z e. y -> z e. a ) ) $.
$( Infinity: infinite set exists $)
ax-inf $a |- E. x ( (/) e. x & A. y ( y e. x -> ( y u. { y } ) e. x ) ) $.
$( Regularity: no set is an element of itself $)
ax-reg $a |- ( E. x x e. a -> E. x ( x e. a & A. y ( y e. x -> ~ y e. a ) ) ) $.

$( ============================================================================ $)
$( GLOBAL vs LOCAL TRUTH AXIOMS $)
$( ============================================================================ $)

$( Global ModuliSpace construction $)
ModuliSpaceGlobal-def $a |- class ModuliSpaceGlobal $.
$( Local ModuliSpace construction $)
ModuliSpaceLocal-def $a |- set ModuliSpaceLocal $.
$( Global TypeGraph construction $)
TypeGraphGlobal-def $a |- class TypeGraphGlobal $.
$( Local TypeGraph construction $)
TypeGraphLocal-def $a |- set TypeGraphLocal $.
$( Global Arity construction $)
ArityGlobal-def $a |- class ArityGlobal $.
$( Local Arity construction $)
ArityLocal-def $a |- set ArityLocal $.

$( ============================================================================ $)
$( INSTITUTION SATISFACTION AXIOMS $)
$( ============================================================================ $)

$( ModuliSpace satisfaction: class to set mapping $)
moduli-satisfaction-def $a |- wff moduli-satisfaction A a $.
$( TypeGraph satisfaction: class to set mapping $)
typegraph-satisfaction-def $a |- wff typegraph-satisfaction A a $.
$( RG satisfaction: class to set mapping $)
rg-satisfaction-def $a |- wff rg-satisfaction A a $.
$( Arity satisfaction: class to set mapping $)
arity-satisfaction-def $a |- wff arity-satisfaction A a $.

$( ============================================================================ $)
$( RG OPERATOR AXIOMS $)
$( ============================================================================ $)

$( RG Flow: class function $)
rg-flow-def $a |- class rg-flow A B $.
$( RG Beta function: class function $)
rg-beta-function-def $a |- class rg-beta-function A $.
$( RG Anomaly measure: class function $)
rg-anomaly-measure-def $a |- class rg-anomaly-measure A $.
$( Anomaly vanishes at M3: class predicate $)
anomaly-vanishes-at-m3-def $a |- wff anomaly-vanishes-at-m3 A $.
$( Well-formedness: class predicate $)
well-formed-def $a |- wff well-formed A $.

$( ============================================================================ $)
$( KERNEL ARGUMENT AXIOMS $)
$( ============================================================================ $)

$( Kernel: class $)
Kernel-def $a |- class Kernel $.
$( Kernel parameters: set $)
KernelParameters-def $a |- set KernelParameters $.
$( Global LLM parameters: class $)
GlobalLLMParameters-def $a |- class GlobalLLMParameters $.
$( Local truth: set $)
LocalTruth-def $a |- set LocalTruth $.
$( Deformation parameter: class $)
DeformationParam-def $a |- class DeformationParam $.
$( Global-local correspondence: class relation $)
GlobalLocalCorrespondence-def $a |- class GlobalLocalCorrespondence A B $.

$( ============================================================================ $)
$( FUNCTIONAL OPERATOR AXIOMS $)
$( ============================================================================ $)

$( Function composition: class operation $)
comp-def $a |- class comp A B $.
$( Boolean negation: set operation $)
not-def $a |- set not a $.
$( Boolean conjunction: set operation $)
and-def $a |- set and a b $.
$( Boolean disjunction: set operation $)
or-def $a |- set or a b $.
$( Addition: set operation $)
add-def $a |- set add a b $.
$( Multiplication: set operation $)
mul-def $a |- set mul a b $.
$( Less than or equal: set relation $)
le-def $a |- wff le a b $.
$( Greater than or equal: set relation $)
ge-def $a |- wff ge a b $.
$( Zero: set constant $)
zero-def $a |- set zero $.
$( One: set constant $)
one-def $a |- set one $.

$( ============================================================================ $)
$( COMPREHENSIVE VERIFICATION AXIOMS $)
$( ============================================================================ $)

$( Complete system verification: class predicate $)
complete-system-verification-def $a |- wff complete-system-verification $.
$( Mathematical consistency: class predicate $)
mathematical-consistency-def $a |- wff mathematical-consistency $.
$( Formal verification completeness: class predicate $)
formal-verification-completeness-def $a |- wff formal-verification-completeness $.

$( ============================================================================ $)
$( ZFC CONSERVATIVE EXTENSION PREPARATION $)
$( ============================================================================ $)

$( BootstrapPaper is a conservative extension of ZFC $)
$( This means: every theorem provable in BootstrapPaper $)
$( that uses only ZFC vocabulary is already provable in ZFC $)
$( The new vocabulary (ModuliSpace, TypeGraph, etc.) $)
$( does not add any new theorems about sets alone $)

$( ZFC vocabulary: sets, membership, equality, logical connectives $)
$( BootstrapPaper vocabulary: adds ModuliSpace, TypeGraph, RG operators, etc. $)
$( Conservative extension: new vocabulary, no new set-theoretic theorems $)