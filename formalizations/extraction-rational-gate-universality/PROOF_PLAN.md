# Full proof and pinned API map

All code in this package is an author proof; the separate historical independent
review is not a validation of these new files.

Let Q(a,b)=[[a,b],[-conj(b),conj(a)]]. Existing
`CircuitRecursion.su2_normalForm` and `su2_mass` say every U in actual matrix
SU2 has this form with normSq(a)+normSq(b)=1. The existing constructor
`quaternionSU2` creates exactly Q(a,b) from that mass equality.

For z in Circle define Z(z)=Q(z,0). For t in Circle define
X(t)=Q(Re(t),i Im(t))=[[Re(t),i Im(t)],[i Im(t),Re(t)]].
Tori.lean proves these maps are continuous homomorphisms, rather than treating
an abstract torus as an unverified stand-in for the actual matrices. The local
topological-group witness uses continuous matrix multiplication and inversion
as conjugate transpose. The theorem `ext_first_row` uses the actual normal
form to reduce matrix equality to the two first-row entries.

For arbitrary U=Q(a,b), set c=norm(a), d=norm(b), and t=c+i d. Mass gives
c^2+d^2=1, so t belongs to Circle. Define real phases
alpha=arg(a), beta=arg(-i b), and circle elements
s=Circle.exp((alpha+beta)/2), r=Circle.exp((alpha-beta)/2).
The addition law gives s*r=exp(alpha) and s*r^-1=exp(beta).
The first row of Z(s) X(t) Z(r) is
(c*(s*r), i*d*(s*r^-1)). The globally valid polar identity
norm(z)*Complex.exp(arg(z)*i)=z gives its first entry a. Applied to -i*b,
whose norm is d, it gives its second entry b. Thus U=Z(s) X(t) Z(r).

This proof never divides by a or b. In particular a=0 and b=0 need no
nonzero premise or omitted case. Principal arg is defined at zero; the polar
identity is valid there. The simultaneous equations for the phases are solved
by half-sum/half-difference: s^2=exp(alpha)*exp(beta). This supplies a square
root of the product phase without a complex-square-root branch hypothesis.
No continuity of this Euler choice is needed or claimed. Negative-real phases
and the principal-arg cut cause no problem, because only exact exp addition
identities are used, not an invalid equality arg(uv)=arg(u)+arg(v).

Let S be the algebraic subgroup closure of the actual four-gate range and let
H=S.topologicalClosure. H is a closed subgroup. The concrete gates of labels
0 and 2 equal Z(q) and X(q), where q is phaseCircle. Every integer power of
these gates lies in H. Homomorphism `map_zpow` and the already proved
DenseRange(n -> q^n) extend membership by closed-set induction to every Z(z)
and X(t). Euler and subgroup multiplication give every U in H. Therefore
closure(S)=univ, which is precisely the required Dense S statement.
The inverse labels are not needed for algebraic subgroup generation itself;
their existing concrete proof is used by the offline word-net corollary.

The code uses these exact pinned sources/APIs (line numbers at pin d13f23b7):

- Mathlib/Analysis/SpecialFunctions/Complex/Arg.lean:56,
  `Complex.norm_mul_exp_arg_mul_I`, with no z != 0 hypothesis.
- Mathlib/Analysis/Complex/Circle.lean:74/78/85/134,
  `Circle.norm_coe`, `normSq_coe`, `coe_inv_eq_conj`, `exp_add`;
  `exp_neg` is in the same file.
- Mathlib/Analysis/Complex/Norm.lean:149,
  `Complex.normSq_eq_norm_sq`.
- Mathlib/Topology/Instances/Matrix.lean:98, `continuous_matrix`.
- Mathlib/Topology/Constructions.lean:416, `Continuous.subtype_mk`;
  `continuous_induced_rng` gives the equivalent subtype continuity form used.
- Mathlib/Algebra/Group/Hom/Defs.lean:495, `map_zpow`.
- Mathlib/Algebra/Group/Subgroup/Defs.lean:474, `Subgroup.zpow_mem`.
- Mathlib/Topology/Algebra/Group/Subgroup.lean:40/51/55,
  `Subgroup.topologicalClosure`, `le_topologicalClosure`,
  `isClosed_topologicalClosure`.
- Mathlib/Topology/DenseEmbedding.lean:359, `DenseRange.induction_on`.
- Mathlib/Topology/Closure.lean:385, `dense_iff_closure_eq`.

The local repository inputs reused without editing are:

- extraction-circuit-recursion/CircuitRecursion/SU2Coordinates.lean:
  `su2_normalForm`, `su2_mass`.
- extraction-circuit-recursion/CircuitRecursion/QuaternionPlane.lean:
  `quaternionMatrix`, `quaternionSU2`.
- extraction-rational-gate-provider/RationalGateProvider/CircleDensity.lean:
  `phaseCircle_dense_zpowers`, proving actual Circle density.
- extraction-rational-gate-interface/RationalGateInterface/Library.lean:
  the actual rationalGate and rationalGate_inverse declarations.
- extraction-circuit-recursion/CircuitRecursion/PrecomputedNet.lean:
  `precomputedNet_exists`, deriving a fixed finite word table internally from
  the concrete inverse labels, matrix-group density and compactness.

No ready-made general SU2 Euler-angle theorem was found in the pinned
Mathlib search. The package proves the three-factor statement directly from
these small normal-form and polar APIs. This observation is not a novelty
claim about Euler decomposition or this known rational gate library.
