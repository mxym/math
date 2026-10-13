# All-rate Jacobians and exact multiplicities at an arbitrary leak site

Yongxian Zhang (张永贤)
School of Computer Science and Engineering, South China University of Technology
mxymmxym1@gmail.com; ORCID 0009-0000-3864-3536

This note explains the final alternate-leak polynomial extension of the
[Lean theorem core](../../formalizations/hydrology-tree-core/README.md).
It gives a proof for the actual finite tree model and every real parameter
vector. Historical priority is a separate question; the note does not equate
formal verification with novelty, empirical validation or human peer review.

## 1. Objects and coordinate convention

Let G be a finite labelled simple tree with N vertices. Fix an observation and
input vertex o, and a possibly different leak vertex ell. There is one real
rate in each direction of every edge, and one real external leak lambda at ell.
The matrix A has these off-diagonal transfers; its diagonal is minus the total
rate leaving each compartment, including lambda only at ell. The rates are
initially arbitrary real numbers: positivity is not a premise of the theorem.

Let P(s)=det(sI-A) and let F_o(s) be the original principal cofactor obtained by
deleting o from sI-A. The original diagonal entries are kept in that principal
block. Both polynomials are monic, of degrees N and N-1. The coefficient map
C_(o,ell) returns their non-leading coefficients. In the implementation their
ascending coefficient order is transported by a fixed, explicitly proved linear
coordinate permutation to the original leak-plus-dart parameter space.
J_(o,ell) denotes the determinant of the actual Frechet derivative in this
convention. The symbolic determinant is independently defined from formal
partial derivatives of the actual characteristic/cofactor coefficient polynomials.

Root G at the observer o. For each nonroot vertex v write N_v for the number
of vertices of its descendant subtree T_v. On its edge to its parent, a_v is
the rate toward o and f_v is the opposite rate. Write t_v(ell) for the rate
on this same edge directed toward the leak. This direction is defined by a
second, proved leak-root presentation of the same labelled graph.

For every observed-root child subtree, use the characteristic polynomial of the
ACTUAL principal block of A; do not recompute a closed-system diagonal for it.
Let S_(o,ell) be the product over all vertices of the squared pairwise resultants
of their child-subtree characteristic polynomials. All these are polynomial
functions of the original graph rates.

## 2. The full polynomial identity

There is a sign epsilon_o in {+1,-1}, depending only on the fixed observation
coordinate convention, such that for every leak site and every real rate vector,

    J_(o,ell) = epsilon_o * product_(v != o) t_v(ell)
      * product_(v != o) (a_v*f_v)^(N_v-1) * S_(o,ell).

The SAME sign works simultaneously for every ell and every vector. This is both
an equality in the multivariate polynomial ring and the actual Frechet Jacobian
identity after any real specialization. Zero rates, zero lambda, common roots,
signed values and the one-vertex case are included.

The key formal entries are `formalLocatedJacobian_factorization`,
`formalLocatedJacobian_coordinate_factorization`, `formalLocatedJacobian_evaluate`,
and `finite_graph_complete_all_leak_algebra`. The independent graph theorem
constructs the required root presentations from G.IsTree and its finite cardinality.
It does not ask the user to provide a parent numbering as an additional premise.

## 3. Exact multiplicities and the complete boundary zero set

For either directed rate d on an observed-root edge at v, its exact multiplicity
in the formal Jacobian polynomial is

    N_v - 1 + indicator(d is directed toward ell).

The external leak coefficient lambda has multiplicity zero. Every displayed
power divides the actual formal determinant and the next power does not. In
particular this is stronger than exhibiting a factorization with a possibly
still-divisible residual. When ell=o, the inward and outward exponents are
respectively N_v and N_v-1, as in the original root-leak theorem.

The entire real Jacobian zero set is therefore exactly the union of: a zero
coordinate having positive displayed exponent, and the zero set of the actual
sibling resultant residual. There is no exceptional omitted zero-leak locus.
For signed models the residual statement is algebraic; it must not be silently
replaced by a positive-model assertion about exclusively real spectra.

Formal entries: `formalLocatedJacobian_emultiplicity`,
`formalLocatedJacobian_exact_power`, `located_inward_multiplicity`,
`located_outward_multiplicity`, `located_leak_variable_not_dvd`, and
`locatedJacobian_zero_iff_all_rates`.

## 4. Proof of the identity: remove the rational transformation first

The previous positive-rate relocation theorem constructs a diagonal similarity
moving the leak from ell to o without moving the observer. Its differential is
proved, and its determinant gives

    lambda_old * J_(o,ell)(y) = lambda_new * J_(o,o)(R(y)).

No coefficient Jacobian is assumed nonzero here; positive spectral collisions
are included. The observation-root theorem factors J_(o,o) as its fixed sign,
one inward rate per edge, and an invariant core weight.

The core weight is the product of the edge-product powers and the actual squared
principal sibling resultants. Diagonal similarity preserves each edge product
A_ij*A_ji. It restricts to a diagonal similarity on EVERY principal child block,
so it also preserves all their characteristic polynomials and resultants.
Induction proves invariance of the full observed-root core weight, not only the
full matrix characteristic polynomial.

The inward-rate product in the root-leak formula is exactly the root cofactor
at s=0. More generally, with any leak-root presentation, elementary physical
conservation and the proved tree recursion give

    P(0) = lambda * F_ell(0),
    F_ell(0) = product_(edges directed toward ell) rate.

These identities already hold for all real parameters, including lambda=0.
They are proved by transport to the actual leak-root tree, not by importing an
unformalized matrix-tree theorem.

For positive parameters, combining them with the relocation derivative removes
all transformed rates and denominators:

    J_(o,ell)(y) = epsilon_o * F_ell(0) * coreWeight(A(y)).

Every quantity on both sides is now a multivariate polynomial. The formal
partial-derivative determinant is proved to evaluate to the actual Frechet
Jacobian at ALL real vectors, with differentiability independently established.
Equality on the product of positive real half-lines implies equality of the
polynomials, by the proved infinite-sided-box extensionality theorem. Therefore
the identity extends to every signed and zero-boundary specialization. This
argument does not divide by a zero rate or assume that the positive orthant is
dense in the whole real parameter space.

Finally, the actual recursive edge weights are flattened to the original
observed-root edge set. The leak-root cofactor supplies exactly one factor for
each edge directed toward ell. This yields the displayed formula and its exact
sign convention.

## 5. Why the residual has no hidden coordinate factor

Fix any original rate coordinate, including the external leak. Construct a
witness using the leak-root presentation: set every rate pointing away from ell
to zero, and choose the leak and the inward rates to be injective real numbers.
The resulting actual physical matrix is triangular in that leak-root ordering,
with pairwise distinct diagonal entries.

The observation-root principal sets need not follow the same ordering. For ANY
injective principal enumeration, however, pull back the leak-root rank order.
This is a proved linear order; the principal matrix is triangular in it, and its
characteristic polynomial is the product of its actual diagonal linear factors.
Different observed sibling subtrees contain disjoint original vertices, so their
factor sets are disjoint. Their characteristic polynomials are coprime. Repeating
at every depth shows S_(o,ell) is nonzero.

This construction can put any selected coordinate exactly on its zero hyperplane.
An outward-from-leak rate is already zero. For an inward-to-leak rate, choose the
injective values as a_i=i-j, where j is the selected vertex. For lambda, choose
j to be the leak root. All diagonal values remain distinct; negative values are
allowed because these are algebraic witnesses, not claimed positive experiments.

Thus every coordinate hyperplane contains a point where the residual is nonzero.
If that coordinate variable divided the residual polynomial, evaluation at the
constructed point would force zero, a contradiction. This proves polynomial
nondivisibility for every coordinate of every finite tree and every leak site.
The primeness of individual multivariate variables then gives the exact finite
multiplicities of the displayed monomial, including the exclusion of the next
power. No finite table of test models substitutes for these quantified proofs.

## 6. Semantic and verification boundaries

The result concerns collocated input/state observation at o and one external
leak at ell. State observation at o is not asserted equivalent to measuring
outflow at a different leak vertex. The separate co-located discharge theory and
continuous-input ODE bridges remain the distinct statements given in the theorem
core. Nonlinear catchments, noisy inference, nonnegative-only arbitrary steering,
and fewer-mode or complex-parameter fiber enumeration are not covered by this
polynomial theorem.

The source modules are individually compiled. The exact source checkpoint's
independent fresh Lake build, separate source compilation, complete axiom audit,
empty-kernel trust-level-zero replay, deliberate false mutations and literal
logs are required before labelling those bytes independently verified. Historical
receipts and development caches do not certify a new revision. The mathematical
proof graph and scope are documented with the code; immutable historical versions
are not modified.

No external funding; AI-assisted research and formalization. Existing repository
and third-party notices remain in force. Original additions retain all rights
not otherwise granted by an applicable existing license.
