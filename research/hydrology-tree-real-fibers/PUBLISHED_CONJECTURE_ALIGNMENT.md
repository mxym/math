# Published-conjecture correspondence and scope audit

Audit date: 2026-10-13. This is a theorem-correspondence check, not a historical
priority certificate or external human peer review. The new arbitrary-leak result
is stated in ALTERNATE_LEAK_JACOBIAN.md; the previously formalized collocated-leak
specializations are located below.

## Primary sources checked

[1] E. Gross, N. Meshkat, A. Shiu, Identifiability of linear compartmental models:
the singular locus. Advances in Applied Mathematics 133 (2022), 102268.
DOI 10.1016/j.aam.2021.102268. Author version arXiv:1709.10013v3 (2021-06-28),
full HTML: https://arxiv.org/html/1709.10013 . Relevant statements: Definition
2.4, Definitions 2.8–2.9, Remark 2.10, Conjectures 5.5 and 5.9, Proposition 6.2.

[2] S. Ahmed et al., Identifiability of Directed-Cycle and Catenary Linear
Compartmental Models. SIAM Journal on Applied Dynamical Systems 25(1) (2026),
304–350. DOI 10.1137/25M1728636. Published online 2026-01-28. Publisher HTML:
https://epubs.siam.org/eprint/IXIEMIECP3TISXXACWXU/full . Its closing discussion
still identifies resolving [1, Conjecture 5.5] as a future direction. That
statement describes this source, not a proof that no subsequent resolution exists.

Both sources were read as HTML. No external published result is added as a Lean
axiom or silently inserted into the mathematical dependency chain.

## 1. Actual mathematical object

The correspondence with [1] is exact on the following points: bidirected finite
tree, scalar inlet and state observer in the first compartment, sole leak there,
column-conservative compartment matrix with the leak subtracted on the diagonal,
and the coefficient map of the unreduced characteristic/root-cofactor pair.
The fixed monic leading coefficients are omitted from the square coordinate map.
Reordering the remaining coefficients and rates changes its determinant only
by sign. The paper explicitly permits that sign convention.

The implementation uses vertices 0,...,n for N=n+1 compartments. For a path,
edge index e=0,...,n-1 connects paper vertices i=e+1 and i+1. Its inward rate
`x.1 e.succ` is the paper's a_(i,i+1), its outward rate `x.2 e` is a_(i+1,i),
and `x.1 0` is a_(0,1). Both descriptions use the actual generator and its
original principal minor, not the denominator of a separately reduced fraction.

## 2. Catenary formula

`catenary_standard_formal_polynomial` proves a fixed sign times

    product_(e=0..n-1) inward_e^(n-e) * outward_e^(n-e-1)

for the formal derivative determinant of the actual path coefficient polynomials.
With N=n+1 and i=e+1 this is

    product_(i=1..N-1) a_(i,i+1)^(N-i) * a_(i+1,i)^(N-i-1).

Grouping equal exponents gives precisely the monomial in [1, Conjecture 5.5].
All rate values are included; there is no positivity or genericity premise in
this polynomial theorem. At N=2 the outward exponent is zero, giving only the
inward rate as the monomial. The full proof is not inferred from small paths.

The main Lean entry is in HydrologyTree/CatenaryFormalPolynomial.lean. The
independent actual Frechet/formal-partial-derivative bridge is in
HydrologyTree/FormalTreePolynomial.lean.

## 3. Tree multiplicity procedure

Let s_v be the vertex count of the actual observed-root descendant subtree at v.
Our exact inward and outward multiplicities are respectively s_v and s_v-1.
Since s_v=1+sum_(children w of v) s_w, these satisfy both recursive rules of
[1, Conjecture 5.9], with the stated leaf initializations. The paper attributes
that procedure and conjecture to Molly Hoch, Mark Sweeney and Hwai-Ray Tung.

The correspondence needs EXACT multiplicity, not merely divisibility by a
candidate monomial. `formalTreeJacobian_exact_powers` proves divisibility by
the displayed power and nondivisibility by the next. Its specific inward and
outward theorems are in HydrologyTree/FormalTreePolynomial.lean. The hidden-factor
exclusion is proved in the actual multivariate residual, using uniform coordinate
hyperplane witnesses. The same-root specializations in
HydrologyTree/LocatedExactMultiplicities.lean recover these exponents independently
from the broader arbitrary-leak formula.

Thus the formal theorem statements mathematically imply the two conjecture
statements under their actual parameter conventions. This implication is distinct
from asserting that the present work is their historically first proof.

## 4. What the arbitrary-leak extension adds

The new theorem allows any leak site ell, on the same independently presented
finite labelled graph, with the input and state observer still collocated at o.
Its exact exponent on either dart of an observed-root edge v is

    s_v-1 + indicator(dart points toward ell).

It also gives the complete actual sibling-resultant residual, an all-real
polynomial identity, uniform exact multiplicities and the full zero-boundary
singular set. The original leak-site convention is recovered by setting ell=o.
This is an extension of the displayed root-leak statements; it is not a claim
to solve directed-cycle or multiple-input/output conjectures from [2].

## 5. Novelty and interpretation limits

A targeted search for later catenary/tree singular-locus proofs found the sources
above and their cited literature, but no search can establish historical priority
by absence of an exact retrieved match. Separate comparison of unpublished or
less-indexed work remains appropriate before a first-proof assertion.

The classical realization counts mentioned in [1, Proposition 6.2] are explicitly
prior art, not new consequences to rebrand. Our complete all-real full-positive-
target count, automatic positivity and actual ODE classification must likewise
be compared under their exact hypotheses with the older realization literature.
A kernel certificate establishes the checked statements, not novelty or impact.

The singular set in these theorems is where the actual coefficient Jacobian drops
rank. It must not be indiscriminately identified with every possible notion of
local uniqueness at a singular point, or with numerical ill-conditioning under
noise. Such extensions are not asserted by this correspondence audit.

Author: Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology; mxymmxym1@gmail.com; ORCID 0009-0000-3864-3536.
No external funding; AI-assisted research. Existing repository and third-party
notices remain in force.
