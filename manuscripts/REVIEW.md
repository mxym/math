# Proof review and verification boundaries

This is a review by the repository's AI research agent, not external human peer
review. It distinguishes proof inspection from formal kernel checks, exact
certificate replay, and finite diagnostic experiments. Full proof sources are
provided so that readers can inspect assumptions rather than trust this list.

## Sharp simplex

The integrated proof explicitly derives the facet/pyramid and cone-law
normalizations; translation is an elementary operation in lifted determinants.
The centered-law witness also covers singular bases. The volume-weighted
selection retains the indicator of nonsingular tuples and does not assume a
minimum exists for a ratio at degeneracy. The metric clipping step uses a
separate support-diameter bound. Actual cone laws, rather than arbitrary-law
examples, supply the convex-body conversion.

The intrinsic norm argument uses the centroid of the prescribed maximum
simplex, preserves that maximum throughout, and tracks all strict denominators.
The endpoint `e=1/H` satisfies them; zero deficit is covered. Projection errors
are relative to the enclosing simplex. The cap bootstrap applies to every
maximum simplex, including nonunique maxima. The truncation appendix proves
the classification of all maximum simplices, not just vertex simplices, and
gives a Banach--Mazur lower bound allowing free translation. The sharp exponent
and every-maximum constant obstruction follow from these actual convex bodies.

The two full Lean packages prove the earlier sharp exponent upper theorem
and the existential truncation sharpness target. The manuscript's all-maxima
classification, best-maximum and free-translation Banach--Mazur conclusions
have complete written proofs, with no claim that the one lower Lean target
contains all those stronger assertions. The packages do not formalize the improved quadratic
constant. Its full traditional proof is now in one manuscript. Floating
constant diagnostics are supplementary; the `4096 d^2` bound is established by
the elementary induction in the text. The optimal dimension order remains open.

## Continuum avoidance

The fixed family is chosen before the avoiding set; exponents, coefficients,
centers and remainders vary afterward. It is not a single set for all possible
families. Dyadic occupied-bin gaps and nonzero leading coefficient are required.
The proof includes boundary strata in the finite parameter representatives,
conditions on all exposed center selectors, and does not treat dependent tree
routes as independent. The window and error buffer are scheduled together.
The missed-center set is closed by compact projection, and open repair handles
those centers using sufficiently small samples. Distinct missed values follow
from the nonzero leading term, without an injectivity assumption on the map.
Partial-domain and total-function formulations have the same tail values.

The main endpoint has a full Lean proof. The auxiliary mechanism obstruction
in the written paper is not claimed as a theorem of that Lean release. The
replay adapter supplies a pinned comment/string-aware `import all` scanner,
walks cached modules' imports and restores the pinned Mathlib Lake options
for missing external modules, without changing proof sources or kernel guards.
A successful
fresh build is required in addition to inventory checks; actual kernel replay
outcomes are recorded separately from historical review counts.

## Fractional spectrum

The signed bin proof assigns every non-anchor edge exactly once, so repeated
intersections do not create a hidden linearity assumption. The anchor extension
does not require the non-anchor edges to intersect each other. Greedy anchors
are disjoint, bounding the number of groups by the matching number. The finite
LP duality appendix supplies the optimization identity independently of any
solver. Nonempty edges, rank at least two, and singleton families are handled.

The lower constructions use exactly identified Wilson and Kahn inputs. The
common-rank lemma works at every sufficiently large integer rank, which is
needed for the matching allocation and diverging-matching limit. Private
padding preserves fractional values. The integer-boundary characterization
assumes uniformity; the strict-ramp characterization excludes its switch point.
Near-extremizers need not be globally near-linear before deletion; the example
demonstrating this is retained. The finite allocation formula is justified by
convexity on each unit interval and discrete balancing, not a sampled maximum.

Lean checks the stated finite incidence, extraction and anchor exports; it
does not establish the entire limiting frontier, classical design existence,
LP duality or all sharpness constructions. Finite rational checkers supplement
the complete written proof. Ryser and the general weighted nonuniform
Füredi--Kahn--Seymour conjecture remain outside these claims.

## Complex pencil

The matrix certificate covers every complex coefficient, with explicit
principal-minor and determinant identities. Polynomial interpolation has a
separate degree bound in every variable; testing its complete finite grid
therefore proves identities, not just sampled positivity. Analytic sign
conditions and all five sharp witnesses complete the norm proof. The zero-row,
monomial and rank-one cases belong to the endpoint equality classification.
That classification is not extended to every coefficient outside the lens.

All three-row marginal-preserving laws are parameterized before deriving the
exact amplification. Conditioning on independent nonidentical columns gives
the norm product, with matching witnesses. The proof is self-contained and
does not import the Bristiel--Caputo inequality as a premise. No full Lean proof
is claimed. The four-row part is a separate elementary Laplace/Cauchy argument.
It retains the rectangular two-row identities and all-column equality cases.
Pairwise deficits are averaged over all three row pairings. At the transition,
intersecting nonzero row supports force full support; constant pair products
then force the rank-one flat class. Otherwise the four supports are distinct
singletons. This closes every equality case. The four-row pencil norm concerns
real coefficients, and its tensor norm concerns the parity subfamily of laws.

## Orbital atom stability

The universal theorem handles nonfaithful and nontransitive actions, including
the zero tangent space. Conjugation averaging preserves marginal constraints,
and orbital moments determine the central matrix entries. The oscillation dual
uses ordinary finite LP duality with an explicit feasible bounded polytope.
Extremizers with positive objective have disjoint Jordan supports; otherwise
rescaling would improve the optimum. Rational small perturbations are genuine
probability laws, and left translation preserves the uniform-action marginals.

The two-subset proof treats both parities, the `n=4` boundary and `n=5` tie
explicitly, with matching analytic primal and dual witnesses. The three-subset
classification covers degrees 3--120. Its first 18 nontrivial certificates are
checked against every conjugacy class; the further 97 use a proved three-cycle
compression and exhaust all 1,489,083 feasible types. Independent
enumeration, class-size totals, positivity and primal--dual objective equality
are the finite proof obligations. The separate asymptotic proof bounds the dual
globally, including the near-identity endpoint where at least two vertices move,
and matches it by rational systems in every residue modulo four. Exact symbolic
determinant and leading-coefficient checks support the polynomial calculations;
the real-variable inequalities and eventual positivity are proved analytically.
The asymptotic is not inferred from a finite table.

The all-rank transfer argument works over formal series Q[t][[s]], whose
designated root is invertible, and discards long-cycle factors only beyond the
required degree. Feasible short-cycle types have residual size zero or at least
k+1. Only feasible orbitals enter divisions. The hierarchy uses an injective
inclusion matrix with its induction hypotheses checked. The Bernstein coupling
controls bad adjacent moved pairs and replacement collisions separately; it
does not establish the higher-rank sharp asymptotic conjecture. The four-subset
certificates cover every degree 11--50 and all feasible types at those degrees.
An exact all-degree formula remains outside the claims.

The checkers' Python assertions must remain enabled. The new launcher and
negative controls enforce that requirement. This line is not Lean-formalized.
