# Proof scope and remaining external questions

## 1. Declared mathematical core: proof dependencies closed

The repository's finite labelled bidirected tree model has actual conservative
matrices, one external leak, a collocated scalar inlet/state observer, and
explicit real rate coordinates. The following mathematical chains are closed
in source, with independent verification always bound to the exact checkpoint.

- All-rate actual coefficient-Jacobian and independent formal partial-derivative
  polynomial factorization, signed resultant identity, exact coordinate
  multiplicities, and complete zero-boundary singular sets.
- All-real full-positive-Stieltjes target fibers: actual realization existence,
  automatic strict positivity of unrestricted real competitors, complete
  recursive allocation bijection and exact factorial/hook count; every counted
  model's actual coefficient Jacobian is proved regular.
- Independently presented finite SimpleGraph trees: root-preserving enumeration,
  actual vertex/rate/matrix/coefficient transports and original graph fibers.
- Actual classical ODEs for continuous real inputs: global existence/uniqueness,
  all-input zero-initial output equivalence and its converse, storage balance,
  finite-window trajectory observability, positive-horizon signed steering,
  and the exact minimum-energy formula with its equality condition.
- Every prescribed leak site and the unknown-site model: exact diagonal gauge,
  all-real automatic positivity, exhaustive actual response and continuous-ODE
  fiber classification, actual site/matrix injectivity, and non-identifiability
  from all collocated experiments. Solutions are constructed; universal history
  predicates are not allowed to be vacuous.

The final former dependency gap was the alternate-leak all-real polynomial at
zero boundaries and its exact coordinate factors. It is closed by
`finite_graph_complete_all_leak_algebra`, `formalLocatedJacobian_exact_power`,
and `locatedJacobian_zero_iff_all_rates`. The all-real derivative/polynomial
bridge and uniform no-hidden-factor witnesses are proved, not supplied as
assumptions. The same exact +/-1 sign works for every site and every real rate.
For an observed-root edge e, each dart has exponent |T_e|-1, with an extra one
precisely in the direction toward the leak. The external leak exponent is zero.

## 2. Explicit scope exclusions, not unproved inputs

The finite fiber enumeration concerns N-vertex models and N distinct positive
target poles with strictly positive normalized weights. Fewer-mode targets,
coincident target poles, and complex-parameter fibers are not enumerated here.
Their absence from a theorem is not an assumption that they have no solutions.

The ODE notion is for classical trajectories driven by continuous real inputs.
Measurable, impulsive or discontinuous forcing requires another solution notion.
Controls in the arbitrary-endpoint and minimum-energy theorems are signed.
Arbitrary endpoint steering by nonnegative rainfall alone is NOT claimed.

A collocated inlet/state observer at o is NOT the same data model as physically
measuring outflow at a different leaking vertex ell. The graph/site theory keeps
the observer fixed. Original co-located discharge theory is proved; no equality
of arbitrary off-diagonal transfer data or distinct output channels is asserted.

These are linear constant-rate finite tree results, not statements about all
nonlinear catchments, uncertain forcing, measurement noise or forecast accuracy.
Historical priority, research impact and external human peer review remain
separate from correctness of the formal mathematical statements.

## 3. Verification is source-specific

A clean Lake build, separate owned-source compilation, complete root audit,
empty-kernel trust-level-zero replay and all deliberately false mutations must
pass for the exact final source. Standard allowed axioms are only propext,
Classical.choice and Quot.sound. Development compilation or a previous source's
CI success is not substituted for the new independent verification.

At the source-writing checkpoint the final boundary modules have compiled.
The final independent run and its preserved artifact must be consulted before
calling those new bytes independently verified. No completion Release or DOI
is implied by this source-level scope update. Existing frozen versions remain
unchanged; any release must identify its own exact commit and scope.


## Extension: low-order all-node observations (2026-10-15)

`finite_tree_all_node_jet_classification` proves that ANY strictly positive
reference on a known finite tree, even with hidden modes or repeated spectra,
has exactly |V| unrestricted-real models with matching diag(A) and diag(A^2)
data across all vertices when the leakage site is unknown. There is exactly
one at each specified site. Every competing real vector is automatically
positive and the matrices are distinct. No full-mode target is assumed.

The fixed-site theorem requires only nonzero reference rates directed toward
the leak, and leaves the competing real vector unrestricted.
`constant_input_collocated_jet` proves that actual zero-initial constant-unit-
input outputs have second derivative A_vv and third derivative (A*A)_vv.
These are exact derivatives, not finite noisy samples or impulse observations.

The four new modules compiled in the isolated development compiler. Commit
75a87854 saved the files but did NOT register them in MODULES.json, the aggregate
import or audit roots: any run on that source certifies only the old 220-module
scope. This checkpoint explicitly adds all four modules, all their declarations,
source hashes and negative controls to the 224-module independent verification.
The old green status is NOT a certificate for the new files.

The actual whole-experiment classification, one redundant-coefficient removal,
and the mixed-input observation refinement remain subsequent extension tasks.
They are not hypotheses of the old completed core or of the new moment theorem.
