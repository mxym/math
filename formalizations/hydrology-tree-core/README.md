# Finite tree compartment models — formalized theorem core

The proof dependencies for the declared finite-tree theorem family are closed
in source, including the final all-real arbitrary-leak boundary Jacobian and
exact coordinate multiplicities. Verification of new source is checkpoint-
specific; the independent run and original artifact, not an earlier receipt,
certify the corresponding version. Scope exclusions are explicit in `GAPS.md`.

## Model and actual objects

A finite labelled bidirected tree has real rates in both directions on each edge
and one external leak. The inlet and state observer are collocated at o; the leak
may be at any ell. The actual conservative matrix, original principal submatrices,
characteristic/cofactor polynomials, real Frechet derivatives, formal multivariate
partial derivatives, resolvents and classical ODE trajectories are constructed.
No recursive surrogate or unproved main-theorem interface replaces these objects.
Independent finite SimpleGraph/IsTree hypotheses supply a proved enumeration;
an externally supplied parent presentation is not necessary in the exported
graph theorems. Original principal diagonals retain exit-to-parent rates.

Aggregate source entry: `import HydrologyTree`.
Exact statements: `FORMAL_THEOREMS.md`. Dependency map: `DEPENDENCY_MAP.md` and
`DEPENDENCIES.dot`. Mathematical and verification scope: `GAPS.md`.

## 1. All-rate Jacobian polynomial and exact multiplicities

Root the tree at the observer. For each observed edge e let N_e be the size of
its descendant subtree and let a_e,f_e be its two directed rates. Let L_ell be
the product containing exactly one rate from each edge, directed toward the
leak vertex. Let S_(o,ell) be the product of actual squared sibling resultants,
computed in the original observed-root principal subtrees. Then

    J_(o,ell) = epsilon_o * L_ell * product_e (a_e*f_e)^(N_e-1) * S_(o,ell).

The sign epsilon_o is proved to be +1 or -1 in the explicitly fixed coordinate
convention, and is independent of ell and ALL rate values. The identity holds
as an equality of multivariate polynomials AND as the determinant of the actual
Frechet derivative at every real vector. Zero rates, zero leak, repeated spectra
and the singleton tree are included; no final boundary value is divided out.

Each original dart variable has EXACT multiplicity N_e-1 plus one when directed
toward ell. The external leak variable has multiplicity zero. Uniform coordinate-
hyperplane witnesses prove that no hidden individual variable divides the sibling
residual. Every displayed power divides the formal Jacobian, and the next does
not. The complete zero set is exactly a zero variable with positive exponent
or a vanishing actual sibling residual. When ell=o the original inward/outward
exponents N_e and N_e-1 are recovered separately.

Main new entries:
`formalLocatedJacobian_factorization`, `formalLocatedJacobian_evaluate`,
`formalLocatedJacobian_coordinate_factorization`,
`formalLocatedJacobian_exact_power`, `locatedJacobian_zero_iff_all_rates`, and
`finite_graph_complete_all_leak_algebra`.

The original root-leak `full_tree_standard_jacobian`, exact signed
`full_tree_resultant_jacobian`, independent `formalTreeJacobian` and all-size
catenary monomial/multiplicity statements remain included. No generic numerical
rank computation substitutes for the polynomial identities or singular sets.

## 2. Complete unrestricted-real full-response classification

For an N-vertex tree and a normalized full target

    G(s) = sum_(i=1..N) w_i/(s+r_i),
    r_i positive and distinct, w_i positive, sum_i w_i=1,

every real realization is automatically strictly positive and regular. There
are no additional mixed-sign, zero-rate or singular real competitors with this
full target. Actual fibers are explicitly equivalent to recursive labelled pole
allocations, finite, and have cardinality

    (N-1)! / product_(original nonroot v) |T_v|.

All inductive existence, inverse, positivity, finiteness, surjectivity and counting
obligations are discharged. Labels are retained; internal pole permutations are
not double-counted and tree automorphisms are not quotiented. Original root
response equality recovers full coefficients, not assumed extra observations.
For co-located discharge, the unknown leak is recovered from the actual transfer.

The same exact state-response and continuous-history classification holds for
any prescribed leak site. The unknown-site model has N times the count, with
site/matrix injectivity proved so this is not a duplicated encoding. Positive
leak relocation preserves every collocated experiment, including actual
continuous-input histories, while distinct leak sites give distinct matrices.
Main entries include `realResponseRecursiveEquiv`,
`real_root_response_fiber_exact_card`, `real_discharge_fiber_exact_card`,
`finite_graph_all_real_leak_ODE_classification`, and the explicit site transports.

## 3. Actual ODE and system/control theory

For continuous real inputs, actual global classical solutions are constructed
and unique. Both directions of the transfer/history identification are proved;
explicit exponential probes prevent vacuous universal trajectory assertions.
Mass balance, original-coordinate Kalman nonsingularity, full state observability
on any nonempty open interval, and steering between arbitrary states in every
T>0 by a constructed continuous SIGNED control are proved. The integral Gramian
is proved positive before inversion. Minimum input energy is attained with an
exact cost and full equality classification. Graph and leak-site state maps
preserve the same inlet and observed coordinate, with no hidden input rescaling.

## Verification and reproduction

Fixed Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`.
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`; all transitive Git revisions
and dependency source blobs are checked against the locked manifest.

    bash fetch_cache.sh
    python3 reproduce.py --output-dir /tmp/tree-proof-independent-check

The output directory must be new. The script checks proof-input source hashes,
builds a fresh Lake tree with initially zero owned objects, separately compiles
all owned modules, audits every exported root, and replays the complete used
declaration closure into `mkEmptyEnvironment 0`, comparing root types and
universes. Only propext, Classical.choice and Quot.sound are allowed. No custom
mathematical axiom, sorry, admit, native_decide, unsafe mathematical dependency
or unchecked solver is accepted. False source mutations must be rejected.

Literal logs, hashes, dependency locks and deterministic verified-source archives
are in the exact checkpoint's GitHub Actions artifact and preserved verification
receipt. Development compilation is not independent replay or human peer review.
The new boundary extension compiled; its new independent CI must pass before
these new bytes are labelled independently verified. No historical-priority,
full hydrology-model breakthrough, completion Release or DOI is asserted here.

## Scope and provenance

Full-target enumeration does not enumerate fewer-mode or complex-rate fibers.
Nonnegative-rainfall-only arbitrary steering is not claimed. Input continuity,
collocation and the finite linear tree assumptions are not omitted. Observing
state at o is distinct from measuring outflow at a different leak ell. Nonlinear
catchments, field validation and superior predictions are outside these theorems.
See `GAPS.md` for exact boundaries and source-specific verification status.

Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology; mxymmxym1@gmail.com;
ORCID 0009-0000-3864-3536. No external funding; AI-assisted research.
Existing repository and third-party notices remain in force. Original additions
retain all rights not otherwise granted by an applicable existing license.


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
