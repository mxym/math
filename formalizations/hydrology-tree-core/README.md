# Tree compartment identifiability — verified core, partial overall program

The actual all-tree coefficient-Jacobian factorization, exact algebraic
multiplicities, positive spectral characterization and full-response realization
theorems are proved in Lean. The exhaustive recursive classification and exact
count now cover **ALL REAL realizations** of a full positive Stieltjes target:
positivity and Jacobian regularity are conclusions, not restrictions imposed on
the competitors. The overall program remains **PARTIAL** for independent graph
presentations, alternate leak location and actual ODE/system bridges.

## Actual model and main theorem scope

`OrderedTree n` has n+1 original labelled vertices, with one strictly lower-numbered
parent for each nonroot vertex. Input, observation and the sole leak are at root
0. `TreeRates n` contains the root leak and both directed rates on each edge.
`compartmentMatrix` is the actual edge-conservative matrix, not an assumed
recursive surrogate. Characteristic polynomials, root principal cofactors,
subtree sizes, resolvents and all coefficient maps are built from that matrix.
Original boundary-exit diagonals are retained in every principal subtree.

No custom mathematical axiom, missing-theorem interface, sorry, admit,
native_decide, unsafe mathematical dependency or unchecked solver is allowed.
Main aggregate entry: `import HydrologyTree`.

## Exact algebraic and local identifiability results

`full_tree_standard_jacobian` proves, for each finite tree T, one fixed sign
ε in {1,-1}, independent of all rates, such that simultaneously for all real x:

    det D C_T(x) = ε * product_(nonroot v) a_v^N_v f_v^(N_v-1)
      * product_(vertices u) product_(sibling pairs v<w at u) Res(P_v,P_w)^2.

C_T is the ACTUAL characteristic/cofactor coefficient map in standard ascending
coefficient bases and D denotes its actual Frechet derivative. N_v and P_v are
the size and original principal characteristic polynomial of the actual subtree.
Zero rates, zero root leak, repeated roots and zero resultants are included.

`full_tree_resultant_jacobian` proves the signed all-rate identity

    Res(P_T,F_T) = ε_T * product_e f_e * det D C_T.

`formalTreeJacobian` is independently defined by formal partial differentiation
of the actual multivariate coefficient polynomials. Its evaluation, exact
polynomial factorization and all individual-rate multiplicities are proved,
including absence of any hidden coordinate factor in the sibling residual.
`catenary_standard_formal_polynomial` gives the all-size endpoint-path monomial.

The full real boundary singular set, positive sibling spectral-collision
criterion and full distinct positive-mode criterion are proved. Grounded energy,
detailed balance, real negative spectrum, Stieltjes representation and exact
polynomial cancellation are genuine dependencies, not assumed external inputs.
Zero-rate cancellation is not conflated with a singular unreduced coefficient map.

## Complete full-response classification and exact count

Let T have N=n+1 vertices, and let

    G(s) = sum_(i=1..N) w_i/(s+r_i),
    all r_i > 0 and distinct, all w_i > 0, sum_i w_i = 1.

`positive_tree_stieltjes_realization_exists` constructs a strictly positive
physical realization on every prescribed original tree. Reciprocal interlacing,
all numerator zeros, residue signs, complete polynomial reconstruction and child
assembly are proved from real analysis and exact algebra.

`positiveReciprocalFiberEquiv` establishes the exhaustive root-level bijection:
actual positive parent fiber ↔ labelled pole allocations with actual positive
child-fiber points. Both injectivity and surjectivity are proved.
`positiveStieltjesRecursiveEquiv` recursively gives the full bijection with
`RecursivePoleAllocations T`, a finite type depending only on the labelled tree.
Within-block pole enumeration is canonical and is not an additional counted choice.

`positive_stieltjes_fiber_exact_card` proves actual finiteness and

    card(fiber) = n! / product_(original nonroot v) |T_v|.

Integrality, original subtree counts and every inductive fiber obligation are
proved. The singleton tree is included. Original labels are retained; there is
no quotient by tree automorphisms. These are not counts of a candidate list.

`stieltjes_root_response_iff_polynomials` recovers both complete polynomials from
only the ACTUAL root resolvent on the common nonpole domain. The competing real
vector is not assumed positive or regular. `positive_root_response_fiber_exact_card`
therefore has the same count without extra internal coefficient observations.

## Stronger rigidity: every real realization is automatically positive

`real_stieltjes_realization_is_positive` proves that ANY real rate vector having
the prescribed full positive target pair is strictly positive in every original
coordinate, including the root leak. No sign, stability, nonzero-edge or Jacobian
premise is made about that vector. Each child polynomial is an actual monic
divisor of the simple split target numerator. Real factorization, exact recovery
of the normalized child cofactors and strong induction force the conclusion.

`realResponseRecursiveEquiv` classifies ALL real response realizations by the
same recursive allocation type. `real_root_response_fiber_exact_card` proves
that the entire real response fiber is finite with the same factorial count.
`real_full_response_forces_positive_regular` proves positivity AND nonzero
actual coefficient Jacobian. Thus there are no uncounted mixed-sign, zero-rate
or singular real models with this full positive response.

These theorems apply to full N-mode targets. Repeated-pole or fewer-mode targets
are not counted by this result. Complex parameter fibers, alternate leak placement,
ODE input histories and nonlinear catchments are not silently included.

## Actual root discharge and unknown leak

`physicalDischargeResponse` is the actual root leak times the actual root
resolvent. `equal_discharge_recovers_leak` derives the leak from discharge
transfer equality via the leading coefficients of an exact polynomial identity.
For the full positive target, `full_stieltjes_leak_identified` proves
ell = 1 / sum_i(w_i/r_i). This parameter is not assumed calibrated externally.

`stieltjes_discharge_iff_root_response` proves that the prescribed physical
discharge transfer and the normalized root response have the same unrestricted
real parameter fiber. `real_discharge_fiber_exact_card` proves the exact finite
factorial count for actual discharge observations. The independent ODE solution
and controllability bridges remain separate; transfer equality is not silently
called an all-input ODE proof.

A self-contained written explanation of the complete proof is available in
[the real-fiber research note](../../research/hydrology-tree-real-fibers/README.md).

## Reproduction and audit

Lean 4.34.1 (`5045d0056413266e57c625dcd7c365b10e377c52`), Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`; all transitive revisions are locked.

    bash fetch_cache.sh
    python3 reproduce.py --output-dir /tmp/tree-proof-independent-check

The output directory must be new. The script checks all proof-input hashes and
dependency sources, builds a fresh Lake source tree with zero owned objects,
separately recompiles every owned module, audits every declared root, and replays
the complete used declaration closure into `mkEmptyEnvironment 0`. Types and
universes are compared. Only propext, Classical.choice and Quot.sound are allowed.
Deliberately false source mutations must fail. Complete literal logs, before/after
source hashes and a deterministic verified-source archive are retained.

The positive-fiber and unrestricted-real extensions have compiled with exact
source hashes in the isolated development environment. Their source-bound
independent runs are separate. A previous success or development cache is NOT
presented as a new empty-kernel certificate. Consult the checkpoint-specific
receipts under `verification/` and the matching GitHub Actions run.

`FORMAL_THEOREMS.md` states the exact quantified mathematical scope.
`DEPENDENCY_MAP.md`, `DEPENDENCIES.dot` and `GAPS.md` record coverage and all
remaining obligations. No full-program completion Release or DOI is issued.
Historical-priority and external human peer-review claims are not made.

## Provenance

Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology; mxymmxym1@gmail.com;
ORCID 0009-0000-3864-3536. No external funding; AI-assisted development.
Existing repository and third-party notices remain in force. Original additions
retain all rights not otherwise granted by an applicable existing license.


## Actual continuous-input ODE bridge

`IsPhysicalForcedSolution` is the actual state equation z'=A_T(x)z+u e_0,
expressed by HasDerivAt at every real time. `physical_forced_ODE_existsUnique`
proves a unique global classical trajectory for every positive physical model,
every continuous real input and arbitrary initial state/time. The scalar solution
uses actual interval integration; all derivative and initial-value identities
are proved. `physical_root_modal_representation` constructs the complete modal
witness from the original matrix rather than assuming a representation.

`real_full_response_forced_ODE` discharges positivity from the previously proved
unrestricted-real response theorem and proves the unique actual zero-initial
trajectory and its prescribed time-domain root output. The competing real
parameters need no sign or regularity hypothesis. `same_full_response_all_continuous_inputs`
proves equality of actual root state and discharge for every continuous input,
including across two prescribed same-size tree topologies. Equality is not
limited to sampled histories or sinusoidal probes.

`physical_total_storage_hasDerivAt` proves d(sum z_i)/dt=u-ell*z_0 for ANY
classical physical trajectory and arbitrary real rates. Its integrated interval
balance and equality of storage under equal input/discharge are proved separately.

Scope is globally continuous real forcing with classical trajectories. The
reverse implication from equality of all time-domain outputs to transfer equality,
continuous-time reachability/observability, independent graph presentations and
alternate leak locations remain separate obligations. The new modules have
compiled locally; only their own subsequent source-bound CI certifies replay.


## Reverse ODE identification and exact continuous-output fibers

`matrixFlow` is the actual operator exponential of the real matrix linear map.
Its differential equation and Gronwall growth bound are proved for arbitrary
real matrices. `exponentialODEProbe` is an explicit zero-initial classical state
trajectory for the positive continuous input exp(q*t). After scaling by exp(-q*t),
it converges to the actual resolvent vector whenever q exceeds the operator norm.
No stability or positivity restriction is imposed on competing real matrices.

`same_continuous_outputs_cross_identity` recovers the actual transfer polynomial
identity from equality of zero-initial root outputs for every continuous input
at every nonnegative time. Explicit exponential solutions ensure that this
universal predicate is not used vacuously. Infinitely many nonpole probes, not
finite sampled verification, establish the polynomial identity.

`continuous_root_output_iff_response` proves BOTH directions between the actual
ODE behavior and the full Stieltjes root response, for unrestricted real rates.
`real_continuous_output_fiber_exact_card` now proves the finite exact factorial
count for actual continuous-input ODE output fibers. Positivity, regularity and
global classical well-posedness follow from the behavior; none is imposed as an
extra condition on the counted parameter vectors. The claim is for globally
continuous forcing and classical trajectories, not all measurable forcing.

The latest modules are checked by their own source-bound CI. Kalman/actual
reachability and observability, direct time-domain discharge-only inverse
identification, independent graph presentation and alternate leaks remain
separately listed obligations, not consequences silently assumed here.


## Actual discharge-history identification and trajectory observability

`same_continuous_discharge_leak` identifies the unknown leak from actual
zero-initial discharge histories, using actual exponential trajectories and
monic coefficient identities. `continuous_discharge_output_iff_response` proves
both directions between the continuous-input discharge behavior and the complete
Stieltjes root response, without imposing signs on real competing parameters.
`real_continuous_discharge_fiber_exact_card` proves the complete finite factorial
count for this actual ODE discharge-history fiber, not only a transfer function.

`rootKrylovMatrix` and `rootObservationMatrix` use actual powers of the original
matrix and actual root input/output. Their Vandermonde factorizations and
nonsingularity for every full-response real realization are proved, rather than
supplied as Kalman-rank assumptions. `actual_trajectory_observability` proves
that equal root outputs on ANY nonempty open interval and a common forcing
imply equality of complete actual classical state trajectories. No initial-state
equality is assumed. `real_full_response_trajectory_observable` discharges the
rank prerequisite from the full target response.

Finite-horizon steering by an actual continuous input is not inferred merely
from the Kalman determinant here; it remains a separate proof obligation until
its trajectory construction is checked. Broader forcing, independent graph
presentation and alternate leak location remain outside this checkpoint.


## Actual finite-horizon controllability

`ExponentialIndependence` proves independence of every finite family of distinct
real exponentials on ANY nonempty open interval, using actual derivatives and
the checked Vandermonde matrix. `ExponentialGramian` proves strict positivity
of the actual finite-horizon integral Gram matrix for EVERY T>0; no sampled
matrix, assumed Gramian invertibility or external control theorem is used.

`modalSteeringInput` explicitly constructs a finite linear combination of real
exponentials from the inverse of that proved positive Gramian.
`modalSteering_terminal` proves the exact terminal state of the actual interval-
integral solution. `real_full_response_controllable` then proves, for any full
response realization, ANY T>0 and ANY initial/final state vectors, existence of
a continuous real-valued input and its unique global classical state trajectory
with those endpoints. The actual physical matrix is used and its modal prerequisites
are constructed from the full target response, not assumed.

This is standard SIGNED-input linear controllability. No claim is made that
nonnegative rainfall alone can steer arbitrary states. Combined with the actual
finite-window observation theorem, both continuous-time system bridges are now
proved for the existing root-leak model. Independent graph presentations and
alternate leak locations remain separate variants.

The reproduction driver now supports symbolic-link dependency layouts without
changing any pinned revision or source-blob check. Earlier local setup failures
are distinct from completed proof checks; each receipt binds its own exact source.
