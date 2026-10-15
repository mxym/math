> Current scope update: the all-real alternate-leak Jacobian polynomial,
> exact original-coordinate multiplicities and complete zero-boundary criterion
> are now proved. Earlier descriptions of these tasks as pending are historical
> and are superseded by the final section below and the current GAPS.md. Each
> independent verification receipt applies only to its own exact source bytes.

# Mathematical scope of the proved tree Jacobian results

## Objects and conventions

Let `t : OrderedTree n`. There are n+1 compartments with root 0 and n
bidirected edges. Edge e joins its parent to vertex e+1. Its inward rate is
`x.1 e.succ = a_e`, outward rate `x.2 e = f_e`; the root leak is `x.1 0`.
The coefficient map is defined for every real rate vector, not only positive ones.

The actual compartment matrix A has off-diagonal entries
A_(parent,child)=a_e and A_(child,parent)=f_e. Its diagonal is the negative
sum of rates leaving that vertex, including the root leak. Each column sums
to zero except the root column, which sums to minus the leak.

Define P_T(X)=det(X I-A) and F_T(X) as the characteristic polynomial of the
root-deleted principal matrix. The original diagonal entries are retained
when taking principal submatrices. P_T and F_T are monic of degrees n+1 and n
at every rate vector. The coefficient map C_T consists of the ascending
non-leading P coefficients followed by the ascending non-leading F coefficients.
`treeCanonicalJacobian` is det of its actual Frechet derivative in these
standard coefficient bases and the standard physical rate-array basis.

## All-tree factorization and exact powers

For a nonroot vertex v, let m_v be its actual descendant subtree size, including
v. Every principal child subtree inherits its outgoing-to-parent rate as its
root leak. At every vertex, take the pairwise resultants of its actual child
characteristic polynomials, and let R_T be the product of their squares.

`full_tree_standard_jacobian` proves, for one sign epsilon_T fixed by the tree
and coordinate conventions, simultaneously at all real rate vectors,

    det D C_T = epsilon_T * product_(v != 0) a_v^m_v f_v^(m_v-1) * R_T.

The all-tree induction, independent child coordinates, original matrix
identification, coefficient reconstruction, arbitrary-family gluing, scaling,
root update and determinant normalizations are included in the proof chain.

`formalTreeJacobian` is a separate algebraic construction: first construct the
actual matrix with independent multivariate rate variables, then its actual
characteristic/cofactor coefficient polynomials, formally differentiate those
polynomials, and take the determinant. `formalTreeJacobian_evaluate` proves
that evaluating this determinant at any real rate vector gives det D C_T.
The multivariate evaluation derivative and the coordinate conjugacy are proved.

`formalTreeJacobian_factorization` is the factorization as an equality in the
multivariate polynomial ring. `formalTreeJacobian_exact_powers` proves both
X_j^m divides this polynomial AND X_j^(m+1) does not. Consequently

    multiplicity(a_v) = m_v,
    multiplicity(f_v) = m_v-1,
    multiplicity(root leak) = 0.

The residual has no additional individual-coordinate factors: for each
coordinate, a uniformly constructed rate vector sets it to zero while keeping
the actual sibling residual nonzero. Ring-valued matrix specialization turns
this into polynomial nondivisibility. This statement is about exact algebraic
multiplicity, not an estimated order of vanishing along a sampled curve.

For the endpoint path with n+1 stores, `catenary_standard_formal_polynomial`
specializes the determinant to the monomial

    epsilon_n * product_(e=0,...,n-1) a_e^(n-e) f_e^(n-e-1).

The outward leaf variable has exponent zero. Zero-rate specializations are
included throughout; no division by these variables is used in the theorem.

## Exact characteristic/cofactor resultant and boundary distinction

`full_tree_resultant_jacobian` proves a second tree-dependent fixed sign delta_T
such that, again for every real rate vector,

    Res(P_T,F_T) = delta_T * (product_e f_e) * det D C_T.

Its proof first establishes actual-degree monic resultant algebra (including
right-degree drops and zero numerators), the signed arbitrary-family numerator
formula, exact finite-family enumeration, and the physical root recurrence.
Strong induction then matches the resultant factorization to the actual
Jacobian, retaining every connector factor.

`physicalPair_coprime_iff_all_rates` therefore gives

    IsCoprime(P_T,F_T)
      iff every outward rate is nonzero and det D C_T is nonzero.

`treeJacobian_zero_iff_all_rates` separately characterizes the unreduced
coefficient-map singular locus as a zero inward rate, a zero outward rate at
a vertex with more than one descendant (including itself), or failure of
coprimality at some actual sibling family. Thus response cancellation at a
zero outward leaf rate must not be equated with a singular coefficient map.

## Remaining program

These results concern the actual rooted-parent model and its actual polynomial
and Frechet Jacobians. The overall program remains partial. In particular,
uniqueness for a prescribed recursive characteristic assignment does not prove
that every admissible assignment has a positive realization, or prove the
factorial count of all positive realizations. Reciprocal Stieltjes interlacing
and residue-sign reconstruction, exhaustive assignment realization and counting,
independent graph/leak-location presentations and the remaining ODE semantics
are the outstanding blocks listed in `GAPS.md`.

All verification statements refer to the exact source hashes and completed
independent receipts, not to development compiler statuses. A complete-program
Release or DOI is not asserted.

## Completed reciprocal analytic input

For any positive normalized Stieltjes data with n+1 distinct positive rates,
there exist n positive, distinct, strictly interlacing zero rates b_i and positive
g_i, and a real d, such that the actual input numerator F and denominator P obey

    F = product_i (X+b_i),
    P = (X+d) F - sum_i g_i product_(j != i) (X+b_j),
    d - sum_i g_i/b_i = P(0)/F(0) > 0.

Existence and simplicity of all zeros, residue signs, and the entire polynomial
identity are proved rather than imported as assumptions. Sorting preserves the
actual polynomials, so arbitrary injective positive input labels are covered.
The one-store case n=0 uses the empty product/sum identities explicitly.
This input closes the reciprocal interlacing/residue obligation but is not alone
a theorem that all positive tree assignments have been realized or counted.

## Completed global positive existence theorem

For every n≥0, every original parent-encoded rooted tree with n+1 stores, and
every n+1 distinct positive rates r_i with positive weights summing to one,
there exists a strictly positive physical rate vector x whose actual matrix
has characteristic P=product_i(X+r_i) and root cofactor
F=sum_i w_i product_(j!=i)(X+r_j). The exact root-resolvent response follows off
its poles. All smaller-child realization inputs are discharged by strong
induction; every ORIGINAL physical rate and the root leak are proved positive.

The same P,F can therefore be realized on any two specified same-size trees.
Existence and topology ambiguity are now complete for this model. Exhaustive
positive-fiber enumeration and its factorial count remain separate obligations.


## Root allocation extraction (partial fiber-classification step)

`positive_child_allocation_exists`: for every actual positive OrderedTree model
whose root cofactor is a product of n distinct real linear factors, there is a
labelled allocation of those pole indices with the actual child vertex counts,
and every actual child characteristic polynomial equals its allocated factor
product. `positive_child_allocation_unique` proves uniqueness.
`sizedAllocation_card_factorial` proves the exact finite allocation count. These
are not yet the full recursive physical parameter-fiber counting theorem.


## Complete actual positive fibers: exhaustive bijection and exact cardinality

Let T : OrderedTree n, r,w : Fin(n+1) -> R, with r injective, every r_i>0,
every w_i>0, and sum_i w_i=1. Let P=product_i(X+r_i) and
F=sum_i w_i product_(j != i)(X+r_j). `PositiveStieltjesFiber T r w` is exactly
{ x : TreeRates n | ALL inward rates including the root leak are positive,
ALL outward rates are positive, charpoly(A_T(x))=P, root cofactor(A_T(x))=F }.

`positiveStieltjesRecursiveEquiv` is an actual Lean equivalence from this set
to the complete recursive labelled pole-allocation type. It uses no assumed
classification, counting or smaller-model existence premise.

`positive_stieltjes_fiber_exact_card` proves BOTH that this actual set is finite
and that its cardinality equals n! / product_(e : Fin n) subtreeVertexCount(T,e.succ).
The original vertex labels and branch identities remain fixed. The quotient is
proved integral through `treeFiberDegree_mul_hook` and actual subtree recursion.

`HasStieltjesRootResponse T x r w` quantifies every real s where the ACTUAL
matrix (sI-A_T(x)) is invertible and every target denominator s+r_i is nonzero,
and requires the actual inverse entry (0,0) to equal sum_i w_i/(s+r_i).
`stieltjes_root_response_iff_polynomials` proves equivalence with the two full
polynomial equalities; the competing real vector is not assumed regular.
`positive_root_response_fiber_exact_card` gives the same finite exact count for
positive real vectors satisfying just this response condition.

`positive_stieltjes_fiber_regular` proves that the actual coefficient Jacobian
of EVERY counted positive model is nonzero. Regularity is not an extra condition
silently deleting positive solutions. The separate ODE and alternate-leak
variants remain outside these theorem statements.


## Automatic positivity and complete UNRESTRICTED REAL fiber classification

`RealStieltjesFiber T r w` has only the two actual polynomial equalities as
membership conditions. `RealResponseFiber T r w` has ONLY the actual root
resolvent equality on the common nonpole domain. Neither definition assumes
positive/nonnegative/nonzero rates, stable matrices, or nonsingular Jacobians.

Under the same full positive target hypotheses (distinct n+1 positive poles,
positive weights summing to one), `real_stieltjes_realization_is_positive` proves
ALL original directed rates and the root leak strictly positive. It uses the
real factorization of each monic child divisor of the target numerator, exact
child-cofactor recovery and a complete strong induction; no positivity theorem
or missing spectral claim is supplied as a hypothesis.

`realStieltjesFiberEquivPositive` preserves the actual rate vector in both
directions. `realResponseRecursiveEquiv` is a full equivalence from every real
root-response realization to RecursivePoleAllocations T.
`real_stieltjes_fiber_exact_card` and `real_root_response_fiber_exact_card`
prove actual finiteness and exact cardinality n! / product_(e) |T_(e.succ)|.
`real_full_response_forces_positive_regular` proves strict positivity and a
nonzero actual coefficient Jacobian for every real competitor with the specified
response. No real sign or regularity restriction is part of the counted set.

These statements concern real rate parameters on the existing root-leak
OrderedTree model. Complex fibers, nonroot leak variants and actual ODE
controllability/observability remain outside the formal theorem scope.


## Actual discharge transfer, leak identification and exact all-real fibers

`physicalDischargeResponse T x s` equals (x.1 0)*physicalRootResponse T x s.
`stieltjesLeak r w` is (sum_i w_i/r_i)^(-1), proved positive for the target class.
`equal_discharge_recovers_leak` recovers equal actual leaks from equal discharge
transfers on the common nonpole domain, using actual monic coefficient identities.
`stieltjes_discharge_iff_root_response` identifies the two unrestricted real
fibers WITHOUT an externally given leak. `real_discharge_fiber_exact_card` proves
that this actual discharge fiber is finite of cardinality n! / product_(e)|T_e|.
This is a rigorously proved matrix-transfer bridge; actual ODE solution and
system-theoretic controllability/observability statements are still separate.


## Actual classical ODE and continuous forcing

`IsPhysicalForcedSolution T x u z` means, for EVERY real time s,
HasDerivAt z (compartmentMatrix T x *v z(s) + u(s) * e_0) s.
`physical_forced_ODE_existsUnique` proves global existence and uniqueness for
arbitrary initial time/state and every continuous u whenever all physical rates
are strictly positive. It constructs modal coordinates from the actual weighted
symmetric generator and uses the actual interval-integral scalar solution.

`real_full_response_forced_ODE` assumes only the earlier full positive Stieltjes
TARGET hypotheses and actual root-response equality for the competing real
parameters. It concludes a unique classical zero-initial solution for every
continuous u and its exact root value sum_i w_i*scalarForcedSolution(r_i,u,a,0,s).
The sign and regularity of the competing parameters are derived, not presumed.
`same_full_response_all_continuous_inputs` compares actual solution outputs on
two prescribed topologies for every continuous input and initial time.

`physical_total_storage_hasDerivAt` and `physical_total_storage_integral_balance`
prove actual differential and integral mass balance, for arbitrary real rates
whenever a classical trajectory is given. No positivity or symbolic conservation
axiom is supplied. These are forward dynamical bridges, not yet the converse
identification theorem or a continuous-time reachability/observability theorem.


## Exact inverse identification from actual ODE root outputs

`HasFullContinuousRootOutput T x r w` quantifies every continuous real input u,
every actual global classical state solution with z(0)=0, and every real s>=0,
and requires the measured root coordinate to equal the prescribed forced
Stieltjes sum. It assumes no sign condition or existence assertion about x.
`continuous_root_output_iff_response` proves equivalence with the actual root
resolvent condition. Explicit exp(q*t) input solutions exist for every competing
matrix at the nonpole probes, ruling out any vacuous interpretation.

`RealContinuousOutputFiber` contains precisely the unrestricted real rate vectors
satisfying that ODE output property. Its actual finiteness and cardinality
n! / product_e subtreeVertexCount(T,e.succ) are proved in
`real_continuous_output_fiber_exact_card`. The observed output alone forces
positivity, the nonzero actual Jacobian, and unique global classical solutions
for arbitrary initial state and every continuous forcing, proved in
`continuous_output_forces_physical_wellposedness`.


## Actual discharge ODE histories, Kalman matrices and finite-window observation

`HasFullContinuousDischargeOutput T x r w` quantifies every continuous forcing,
every actual zero-initial classical trajectory, and every s>=0, observing only
ell_x*z_0(s). `continuous_discharge_output_iff_response` proves its equivalence
with the full root transfer property for every unrestricted real vector x.
`real_continuous_discharge_fiber_exact_card` proves actual finiteness and the
same exact n! / product(subtree sizes) cardinality, without a calibrated leak.

`rootKrylovMatrix A` has columns A^j e_0, j=0,...,n, and
`rootObservationMatrix A` has rows e_0^T A^j in the original coordinates.
`real_full_response_kalman_nonsingular` proves both determinants nonzero.
`actual_trajectory_observability` compares actual classical forced trajectories
z and q with the SAME input; if their root values agree throughout any Ioo(a,b)
with a<b and the observation matrix is nonsingular, then z=q everywhere.
`real_full_response_trajectory_observable` proves the needed determinant from
the full response. There is no assumption of equal initial states. This closes
trajectory observability, while actual finite-horizon steering still needs its
own existence construction beyond the already checked Krylov determinant.


## Actual finite-horizon state steering

`exponentialGramian r T` has entries integral_(0..T) exp(r_i*s)exp(r_j*s) ds.
`exponentialGramian_posDef` proves strict positivity for every injective real
r and every T>0. Actual finite exponential independence on open intervals is
proved first; a.e. vanishing of the nonnegative square integral is upgraded to
pointwise vanishing by continuity. No unproved Gramian input is assumed.

`modalSteeringInput` explicitly uses this inverse Gramian and the proved actual
modal maps to construct a continuous real-valued control. The exact original
ODE trajectory reaches the desired terminal state, as a checked integral identity.
`real_full_response_controllable` concludes that for any unrestricted real vector
realizing the full positive target, for EVERY T>0 and all z0,z1, there exists
continuous u and a UNIQUE global classical z satisfying the original state
ODE, z(0)=z0 and z(T)=z1. No controllability/Gramian/positive-rate condition is
supplied as an additional premise; all follow from the target and are proved.

This is signed-input linear controllability. Neither the control nor the whole
trajectory is constrained to be nonnegative. The theorem does not assert
arbitrary reachability using nonnegative rainfall inputs only.


## Actual minimum-energy continuous control

For every actual root-leak tree realization of a full normalized positive target,
every T>0 and every pair of state vectors z0,z1, there exists a globally continuous
real input u* with a unique global classical actual ODE trajectory through those
endpoints. For every OTHER continuous u and every actual trajectory z with
z(0)=z0 and z(T)=z1, `real_full_response_minimum_energy_control` proves:

    E(u)=E(u*)+E(u-u*), E(u*)<=E(u),
    E(u)=E(u*) iff forall s in [0,T], u(s)=u*(s),
    where E(v)=integral_(0..T) v(s)^2 ds.

The original matrix and actual HasDerivAt equation are used. The endpoint moment
constraints are derived in `actual_terminal_implies_moments`. No candidate input
family, assumed Gramian or unproved minimization interface replaces the full
quantifiers. `minimumEnergyInput_energy` proves the exact quadratic value d^T H^-1 d.
`modalMinimumEnergy_independent_of_witness` proves coordinate independence.
The continuous equality statement includes endpoints but deliberately imposes
nothing outside the energy interval. Signed inputs and real state vectors are
allowed; nonnegative-input reachability is not claimed.


## Independently presented finite graphs

For any finite vertex type V, SimpleGraph G, proof hG : G.IsTree, root o and
card V=n+1, `finite_rooted_tree_presentation` constructs an adjacency- and
root-preserving equivalence with an actual OrderedTree. `GraphRates G` is the
root leak together with a real number on every graph dart. Its physical matrix
is independently built from oriented transfers and column conservation.

`finite_graph_coefficient_jacobian` proves the all-rate factorization for the
actual graph characteristic/cofactor coefficient map in the explicit transported
basis. `finite_graph_full_response_classification` and
`finite_graph_continuous_fiber_classification` classify all actual real graph
rates realizing a full positive N-mode target, with finite exact factorial count
and automatic positivity. Presentations are constructed, not hypotheses.

`finite_graph_full_dynamical_properties` gives global classical well-posedness,
signed continuous steering in any T>0, and equality of entire state trajectories
from the same forcing and equal root output on any nonempty open time window.
`graph_full_response_minimum_energy` proves the exact energy decomposition and
control equality on [0,T] for endpoint-feasible continuous inputs.
`GraphMassBalance` gives the independently defined graph ODE's exact differential
and integrated storage balance. None of these changes the root-leak convention.


## Arbitrary-site positive leakage classification

For any finite SimpleGraph tree G, any fixed input/state observation o and any
leak sites u,v, `relocatePositiveLeak` is an equivalence of the ENTIRE positive
graph-rate spaces. `relocatePositiveLeak_similarity` constructs positive vertex
weights h for the actual identity A_v(E(y))=diag(h) A_u(y) diag(h)^(-1).
All graph rates and leakage positions are independent physical definitions.
`relocatePositiveLeak_response` proves characteristic/cofactor and every diagonal
resolvent invariant, with singular values only under the algebraic inverse
convention. The physical response predicates use actual nonpole domains.

`PositiveLocatedFiber o ell r w` explicitly requires strict positivity and the
actual root response at o of the graph matrix with leak at ell. For N=n+1
vertices and a full normalized positive Stieltjes target with N distinct positive
rates, `finite_graph_arbitrary_leak_classification` constructs a full bijection
to the recursive allocation type and proves finite cardinality
n! / product_(v != o)|T_v|. `UnknownLeakFiber` includes the actual leak vertex as
part of the parameters; its exact finite cardinality is |V| times that number.
No positivity premise on an unrestricted competitor has been silently dropped:
this extension is about the stated POSITIVE physical fibers.


## Actual ODE transport and leakage identifiability

For B=diag(h) A diag(h)^(-1), with h_v nonzero, the explicitly constructed state
map S(z)_v=(h_v/h_o)z_v fixes both the physical scalar inlet at o and the observed
coordinate o. `normalizedGauge_solution_iff` proves equivalence of actual
classical ODE solution predicates with the SAME forcing. Both endpoints and
initial values are transported exactly. No positivity premise is needed for
this generic normalized state-equivalence lemma.

For positive finite trees and arbitrary leak ell, `located_continuous_iff_response`
proves exact equivalence of the actual every-continuous-input root-state histories
and the prescribed full Stieltjes response. `finite_graph_all_leak_ODE_classification`
constructs the independent graph presentation and proves complete finite actual
trajectory-fiber classification at each ell and for the unknown-site disjoint
union. The unknown-site count is |V| times the usual factorial/hook expression.

`located_full_response_minimum_energy` states the exact energy decomposition
for every continuous competing control and ACTUAL endpoint-feasible trajectory,
with equality exactly when the controls agree at every point of [0,T]. Signed
control, arbitrary T>0, original state endpoints and the absence of input
rescaling are explicit. Well-posedness and full state observability are proved.

Without ANY full-mode assumption, `leak_location_all_input_indistinguishability`
constructs the actual unique zero-initial solutions of both models for every
continuous input at every collocated inlet/state observer, and proves identical
output histories at every time. The leakage-location transformation is the
same rate-space equivalence for all those collocated experiments. Cross-transfer
and output at a different leaking compartment are not asserted invariant.


## Distinct physical alternatives and nonredundant location counts

`graphCompartment_dart_entry` proves that each actual oriented-edge rate is its
matrix off-diagonal entry, and `graphRates_from_matrix_injective` proves full
rate injectivity for a fixed site. `equal_graph_matrices_identify_leak_site`
proves site injectivity when the leak is nonzero, using actual column sums.
Thus `positiveGraphModelMatrix_injective` and
`unknownLeakContinuousMatrix_injective` exclude duplicate matrix encodings.
`distinct_leak_models_all_collocated_outputs` constructs genuinely distinct
physical matrices at different leak locations with equal all-collocated transfer
and actual continuous-input state histories. No full-mode assumption is needed.


## Positive alternate-leak Jacobian with exact multiplier

`slideLeakJacobian_formula` is a theorem about fderiv of the actual rational
single-edge map, giving a/(f+lambda). Every derivative and its invertible inverse
are proved. `locatedGraphJacobian` reads the ACTUAL alternate-leak coefficient
map followed only by an explicit fixed coordinate permutation.
`locatedGraphJacobian_leak_weight` gives lambda_old*J_ell=lambda_new*J_o(R(y))
for every positive y. Neither coefficient Jacobian is assumed nonzero.
`locatedGraphJacobian_regular_iff` and `positive_located_full_response_regular`
prove the positive singular-set transport and full-target regularity.
`all_positive_located_jacobian_formula` has one fixed root normalization sign,
independent of ell and every y, and the exact previously proved root rate/subtree
factors evaluated at the explicitly relocated actual graph model. This is not
an assertion of zero-boundary all-real polynomial factorization.


## Unrestricted-real arbitrary-leak and actual ODE classification

`supported_positive_diagonal_realization` quantifies ANY real matrix A with
actual tree support and the prescribed full Stieltjes characteristic/cofactor
pair. It constructs a positive conservative model x and nonzero real h with
h(root)=1 and A=diag(h)A_x diag(h)^(-1). No conservation, positivity, stability
or diagonal-similarity premise on A remains after the proved strong induction.
`single_leak_diagonal_gauge_rigid` shows that actual single-leak column sums at
the same site and an invertible nonzero-leak reference force A=B and constant h.
These are the proved dependencies of `real_located_pair_forces_positive`.

`RealLocatedFiber` has ONLY actual response equality as membership; the initially
real rates have no sign, stability or nonzero-Jacobian restrictions.
`realLocatedRecursiveEquiv` gives the complete recursive bijection;
`real_located_fiber_exact_card` proves finite exact n!/product|T_v| cardinality.
`real_located_full_response_positive_regular` derives signs and actual Jacobian
regularity for all competitors. Every specified leak site is included.

`RealLocatedContinuousFiber` likewise has only the actual every-continuous-input
history condition. Reverse identification is proved through explicit actual
exponential-input trajectories for arbitrary matrices. No input rescaling or
vacuous ODE hypothesis is used. `finite_graph_all_real_leak_ODE_classification`
constructs the graph representation, proves the complete all-site actual-ODE
fiber bijections, exact cardinalities and automatic positivity/regularity. The
unknown-site fiber includes the actual site as a parameter and has |V| times the
prescribed-site count. All-rate alternate-leak zero-boundary polynomial
factorization and exact multiplicities remain outside this new full-target block.


## All-rate alternate-leak formal polynomial

For any independently presented finite tree, any observation o and leak ell,
`formalLocatedJacobian` is the formal partial-derivative determinant of the
actual symbolic graph characteristic/cofactor coefficients in the explicitly
fixed coordinate order. Its evaluation equals `locatedGraphJacobian` at EVERY
real vector. `formalLocatedJacobian_factorization` is an equality in the actual
multivariate polynomial ring, not an assumed identity or a finite sample check.

`locatedGraphJacobian_all_real_factored` gives a fixed observation-orientation
sign times the product of actual edge rates toward the leak, actual observed-
subtree edge-product weights, and all actual squared sibling resultants. The
sign is exactly +/-1 and independent of ell and of every rate. Polynomial
continuation is proved from an infinite-sided positive box; no boundary rate
is divided out in the final identity. Exact multiplicities remain a separate
claim until their boundary residual proof is checked.


## Closure: all-real arbitrary-leak polynomial, exact powers and zero set

`finite_graph_complete_all_leak_algebra` starts with an independently presented
finite SimpleGraph G with IsTree, an observation vertex o, and |V|=n+1. It
constructs the observation-root and leak-root presentations, and proves for
EVERY leak ell the independently defined formal partial-derivative determinant:

    J_(o,ell) = C(epsilon_o) * product_(original coordinates k) X_k^m_k * S_(o,ell).

The coefficient map uses actual characteristic and observed principal-cofactor
polynomials in the explicitly specified fixed ordering. Evaluation at EVERY
real vector equals its actual Frechet derivative determinant.

For either dart of an observed-root edge e, m_d=|T_e|-1 plus one if that dart
points toward the leak in its leak-root presentation. The external leak
coefficient has exponent zero. `formalLocatedJacobian_emultiplicity` proves
EXACT finite algebraic multiplicity, and `formalLocatedJacobian_exact_power`
proves divisibility by that power and nondivisibility by the next. The collocated
specializations separately recover the original inward/outward exponents.

S_(o,ell) is built from ACTUAL observed-root principal characteristic polynomials
and their pairwise squared resultants. `symbolicLocatedResidual_no_coordinate_factor`
is proved by universal graph-coordinate hyperplane witnesses: triangulate at the
leak root with all outward rates zero and injective inward values, including the
selected zero coordinate. All observed-root principal blocks inherit a proved
rank order, and disjoint sibling diagonal sets have coprime characteristic
polynomials. This proof works for every original graph coordinate and every
leak site. It is not a finite specialization test or a hidden nondivisibility input.

`locatedJacobian_zero_iff_all_rates` gives the complete actual Jacobian zero set:
a zero coordinate with positive displayed exponent OR a zero actual sibling
residual. The external leak variable does not divide the polynomial, including
when ell != o. Signed rates, zero rates, zero leak, repeated spectra and the
singleton tree are not excluded.

The intended root/alternate-leak algebraic, full-positive-target real-fiber,
independent graph, continuous-input ODE and signed-control theorem families now
have no missing mathematical dependencies within their explicitly stated scope.
Independent empty-kernel verification of these new bytes is a separate source-
bound CI run; no earlier receipt certifies the new exact-multiplicity extension.


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


## Completed actual short-time identification protocol (2026-10-15)

The new protocol is now proved through actual classical ODEs. At each original
node v inject a constant unit input and observe its own zero-initial state.
The second derivative is A_vv; the third is (A*A)_vv. N second derivatives and
N-1 third derivatives suffice: ANY one third derivative may be omitted.
`actual_punctured_step_jets_suffice` proves this from actual trajectories.
These coefficients are exact derivatives, not a finite sample/noise guarantee.

For EVERY strictly positive reference on the known tree, including hidden modes
and repeated spectra, the complete unrestricted-real all-node fiber is exactly
one distinct matrix per leakage site. `all_node_jets_determine_all_collocated_histories`
proves no further collocated continuous-input experiment can distinguish them.

`actual_positive_mixed_probe_identification` adds an adaptive positive rational
mixed-input/mixed-output experiment and proves recovery of BOTH the true leakage
site and every rate. The chosen weights have the explicit form 1+1/(k+2), hence
lie strictly between 1 and 2. A single scalar second output derivative separates
all candidates. The mixed experiment's actual solution exists uniquely and the
output derivative is proved to be c^T A b. No impulse or unchecked solver enters.

This result permits simultaneous inputs and a weighted observation across ALL
nodes. It is not one additional physical point sensor, not one fixed universal
probe, and not a robustness guarantee. The existence proof chooses weights
from an infinite rational grid; a bounded finite search theorem is a separate
possible strengthening. It does not classify nonminimal SINGLE-node fibers.

All five additional modules compiled in source-isolated diagnostics with matching
source hashes. The new 229-module checkpoint has its own independent audit/replay.
A source-coverage guard now rejects tracked owned modules omitted from MODULES,
so source-only additions cannot silently receive an incomplete green certificate.


## New multiple-leak extension — partial formalization

The new MultiLeakSimplex, ResidenceGauge and SingleLeakResidence modules prove
actual residence-inverse positivity for positive finite single-leak trees and
the exact simplex/normalized-scale equivalence for nonnegative ACTUAL column
losses. Physical stationary fractions and zero-loss faces are proved. The
general intermediate inverse hypotheses are discharged at the physical graph
entry graphLeakSimplexEquivGauge. No positive-inverse theorem is assumed there.

The exhaustive multi-leak full-response fibre, original multi-leak rate mapping,
homeomorphism, total-storage sample count and sharp residual ambiguity still
require their own new proofs and source-specific independent verification.
These are an extension beyond the earlier closed single-leak core, not claims
covered by its old certificate. See research/hydrology-multileak/README.md.
