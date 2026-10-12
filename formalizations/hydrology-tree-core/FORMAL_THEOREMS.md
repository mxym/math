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
