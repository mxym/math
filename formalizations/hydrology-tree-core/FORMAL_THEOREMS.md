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
