# Automatic positivity and exact real fibers of root-observed tree models

**Yongxian Zhang (张永贤)**
School of Computer Science and Engineering, South China University of Technology
mxymmxym1@gmail.com · ORCID 0009-0000-3864-3536

This note explains the all-size real-fiber theorems in
[the Lean project](../../formalizations/hydrology-tree-core/README.md).
It concerns actual linear bidirected tree compartment matrices, not arbitrary
nonlinear catchments. The proof in this note specializes to input, observation and external loss
at one root. The completed fixed theorem core also covers arbitrary leak sites,
independent graph presentations and actual continuous-input ODE bridges; see
[the focused manuscript](../../preprints/finite-tree-jacobian-2026-10/README.md),
[arbitrary-leak algebra](ALTERNATE_LEAK_JACOBIAN.md), and
[exact source entrypoints](THEOREM_ENTRYPOINTS.md). This publication-preparation
round checks existing source and receipts and adds no Lean audit roots.

## 1. Model and theorem

Let T be a finite labelled tree with root o and N vertices. For each nonroot
vertex v, write a_v for the transfer from v to its parent and f_v for the
opposite transfer. Let ell be the root leak. Define the actual matrix A using
these off-diagonal transfers and a diagonal equal to minus the total rate leaving
each compartment. Its columns sum to zero except at the root, where the sum is
-ell. The coefficients (ell,a,f) are initially allowed to be arbitrary REAL
numbers; positivity is not a premise on a competing realization.

Let P_x(s)=det(sI-A(x)) and F_x(s)=det(sI-A(x)[V\{o},V\{o}]), retaining the
original diagonals in the principal block. Both are monic, of degrees N and
N-1. The root resolvent is

    G_x(s) = [(sI-A(x))^(-1)]_(o,o) = F_x(s)/P_x(s)

away from the actual characteristic roots.

Fix a target

    G(s) = sum_(i=1..N) w_i/(s+r_i),
    r_i > 0 and pairwise distinct, w_i > 0, sum_i w_i = 1.

Write P(s)=product_i(s+r_i) and
F(s)=sum_i w_i product_(j != i)(s+r_j). For v != o let N_v be the number of
vertices in the actual rooted subtree at v.

### Theorem A — complete real classification

All real rate vectors x with G_x=G on their common nonpole domain have the
following properties.

1. Every a_v, f_v and the root leak ell is strictly positive.
2. Their actual coefficient Jacobians are nonzero.
3. The complete set of such rate vectors is in bijection with the recursive
   labelled pole allocations described below, and has exactly

       (N-1)! / product_(v != o) N_v

   elements. In particular, it is finite. There are no additional negative-rate,
   zero-rate or singular real solutions outside this list.

Labels are retained. This is not a quotient by automorphisms of T. The formula
holds for every target in the displayed full N-mode class, not only for a generic
choice of its poles or weights. The one-vertex case gives one model.

The Lean statements are `real_stieltjes_realization_is_positive`,
`realResponseRecursiveEquiv`, `real_root_response_fiber_exact_card`, and
`real_full_response_forces_positive_regular`. Their definitions use the actual
matrix and actual root inverse entry. The coefficient-pair version and its
response-only equivalence are proved separately; the internal polynomials are
not silently treated as additional observations.

## 2. Why the reciprocal gives positive child data

Order the target rates r_1<...<r_N. The function G has one zero between each
consecutive pair of its negative poles. Indeed, on each such interval its
derivative is -sum_i w_i/(s+r_i)^2<0, and its endpoint limits have opposite
infinite signs. There are N-1 such zeros. Since the numerator is monic of degree
N-1, these account for every zero and each is simple.

Write the zeros as -beta_j, with beta_j>0. The reciprocal has the unique form

    1/G(s) = s+d - sum_(j=1..N-1) gamma_j/(s+beta_j),
    gamma_j > 0.

At a zero z=-beta_j, the residue of 1/G is 1/G'(z)<0. Thus gamma_j=-1/G'(z)>0.
Monic division determines the polynomial part s+d, and exact interpolation
proves the displayed identity. Evaluation at zero gives

    ell = d - sum_j gamma_j/beta_j = 1/G(0) > 0.

These are not imported as a classical Stieltjes black box in the formalization:
interlacing, complete zero factorization, simplicity, residue signs, division
and reconstruction are proved in the Stieltjes modules. The zero-free numerator
case N=1 is included. Unsorted input labels are handled by a proved permutation.

## 3. Forward construction for each root allocation

Suppose the root's labelled child subtrees have sizes N_1,...,N_k, whose sum is
N-1. Partition the N-1 reciprocal pole indices into labelled sets I_c of these
sizes. Define

    k_c = sum_(j in I_c) gamma_j,
    G_c(s) = sum_(j in I_c) (gamma_j/k_c)/(s+beta_j).

Each G_c is a normalized full positive Stieltjes target of the required child
size. Its internal pole enumeration is fixed canonically; reordering within a
block is not a different allocation.

Construct an actual positive model on each child tree recursively. Its root
leak a_c satisfies

    a_c = 1/G_c(0),
    f_c = k_c/a_c = sum_(j in I_c) gamma_j/beta_j > 0.

Use ell=1/G(0) as the parent root leak, and the displayed f_c as its outward
connectors. The parent root's full negative diagonal is
ell+sum_c f_c=d. The proved characteristic/cofactor attachment identities then
give exactly the prescribed P,F, not merely approximate response samples.

The rate-coordinate assembly is performed in the original tree, through a
proved invertible parameter reindexing. Every child principal diagonal retains
its original exit-to-parent rate; it is not reset as though the branch were a
closed system.

This forward construction gives every proposed allocation an actual positive
realization. On its own, however, it would not prove completeness or a count.

## 4. Reverse extraction and automatic positivity

Now take ANY real competing vector x with the prescribed full P,F, with no
physical sign assumptions. The actual root cofactor equals the product of the
actual child characteristic polynomials P_c. Each P_c is monic, has the required
child degree, and divides

    F = product_j(s+beta_j).

Consequently each child polynomial splits into a subset of these distinct real
linear factors. Degree accounting shows that these subsets give exactly one
labelled allocation of all reciprocal poles. This is an algebraic consequence
of the actual matrix identity, not a numerical matching procedure.

For these assigned pairwise coprime denominators, the branch numerator
representation is unique under the strict degree bounds. To see this, subtract
two such representations and reduce modulo P_c. All other summands vanish;
the product of the other denominators is invertible modulo P_c. The remaining
numerator difference is divisible by P_c but has smaller degree, so is zero.
The argument also works if the sums agree only modulo the full product, which
allows the root diagonal to be initially unknown.

Compare x with a proved positive reference constructed for the same allocation.
The exact recovery theorem identifies every edge-product times child cofactor.
Because child cofactors are monic, their scale and polynomial are both identified.
Thus each actual child of x has exactly the normalized target G_c above.
Strong induction now forces every child rate, including its exit-to-parent leak,
to be positive. The remaining parent connectors and root leak are uniquely fixed
by the parent coefficients and these child models. They equal the positive
constructed connectors and ell. Hence x itself is strictly positive.

This proves more than the existence of positive realizations: the response
forbids all additional nonpositive REAL realizations. The theorem does not claim
the corresponding result for complex parameters without a separate proof.

## 5. The exhaustive bijection and count

The forward and reverse constructions are inverse on actual parameter vectors.
Different root allocations have different child characteristic polynomials.
Within one allocation, different actual child rate vectors remain different
after the proved parent assembly. Conversely, every parent gives its unique
allocation and its actual child models. Recursing constructs a full bijection,
not only an injection into a candidate family.

There are exactly

    (N-1)! / product_c N_c!

labelled root allocations. The formal proof obtains this by a bijection between
all pole-ordering permutations and an allocation together with independent
within-block permutations, so the factorial division is justified.

If D(T) denotes the actual fiber cardinality, the bijection gives

    D(T) = ((N-1)! / product_c N_c!) * product_c D(T_c).

Using the inductive formula for D(T_c) gives

    D(T) = (N-1)! / product_(v != o) N_v.

In Lean, the multiplication identity
D(T)*product_(v != o) N_v=(N-1)! is proved before division. Positivity of the
hook product and finiteness of the actual fiber are proved explicitly. No use
of Nat.card on an unproved finite set masks an infinite fiber by zero.

The recursive type `RecursivePoleAllocations T` depends only on the tree.
`realResponseRecursiveEquiv` exhibits its equivalence with the whole real
response fiber. This also shows that the cardinality is independent of the
particular distinct positive target rates and normalized positive weights.

## 6. No stronger observation is hidden

Equal actual root resolvents on the common nonpole domain imply a polynomial
cross identity by equality at infinitely many real points. The target pair is
coprime and has full prescribed degree. Its monic denominator therefore divides
the competing monic denominator of the same degree and must equal it; the
numerators then agree. A competing model need not be assumed minimal, stable,
positive or Jacobian-regular for this argument.

Hence Theorem A concerns root-response data alone. Exact characteristic and
cofactor coefficients are intermediate mathematical objects, not extra measured
information. The root inverse is totalized algebraically at singular values in
Lean, but no equality at a pole is used as a physical measurement.

## 7. Actual discharge rather than root storage

With discharge Q=ell*x_o, the root-discharge transfer is H(s)=ell*G(s), where

    ell = 1/G(0) = 1/(sum_i w_i/r_i).

The leak need not be supplied independently. Equality of two discharge transfers
implies a cross-polynomial identity; its leading coefficients force equality
of the two leaks because the characteristic and root-cofactor polynomials are
monic. For the positive full target, this nonzero leak can be cancelled, giving
root-response equality. The converse uses the proved formula for ell.

The `DischargeFiber` module formalizes this actual matrix-transfer bridge and
proves the same exact all-real cardinality for discharge-response fibers.
The complete package separately proves both directions of continuous-input
ODE history equivalence; see `real_located_continuous_iff_response` and
`finite_graph_all_real_leak_ODE_classification` in the source entrypoint index.
That analytic interface is not inferred from the discharge algebra alone.

## 8. Scope and verification

The hypotheses are essential to the stated scope: finite labelled bidirected
trees, constant real rates, root input and observation, sole leak at that root,
and a full N-mode positive target. The original root-leak theorem in this note
is supplemented by the completed independent-graph, alternate-leak and actual
ODE theorems in the fixed core. Fewer-mode or repeated-pole targets, distributed
inputs, off-diagonal observations and nonlinear hydrological systems remain
outside this stated scope.

The complete code, exact theorem statements, dependency map, fixed toolchain,
source hashes, empty-kernel replay and deliberately incorrect controls are in
[the formalization](../../formalizations/hydrology-tree-core/README.md).
Checkpoint-specific CI receipts certify only their own exact source bytes.
Development compilation is not independent kernel replay or human peer review.
No historical-priority or established major-breakthrough claim is made here.

No external funding; AI-assisted research and formalization. Existing repository
and third-party notices remain in force. Original additions retain all rights
not otherwise granted by an applicable existing license.
