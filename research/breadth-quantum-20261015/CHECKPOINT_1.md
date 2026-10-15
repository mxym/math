# N0 research checkpoint — 15 October 2026

Author: Yongxian Zhang (张永贤), South China University of Technology.
No external funding. OpenAI AI assistants assisted. Original material:
all rights reserved; external inputs retain attribution and licenses.

**Status: the complete N0 target is open in this packet. New major
solutions: zero. This is a research checkpoint, not an audited theorem
package, a Lean proof, or a publication.**

## 1. Effective clock and inherited computation

The interrupted role's 05:24:50–05:27:49 UTC interval is conservatively
charged as 179.030475 author-research seconds. Its saved finite search ran
3023.649546 seconds and completed 16,949 rank-two optimizations, but later
author activity could not be reconstructed. That computational duration
is recorded separately, not silently charged as author research. The
replacement role resumed active work at 06:32:40.132441 UTC. Context
recovery and the unknown intervening interval are excluded. See STAGE.json.

## 2. The full question is retained

We seek a single finite physical NPT state that is undistillable for every
copy number and every collective complex Schmidt-rank-at-most-two vector,
or a distillation theorem covering every finite NPT state. The canonical
Werner endpoint is a sufficient affirmative route, not a replacement for
the complete existence problem. A negative endpoint witness alone would
not settle N0. All finite search and local differential calculations below
are diagnostics toward that full question.

## 3. Exact exclusion of a parity-compressed determinant route

Let d>=3 and let E and O be the even and odd permutations of [d]. In
H=(C^d)^{tensor d}, put

    u = sum_{f in E} |f(1),...,f(d)>,
    v = sum_{f in O} |f(1),...,f(d)>,
    C = |u><u| - |v><v|.

The coefficient matrix C has rank two, u and v have disjoint supports,
and ||C||_HS^2=(d!)^2/2. These facts use unnormalized u,v.
For every traced subset J of resource slots,

    ||Tr_J C||_HS^2 = (d!)^2/2,       |J|=0;
                       (d!)^2/(2d),  |J|=1;
                       0,             |J|>=2.

Proof for |J|>=2: a nonzero partial-trace summand has equal traced row and
column labels, with the same unused alphabet for the untraced row and
column. Their parities either disagree, making C's entry zero, or agree.
In the latter case, swapping two traced labels pairs every completion
with a completion of the opposite sign. The partial-trace entry vanishes.
For |J|=1 there is no such cancellation. The omitted alphabet symbol
labels d disjoint blocks. In each block, the remaining (d-1)! permutations
split equally into two parity classes; the block has two square constant
subblocks, each of size (d-1)!/2. Its squared Hilbert–Schmidt norm is
((d-1)!)^2/2. Multiplying by d proves the asserted value. The untraced
formula follows directly from the two disjoint constant blocks.

Consequently, for the full alternating partial-trace form,

    Q_d(lambda,C) = (1-lambda) (d!)^2/2.

In particular this *particular route* never supplies a negative witness
for any physical Werner parameter lambda<=1. This is not a statement
about all rank-two witnesses. The d=2 exception has Q_2=2-4lambda because
the one-slot remainder does not split into two equal parity classes.

The direct exact controls verify every subset for d=2,3,4 and one subset
per cardinality for d=5,6. Resource-slot permutation symmetry supplies the
remaining subset equivalence in the latter cases. These controls support
the counting argument; they do not replace it.

### A physical check of the old full-domain claim

For rho=(I-F/2)/(15/2) on C^3 tensor C^3, rho is positive, has trace one,
and rho^{T_B}=(I-|Omega_3><Omega_3|/2)/(15/2) has a negative eigenvalue.
For the old parity-compressed rank-two vector vec(C), d=3 and lambda=1/2
give the raw expectation +9. The normalized physical expectation is
4/3375>0. The right sides asserted in Eqs. (22) and (25) of
[Sperling–Vogel, arXiv:0910.0744v2](https://arxiv.org/html/0910.0744v2)
instead evaluate to -9 on this input. In Eq. (22), only the identity
relative even permutation contributes: a nonidentity even permutation
of three letters has no fixed point, and every corresponding contracted
column vanishes. The identity term is det(I-J_3/2)=-1/2, with prefactor 18.
Thus that displayed equality already fails before using its Eq. (23).

The uncompressed antisymmetric determinant vector has raw expectation
-3 but coefficient rank six; it is not a legal rank-two distillation
vector. A local filter applied to this vector is not entitled to preserve
the sign of an indefinite observable. This packet rejects the displayed
argument on its own exact physical input, without asserting priority for
the gap or a resolution of N0.

## 4. Full rank-two local chart and adversarial zero tests

For a rank-two point C0=U W*, where U,W have orthonormal columns, choose
orthonormal complement frames V,Z. Every sufficiently close rank-two
matrix has the chart

    C(S,X,Y)=(U+VX)(I+S)(W+ZY)*.

S is an arbitrary complex 2-by-2 matrix, and X,Y are arbitrary complex
(dim H-2)-by-2 matrices. Thus perturbations do not impose normality,
positivity, common support, a product ray, or real coefficients.
On a straight chart ray, C(t)=C0+tD+t^2 E+t^3 F, where

    D=USW*+VXW*+UY*Z*,
    E=VXY*Z*+VXSW*+USY*Z*,
    F=VXSY*Z*.

Writing L=product_i(Id-(1/2)Tr_i*Tr_i), the exact quadratic coefficient is

    Q(D)+2 Re <L(C0),VXY*Z*>.

The other terms in E pair to zero at a stationary C0 because they are
tangent. Matrix-free Hessian actions are calibrated by this polynomial
chart, its symmetry, orthogonality of computed eigenvectors, and actual
Ritz residuals. No Ritz diagnostic is converted into a global sign bound.

There is an all-copy source of legal zeros inside qubit supports: after
the local unitary taking the two-qubit maximally entangled ray to the
singlet, W_2 is the symmetric projector. Every decomposable global wedge
u tensor v - v tensor u has rank two and is killed by the product of local
symmetric projectors, since that product lies in the globally symmetric
subspace. Mapping back and embedding the qubit supports into qutrits
gives exact endpoint zeros at every copy count. Generic u,v produce
distinct input/output planes, so these tests include nonnormal points.
This is a zero construction, not an all-copy positivity certificate.

At six tested three-copy anti-state points, the corrected full-chart
Hessian has 38 numerical zero directions and no eigenvalue below -1e-9.
Sampling null directions and relaxing the second-order transverse
coordinates gives quartic coefficients zero to numerical accuracy.
Neither a full local-neighborhood theorem nor global positivity follows.

## 5. Retained numerical failure and corrected controls

An initial scipy.linalg.eigh default-driver run produced a badly
nonorthogonal eigenvector matrix at one highly degenerate test point.
Using those vectors as an orthonormal eigenbasis generated spurious
nonzero cubic and quartic null-direction coefficients. Direct chart
evaluation rejected that interpretation. The initial script, matrices,
and result JSONs are retained with INITIAL_NUMERICAL_FAILURE labels.
The rerun uses driver='evd' and explicitly asserts orthogonality and
eigenvector residual bounds. Its cubic values and relaxed quartics are
zero at floating-point accuracy on the stated finite samples. The failure
is not hidden, and no mathematical counterexample was claimed from it.

The inherited controls were accidentally rerun once by importing the old
script, whose top-level block writes its output. The original JSON was
restored byte-for-byte from the parent's interruption archive; the repeat
is retained separately as SEARCH_CONTROLS_RERUN_063331.json. Subsequent
scripts load only the pure function definitions, excluding that I/O block.

## 6. Remaining proof gates

No argument here controls every complex rank-two C for every k with a fixed
physical NPT state. The crossed input/output Gram obstruction remains.
Partial traces can increase rank; a two-copy theorem cannot simply be
reapplied to them. Finite searches cannot certify arbitrary-copy
undistillability, and qubit-supported zeros do not cover qutrit witnesses.
These are explicit open gates, not solved statements in a README.
