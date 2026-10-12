# Actual fixed rational Bapat witness: definition-by-definition proof

This package connects the paper's **specified** matrix and parameters to the
actual all-permutation q-permanent. Its main theorem has no negative-derivative,
Fischer-identity, data-certificate, or perturbation hypothesis.

## Statement

Use the published ordered 200-row data
`notes/bapat-q-permanent-counterexample/counterexample_vectors_n200.csv`, whose
SHA-256 is `9d16617d6eb287535a752cf5ef6f3d4672a133812bf0fbd908738a10c223fc25`.
For row i write its two Gaussian integers as a_i and b_i. Put

\[
 A_{ij}=a_i\overline{a_j}+b_i\overline{b_j},\qquad
 P_q(A)=\sum_{\sigma\in S_{200}}q^{\operatorname{inv}(\sigma)}
             \prod_i A_{i,\sigma(i)}.
\]

Ordering matters: inversion count is computed in exactly the published order.
Define the following integers and rational numbers, without rounding:

\[
 N=19900,\quad \Gamma=N\,200!\,200\,1601^{199},\quad
 K=N(N-1)\,200!\,1601^{200},
\]
\[
 \varepsilon=\frac1{4\Gamma},\quad h=\frac1{8K},\quad
 q_0=1-h,\quad B=A+\varepsilon I_{200}.
\]

`BapatExplicit.explicit_rational_counterexample` proves, for this actual B:

1. B is complex Hermitian positive definite and non-diagonal;
2. 0 < q_0 < 1;
3. \(P_{q_0}(B)-P_1(B)\ge h/8>0\).

The values here are real: `explicit_qPermanent_real` proves reality of the
actual q-permanent for every real q. `explicitMatrix_rational_entries` proves
that every entry of B has rational real and imaginary parts, with explicit
formulas in the same ordered data. `explicit_not_monotone` and
`original_conjecture_false_from_explicit` then refute monotonicity and the
original strict-monotonicity conjecture on [-1,1]. The initial A is a rank-two
Gram matrix; adding a positive diagonal shift makes B full rank. This is a
complex Hermitian counterexample, not a proof of the real-symmetric existence
theorem.

## 1. Definitions really coincide

The universal perturbation package and the original finite-witness package use
separate namespaces. `DefinitionBridge.lean` proves their equivalence rather
than passing it as an assumption:

- the double finite sum of inverted pairs equals the cardinality of the actual
  filtered set of inverted pairs;
- the two q-permanents sum over the same permutations with identical weights;
- the real part of the universal endpoint derivative equals the derivative at
  1 of the original real q-permanent polynomial;
- the actual two-column V satisfies \(VV^*=A\);
- the two diagonal perturbation definitions coincide.

The equality of finite permutation sums is proved extensionally; it does not
rely on assuming two separately constructed `Fintype` enumeration instances
have the same underlying implementation.

## 2. The actual integer certificate supplies the derivative gap

For \(\ell_i(x,y)=a_ix+b_iy\), set

\[
 F=\prod_i\ell_i,\qquad
 S=\sum_{i<j}(a_i b_j-b_i a_j)\prod_{r\ne i,j}\ell_r.
\]

For a degree-d binary form T, the Fischer norm is
\(\|T\|_F^2=\sum_{k=0}^d(d-k)!k!|T_k|^2\).
The original 22-module proof constructs both coefficient arrays by exact
Gaussian-integer recurrence, proves every one of the 200 transitions against
the actual products and derivatives, and proves

\[
 19900\,P<W,\qquad P=\|F\|_F^2,\quad W=\|S\|_F^2.
\]

The permanent/Fischer pairing and ordered marked-inversion identities in that
package prove

\[
 2P'_1(A)=19900\,P-W.
\]

`N200EndpointGap.lean` proves that the actual stored integer norms equal those
of the actual F and S by the proved state-equals-checkpoint theorem. Since P,W
are integers, strict inequality gives \(W-19900P\ge1\). Casting this exact
inequality to the reals and using the actual endpoint identity gives
\(P'_1(A)\le-1/2\). There is no numerical sign premise in the final theorem.

The certificate uses `decide +kernel`, whose finite arithmetic proof is checked
by Lean's kernel. It does not use `native_decide`, a floating-point sign test,
a solver assertion, or a postulated arithmetic theorem.

## 3. The entry bound comes from the same ordered data

`N200EntryBounds.lean` kernel-checks for all 200 rows that the integer squared
norms of both a_i and b_i are at most 800. The exact Gaussian-integer embedding
is proved to preserve the squared complex norm. For any i,j, the inequality
\((|a_i|-|a_j|)^2\ge0\) gives \(|a_i||a_j|\le800\), and similarly for b.
The triangle inequality therefore gives \(|A_{ij}|\le1600\).

`FalseCoordinateBound.lean` deliberately substitutes 400 for the b bound. The
actual data have a b-coordinate squared norm of 421; the same kernel decision
tactic rejects this materially false bound. A failed control is required by
the replay runner.

## 4. Explicit perturbation survives

For 0 <= t <= 1, telescoping each permutation product proves

\[
 |P'_1(A+tI)-P'_1(A)|\le\Gamma t.
\]

The 52-theorem universal package proves this estimate for actual complex
matrix entries, the actual inversion count, and the actual all-permutation
sum. In particular, it proves inversion count <= N and that there are 200!
permutations. Substituting the specified \(\varepsilon=1/(4\Gamma)\) gives
\(P'_1(B)\le-1/4\).

The same package proves \(VV^*+\varepsilon I\) is positive definite for every
positive epsilon, using the actual Hermitian quadratic form. A diagonal matrix
has endpoint derivative zero, so the strictly negative derivative also proves
that B is non-diagonal.

## 5. The specified rational interval reverses monotonicity

Every entry of B has modulus <=1601. Termwise polynomial differentiation and
\(\operatorname{inv}(\sigma)(\operatorname{inv}(\sigma)-1)\le N(N-1)\)
prove \(|P''_q(B)|\le K\) for real 0 <= q <= 1. The universal package proves
the associated derivative estimate and mean-value inequality, not merely a
polynomial-degree bound. Thus for \(q\in[1-h,1]\),

\[
 P'_q(B)\le-1/4+Kh=-1/8,
 \qquad P_{1-h}(B)-P_1(B)\ge h/8.
\]

`ConstantParameters.lean` proves that its natural integer constants, rational
parameters, real casts, and complex casts coincide with exactly the universal
parameters. Its cast lemmas retain factorials and powers symbolically. The
dimension-three lower-bound theorem supplies Gamma >=1 and K >=1 for n=200;
therefore h is positive and q_0 lies strictly between 0 and 1.

`N200Explicit.lean` supplies every hypothesis of the universal transfer theorem
from the proofs above and rewrites the resulting theorem through the proved
definition bridges. It then uses the actual interval membership of q_0 and 1
to contradict `MonotoneOn` and the original `StrictMonoOn` conjecture.

## 6. Rational entries and evidence boundary

Writing a_i=u_i+iv_i, b_i=s_i+it_i, the real part of A_ij is
\(u_i u_j+v_i v_j+s_i s_j+t_i t_j\), and the imaginary part is
\(v_i u_j-u_i v_j+t_i s_j-s_i t_j\). These are integers. Adding the rational
epsilon only on the diagonal preserves rational real and imaginary parts.
The Lean proof verifies these formulas using the actual Gaussian-integer
embedding and `Complex.ext`.

Fresh compilation and empty-kernel replay establish formal proof validity;
source/data correspondence and this definition-by-definition review establish
what that proof says. The empty-kernel replay covers the transitive closure of
all 30 newly owned theorems, including the imported actual arithmetic and
universal analysis needed by those theorems. The input packages additionally
have separate full owned-closure records. A recorded-evidence checksum check is
not itself a new Lean execution. Formal verification of this fixed rational
witness does not certify the separate asymptotic or real-symmetric construction,
and does not establish historical priority.
