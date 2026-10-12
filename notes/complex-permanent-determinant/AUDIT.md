# Internal mathematical audit: complex three-row permanent inequality

**8 October 2026.** Scope: model-assisted proof checking and exact
arithmetic reproducibility; no human referee or formal kernel theorem
certification.

## Claim and dependency audit

The new manuscript proves the **exact all-coefficient norm** via a five-template maximum and independently deduces the **exact coefficient lens**: at the sharp permanent coefficient \(2/\sqrt3\), all complex coefficients \(\lambda\) with universal validity are **exactly** those satisfying \(|\lambda|^2+2|\operatorname{Re}\lambda|\le1/3\). Odd and even permutation matrices establish necessity; the full rational Hermitian certificate establishes sufficiency. In particular it proves, for arbitrary complex \(3\times3\) matrices,
\[
|\operatorname{per}A|+(2/\sqrt3-1)|\det A|
\le(2/\sqrt3)\prod_i\|A_{i,*}\|_2,
\]
and classifies equality. The earlier [real proof](../sharp-robust-permanent/paper.md),
Section 9, already proved the *real* trilinear endpoint and the same
radius for **nonnegative** functions. No claim of novelty for that
inherited real-radius statement is made here. The complex inequality
uses a separate Hermitian certificate and has a genuine additional
absolute value around the permanent.

The stronger full-norm theorem has five necessary equality witnesses:
all-ones, both parity permutation matrices, and two Fourier-mode
rows. Its universal upper bound uses \(B=C_\lambda^2\) and
three explicit constraints \(B\ge4/3\),
\(B\ge1+q+2|x|\), \(B\ge q+1/3+2|y|/\sqrt3\).
The new exact determinant identity is
\[
\det H_B=B(h^2-v^2)U+B(3h^2+v^2)V
+(3B-4)([3(B-q)-1]^2-12y^2)XYZ.
\]
The AM–GM positivity of \(U,V\), the sign gates and all
Hermitian principal-minor arguments are proved directly in the manuscript.
[check_full_norm.py](check_full_norm.py) separately verifies its two
rational polynomial identities at all 4,096 six-variable interpolation
points, hence as global formal polynomial identities. This is additional
to, and strictly stronger than, the sharp-lens certificate.

The resulting three-row **sharp multilinear functional norm** is
\(\kappa(t)=\max\{1,(\sqrt3/2)(1+6|t|)\}\)
for *every* uniform-marginal \(S_3\) law. Exact tensorization over independent
nonidentical columns gives the product \(\prod_\ell\kappa(t_\ell)\).
The upper bound follows by conditional \(L^2\)-norm induction, while
nonnegative constant/indicator row tensors attain equality. The
[exact finite tensor checker](check_tensor.py) independently reconstructs
all uniform marginals, expectations and normalized \(L^2\) ratios for
ten rational parameter vectors, totaling 960 permutation tuples.
This finite replay corroborates the extremizers; the *all-N* proof
is analytic in the manuscript.

The key proof reductions have explicit checks:

- Expansion \(c^{\mathsf T}M_\lambda(a)b=\operatorname{per}A+\lambda\det A\) is obtained term by term from (2).
- The Hermitian coefficient formulas in (5)–(6) follow from matrix
  multiplication; [check_matrix.py](check_matrix.py) separately
  exercises the matrix-entry identities at 60 exact complex test pairs
  including complex phases on and inside the circle of radius \(s\). This is a regression, not an all-input proof.
- All three first-order principal minors are nonnegative for
  \(-s\le\operatorname{Re}\lambda\le s\).
- Formula (7) is a nonnegative-coefficient polynomial for the **full lens**, with the cyclic analogues covering the remaining principal minors.
- The determinant SOS formula (9) is an exact **rational** polynomial identity for the full lens; [check_lens.py](check_lens.py) verifies it and (7) on all **1,024** five-variable interpolation nodes over \(\mathbb Q\). Since the degrees are at most three separately, this *does* prove the displayed polynomial identities, rather than sampling them. The [older specialized certificate](check.py) independently checks the sharp centered-disk identity (9a) at 256 four-variable \(\mathbb Q(\sqrt3)\) nodes.
- Both nonnegative cubic factors are controlled by AM–GM; the
  positive-semidefinite conclusion follows from the elementary
  Hermitian principal-minor criterion.
- Equality requires a nontrivial kernel of the certificate.
  The **centered-disk** determinant factors force either equimodular coordinates in one row or one-sparse support with real extremal \(\lambda\).
  Circulant singular-value separation then forces equal-modulus
  rank-one rows; the one-sparse case forces a monomial matrix.
  Zero rows are stated separately.
- Every uniform-one-point-marginal law on \(S_3\) is an even/odd
  mixture. The endpoint is not just sufficient: indicators of a
  favored parity permutation give the exact necessity.
- Complex tensorization explicitly uses absolute values before
  averaging outer independent permutation coordinates.

## Exact replay and what it certifies

Run all five scripts in both Python modes and compare each with its
frozen report:

~~~sh
python3 notes/complex-permanent-determinant/check_full_norm.py
python3 -O notes/complex-permanent-determinant/check_full_norm.py
python3 notes/complex-permanent-determinant/check_lens.py
python3 -O notes/complex-permanent-determinant/check_lens.py
python3 notes/complex-permanent-determinant/check.py
python3 -O notes/complex-permanent-determinant/check.py
python3 notes/complex-permanent-determinant/check_matrix.py
python3 -O notes/complex-permanent-determinant/check_matrix.py
python3 notes/complex-permanent-determinant/check_tensor.py
python3 -O notes/complex-permanent-determinant/check_tensor.py
(cd notes/complex-permanent-determinant && sha256sum -c SHA256SUMS)
~~~

There are 4,096 exact checks of each complete-norm identity, 1,024 checks of each full lens identity, 256 checks of each centered-disk identity, 60 entrywise complex matrix regressions and 960 exact tensor-witness tuple cases, and two maliciously
corrupted-formula negative controls in the main checker.
No floating point, numerical optimization, randomized solver, or
unreplayable certificate is used. Optimization mode cannot disable
any essential certificate condition because checks use explicit
exceptions, not the Python assert statement.

## Limitations

The proof is a written mathematical argument with exact algebraic
support, *not* a Lean formalization of the AM–GM, equality,
tensorization, or Hermitian spectral claims, and not independent human
peer review. The exact same radius was already known from the
predecessor **for nonnegative functions**, so this supplement
must be credited specifically as a complex extension. No historical
first-in-literature or optimal \(n\ge4\) extension is asserted.