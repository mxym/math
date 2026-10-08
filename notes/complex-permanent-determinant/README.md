# Exact operator norm for the complete complex three-row permanent–determinant pencil

**Strongest result — exact sharp constant for every complex coefficient.**
For any fixed \(\lambda\in\mathbb C\), the optimal all-matrix constant is
\[
\boxed{\ C_\lambda=\max\left\{\frac2{\sqrt3},
|1+\lambda|,|1-\lambda|,
\left|\lambda+\frac{i}{\sqrt3}\right|,
\left|\lambda-\frac{i}{\sqrt3}\right|\right\}.\ }
\]
The [proof](PAPER.md#2b-exact-norm-of-the-permanentdeterminant-pencil-for-every-complex-coefficient) obtains the upper bound from an exact six-variable Hermitian determinant decomposition; each of the five terms has a concrete equality witness (constant, even/odd permutation or Fourier rows). The [full norm rational checker](check_full_norm.py) certifies both symbolic polynomial identities on all \(4^6=4096\) interpolation nodes, independently from the previous lens/disk checkers. The coefficient lens below is precisely the level set \(C_\lambda\le2/\sqrt3\).

This standalone supplement to the [robust permutation permanent programme](../sharp-robust-permanent/README.md) **completely classifies** the complex coefficients \(\lambda\) for which the sharp pencil inequality holds for **every complex** \(3\times3\) matrix:
\[
\boxed{\quad
\left[\,|\operatorname{per}A+\lambda\det A|
\le\frac2{\sqrt3}\prod_i\|A_{i,*}\|_2
\quad\text{for every }A\in\mathbb C^{3\times3}\right]
\quad\Longleftrightarrow\quad
|\lambda|^2+2|\operatorname{Re}\lambda|\le\frac13.
\quad}
\]
The coefficient region is a **sharp closed lens**, proved by a rational Hermitian SOS identity; odd and even permutation matrices certify necessity. Its largest centered disk gives, as a corollary, the sharp absolute-value inequality:
\[
\boxed{
|\operatorname{per}A|
+\left(\frac2{\sqrt3}-1\right)|\det A|
\le \frac2{\sqrt3}\prod_{i=1}^3\|A_{i,*}\|_2.
}
\]
Both coefficients are sharp. The [complete proof](PAPER.md) also classifies all equality cases: zero rows, complex monomial matrices, and rank-one matrices with a common column vector of three equal nonzero moduli.

It yields an **if-and-only-if** optimal \(L^2\) inequality for arbitrary **complex-valued** functions on three positions under a permutation law with uniform one-point marginals:
\[
\left|\mathbb E_\nu\prod_{i=1}^3 f_i(\pi(i))\right|
\le\prod_i\left(\frac13\sum_{j=1}^3|f_i(j)|^2\right)^{1/2}
\quad\text{for all } f_i:\{1,2,3\}\to\mathbb C
\]
if and only if
\[
\|\nu-u_{S_3}\|_{\rm TV}\le \frac1{\sqrt3}-\frac12.
\]
The endpoint is included. The same bound tensorizes to any number of independent, nonidentically distributed columns with complex row functions. **More strongly**, for any independent columns with \(\nu_{t_\ell}(\pi)=1/6+t_\ell\operatorname{sgn}(\pi)\), the *exact optimal amplification constant* for all complex functions is
\[
\boxed{\prod_{\ell=1}^{N}\max\left\{1,\frac{\sqrt3}{2}(1+6|t_\ell|)\right\}.}
\]
This is an equality, attained by tensor products of constant or permutation-indicator rows; it covers all \(|t_\ell|\le1/6\), including outside the stable-radius interval.

## Proof and reproduction

- [Complete mathematical proof and scope](PAPER.md), including Hermitian PSD and equality analysis.
- [Complete global norm checker](check_full_norm.py), 4,096 rational six-variable interpolation nodes for each of two identities.
- [Full complex lens checker](check_lens.py), 1,024 exact five-variable polynomial interpolation points over the rationals.
- [Separate sharp centered-disk checker](check.py), requiring only Python 3.10+ standard library and exact Q(sqrt3) arithmetic.
- [Exact complex matrix-entry regression](check_matrix.py), checking 60 independent field-valued cases.
- [Independent normalized tensor-extremizer replay](check_tensor.py), 960 exact permutation-tuple cases across ten rational parameter vectors.
- [Audit and precise trust boundary](AUDIT.md).
- Frozen results: [full norm](results/full-norm-replay.txt), [full lens](results/lens-replay.txt), [sharp disk](results/replay.txt), [matrix regression](results/matrix-replay.txt), [tensor witnesses](results/tensor-replay.txt).
- [Source hash inventory](SHA256SUMS).

From repository root:

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

Each checker must produce a byte-identical report in both Python modes, matching its frozen result.
The global norm checker works in rational arithmetic for all parameters (4,096 nodes). The full lens checker needs only rational arithmetic and \(4^5=1024\) polynomial interpolation nodes. The centered-disk cross-check uses \(\mathbb Q(\sqrt3)\) and \(4^4=256\) nodes. The analytic steps are proved in the manuscript,
not assumed from a numerical test.

## Contribution and trust boundary

The lens classification and complex absolute-value estimate **extend**, and credit, the [earlier real three-row
permanent–determinant result](../sharp-robust-permanent/paper.md#9-a-complete-sharp-radius-at-three-rows-and-exponent-two).
The earlier note already had the optimal radius for **nonnegative**
functions; the genuinely stronger content here is the exact sharp constant for all complex coefficients, the complete coefficient lens, the complex absolute-value inequality, its Hermitian certificate, complete complex equality classification, and complex-valued tensorization.
It is not a second discovery of the real radius.

The original real proof and all numbered 001--009 manuscripts are
unchanged. This is an AI-assisted research note with reproducible
exact algebra, **not** a full Lean formalization, outside human peer
review, accepted paper, or verified historical priority.
The exact complex robustness radius for \(n\ge4\) is still open
in this project.