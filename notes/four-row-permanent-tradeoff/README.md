# Sharp four-row permanent–determinant tradeoff

A complete sharp theorem for **every complex 4-by-4 matrix** and every
real determinant weight c >= 0:
\[
\boxed{
|\operatorname{per}A|+c|\det A|
\le \max\{3/2,1+c\}\prod_{i=1}^4\|A_{i,*}\|_2 .
}
\]

The bound is optimal for every c and the [proof](PAPER.md) determines
**all equality matrices**, including the critical c=1/2 transition:

- c < 1/2: precisely rank-one matrices with a common equimodular
  nonzero column vector (besides zero-row cases).
- c = 1/2: those rank-one matrices **or** complex monomial matrices.
- c > 1/2: precisely complex monomial matrices.

A stronger explicit [pairwise-deficit inequality](PAPER.md) quantifies
the transition. The same elementary method proves, for **every**
column dimension n >= 2, the sharp rectangular two-row identity
\[
\sup_{\|a\|_2=\|b\|_2=1}
\sum_{j<k}\left(
|a_jb_k+a_kb_j|^2+
c|a_jb_k-a_kb_j|^2\right)
=\max\{2-2/n,1+c\}.
\]

## Permutation application (restricted parity family)

For S4 let nu_t(pi)=1/24+t sgn(pi), with |t| <= 1/24.
All one-point marginals are uniform; TV(nu_t,uniform)=12|t|.

For **arbitrary complex** row functions the **exact** normalized L2
multilinear norm is
\[
\boxed{\kappa(t)=\max\{1,(2/3)(1+24|t|)\}.}
\]
Thus the sharp constant-one inequality holds **iff TV <= 1/4** within
this parity-mixture family, with the endpoint included.

For independent, possibly different parity-mixture laws on N columns,
the exact optimal normalized L2 amplification is
\(\prod_{\ell=1}^N\kappa(t_\ell)\). Tensor products of constants
and permutation-indicator functions attain the sharp factor.

**Important scope:** the TV radius is *not* claimed for all uniform-
one-point-marginal S4 laws; those are a larger family. Nor is the
full pencil norm claimed for nonreal determinant coefficients, or
all matrix sizes beyond four.

## Proof and exact replay

- [Full proof, including rigidity and tensorization](PAPER.md)
- [Formal polynomial-identity certificate](check.py): all two-row
  symmetric/alternating and four-row Laplace identities, checked as
  exact integer-polynomial coefficient equalities, not finite sampling.
- [Independent exact tensor witnesses](check_tensor.py): twelve rational
  parameter vectors and 43,896 enumerated permutation tuples.
- [Audit and trust boundary](AUDIT.md)
- [Frozen output](results/replay.txt), [tensor output](results/tensor-replay.txt)
  and [source-integrity inventory](SHA256SUMS).

From the repository root, Python 3.10+ standard library:

~~~sh
python3 -B notes/four-row-permanent-tradeoff/check.py
python3 -B -O notes/four-row-permanent-tradeoff/check.py
python3 -B notes/four-row-permanent-tradeoff/check_tensor.py
python3 -B -O notes/four-row-permanent-tradeoff/check_tensor.py
(cd notes/four-row-permanent-tradeoff && sha256sum -c SHA256SUMS)
~~~

Ordinary and optimized reports must match their respective frozen logs.
The polynomial coefficients and finite combinatorial identities are
exact, with integer/Fraction arithmetic and no solver or floating point.
The all-real-parameter inequalities, all-n rectangular extension,
equality cases and tensorization are *written analytic proofs*, not
merely consequences of programs printing PASS.

## Prior work and research limits

The classical Carlen–Lieb–Loss permanent-only theorem (2006) gives the
sharp coefficient n!/n^(n/2), equal to 3/2 for n=4.
Our written four-row proof is self-contained and strengthens that bound
by a **sharp simultaneous determinant term**. Its balanced two-row
method is different from the [earlier three-row complex pencil
note](../complex-permanent-determinant/README.md), whose exact
real-coefficient tradeoff is analogous but has coefficient 2/sqrt(3).
The [OpenAI four-row permanent manuscript](https://github.com/openai/math/blob/main/preprints/A-strict-four-row-permanent-inequality-and-permutation-moments-September-26-2026/build/sections/02-permanent.tex)
motivates the permutation setting.

This research note is AI-assisted and not externally peer-reviewed,
globally novelty-certified, fully Lean-formalized or an improvement of
the Thorp-shuffle mixing-time bound.