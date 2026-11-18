# Exact two-adic orders of elementary symmetric Boolean exponential sums

**Research draft, internally AI-reviewed, not externally peer-reviewed or formally verified.** This note gives a proof of the formula stated in [Castro, González, Medina, Negrón and Rubio, Conjecture 6.1, p. 9 (January 2017)](https://ccom.uprrp.edu/~labemmy/Wordpress/wp-content/uploads/2022/12/Raul-Oscar-paper.pdf), for the ordinary domain of a degree-$k$ polynomial in $n$ variables: $1\le k\le n$. It does **not** settle the [general 2008 Cusick–Li–Stănică balancedness conjecture](https://arxiv.org/abs/math/0608369).

For integers $a\ge2$, $s\ge0$, $i\ge2^{s+1}+s$, $r=0,1$ and positive odd $m\le2^s$, let
$$
n=2^a(2^i-1)+r,\qquad k=2^a(2^{i-s}m-1),\qquad \ell=\lfloor\log_2m\rfloor .
$$
The two-adic valuation of the exponential sum of $\sigma_{n,k}$ is $2(2^s-1)+r+1$ if $m=1$, and $2^{s-\ell}-w_2(m)+\ell+r+1$ otherwise. Here $w_2$ is binary digit sum. The natural degree restriction is equivalent to $m\le2^s$; extending the formula to arbitrary odd $m$ is false.

[Full proof](PROOF.md) · [Independent mathematical review and literature limits](REVIEW.md) · [Numerical check descriptions](CHECKS.md)

## What is different from earlier work?

- The two-branch formula is the **2017 authors' conjecture**. Their Theorems 3.1 and 4.1 already prove certain exact cases; Theorems 4.2 and 4.5 give related lower bounds. Their Conjecture 4.4 has a different gap threshold and is not claimed here at that threshold.
- [Su–Tang–Pott, Theorem 5(ii)](https://arxiv.org/pdf/1203.1418) already implies nonbalancedness when $m>2^{s-1}$ in this family. Nonbalancedness alone does not determine the exact valuation.
- [Tollisen–Lengyel](https://www.kurims.kyoto-u.ac.jp/EMIS/journals/INTEGERS/papers/e4/e4.pdf) established valuation results for single lacunary residue classes. Here the key extra step computes the cancellation across a union of $2^f$ such classes selected by freely varying bits. The [2015 Castro–González–Medina boundary paper](https://link.springer.com/article/10.1007/s12095-015-0124-y) is a further exact-divisibility predecessor; the publisher preview is incomplete. The absence of an earlier full proof was not certified; there is **no priority claim or guarantee**.

## Reproduce the finite checks

With standard-library Python 3.10 or later, from this directory:

```sh
sha256sum -c SHA256SUMS
python -B -O check.py
python -B -O independent.py
```

The author's program directly tests 768 restricted rows, 181 original-weight cases (including some smaller-gap stress cases), and 238 original-domain modular cases. The independent program tests 1,408 cyclic/negacyclic splits and 56 original cases across 38 fully streamed Pascal rows through $n=2{,}097{,}149$. Neither script relies on Python assertions. These checks are reproducibility evidence, not a proof over infinitely many parameters.
