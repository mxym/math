# How much uniform noise makes a binary and an m-outcome measurement compatible?

For one binary POVM and one POVM with $m$ outcomes, the largest visibility guaranteed to permit a joint measurement is
$$
s_* = \frac12\left(1+\frac{1}{1+\sqrt m}\right).
$$
This holds in every finite complex dimension $d\ge2$ and for every integer $m\ge2$. Visibility is the fraction of the original measurement retained: an $n$-outcome effect $E_i$ becomes $sE_i+(1-s)I/n$. Both measurements use the same $s$. Every pair is compatible at $s_*$; for each $s>s_*$ there is an incompatible pair.

[Bluhm, Evert, Klep, Magron and Nechita, Conjecture 6.6](https://arxiv.org/pdf/2512.17706v1) predicted this value and identified the extremal example: measure in the Hadamard and computational bases on a qubit, padding the latter with $m-2$ zero effects **before** adding noise. They proved the real-qubit case. The two-binary case and the same scalar tradeoff for a pair of mutually unbiased bases were also known. The contribution here is the matching lower bound for **every** complex binary/$m$-outcome pair, without restricting its rank, basis or dimension.

The [main proof](PROOF.md) turns the joint-measurement question into a trace-norm inequality and proves it using fidelity. A [second proof of the key inequality](TWO-PROJECTION-PROOF.md) uses only two projections and $2\times2$ determinants. Neither proof classifies all extremizers or treats arbitrary pairs in which both outcome counts exceed two.

## Reproduce the algebraic checks

Run from this directory with Python 3.8+ (standard library):

```sh
python3 -O verify.py
python3 -O independent.py
sha256sum -c SHA256SUMS
```

The first script checks an exact polynomial identity certifying the scalar bound on its full domain and the symbolic crossing; the matrix examples and the second script's rational block checks are regressions, not proofs by sampling. [Expected output](CHECKS.txt).

**Status:** AI-assisted mathematical research, independently reviewed internally by AI; not externally peer reviewed or formally verified. [Review](REVIEW.md) · [Sources and scope](SOURCES.md). No global priority claim.
