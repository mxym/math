# Two restricted-family corrections and an alphabet-uniform lower bound for non-overlapping codes

**Yongxian Zhang · Research draft · 19 November 2026.** AI-assisted mathematics and independent internal AI review; not external peer review. The [source comparison](SOURCES.md) is bounded, not a guarantee of priority.

For words of length $n$ over $q$ symbols, distinguish the largest **one-run** code $S(n,q)$ in Chee–Kiah–Purkayastha–Wang's Eq. (5) from the optimum $C(n,q)$ over **all** non-overlapping codes.

* **The restricted liminf is smaller than the value printed in Theorem 4.2, Eq. (9).** At each fixed $q\ge2$, the liminf and limsup of $nS(n,q)/q^n$ are respectively $(\log q)/q^{q/(q-1)}$ and $(q-1)/(qe)$, with a uniform-in-length additive $O_q(\log n/n)$ approximation to the full phase profile. In binary, these are $\log(2)/4$ and $1/(2e)$. The two constants, the code and the optimizing lattice phase as a **lower-bound** calculation are already explicit in Levenshtein (1964), §2, Lemma 2. The point here is the *matching upper bound over every eligible run length*, not discovery of the oscillation or its constants.
* **Theorem 4.1, Eq. (6), also fails for every fixed $q\ge8$.** Along the low phase the one-run construction is too small relative to the unrestricted optimum. This does **not** refute their Theorem 1.1, Eq. (1), for $C$. The contradiction does not require the [repository's fixed-alphabet upper bound](../non-overlapping-codes-leading-constant/README.md).
* **One lower bound works simultaneously for all $q\ge2$.** There are absolute $A,n_0$ such that $nC(n,q)/q^n\ge(q-1)/(qe)-A(1+\log_q n)/n$ for all $n\ge n_0$. A family of short markers calibrates a longer dictionary to probability $1/n$ without an alphabet-sized rounding loss. With Levenshtein's classical upper bound alone this gives $nC(n,q(n))/q(n)^n\to1/e$ whenever both $n$ and $q(n)$ tend to infinity. The fixed-alphabet assertion and the method of using a dictionary of markers predate this note.

[Proof of the profile and construction](PROOF.md) · [Ratio calculation and dependencies](RATIO.md) · [Historical and 2026 comparisons](SOURCES.md) · [Internal proof review](REVIEW.md) · [Internal ratio review](RATIO-REVIEW.md).

**Reproduce the finite checks** (Python standard library):
```sh
sha256sum -c SHA256SUMS
python3 -B -O verify.py | diff -u CHECKS.txt -
```
These finite exact checks verify counts, occurrence formulas and examples; the limiting statements are proved analytically.
