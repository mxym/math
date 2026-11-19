# Two auxiliary cross-products for linear extensions of width-two posets

A five-element poset has exactly five linear extensions. Four positive gap counts give 2 on the left and 1 on the right of the auxiliary inequality CPC2 asserted at width two in Chan–Pak–Panova's *Canadian Journal of Mathematics* paper, Corollary 7.3. Poset duality gives a separate CPC1 example. The authors' previously known universal factor of two is attained even at width two; this is not a counterexample to the classical positive-gap cross-product conjecture.

[Proof and family](PROOF.md) · [Sources, including the difference between the signed and positive assertions](SOURCES.md) · [Independent internal check](REVIEW.md).

For every prescribed positive pair (k,ℓ), a two-chain witness on the minimum possible k+ℓ+3 elements has auxiliary right/left ratio ℓ/(ℓ+1). The signed-gap and absolute-rank comparisons are pinned to the openly accessible 2022 author versions. The established Graham–Yao–Yao theorem is not disputed.

Reproduce the finite arithmetic with Python's standard library:

```sh
python3 verify.py
sha256sum -c SHA256SUMS
```

Expected output: [CHECKS.txt](CHECKS.txt). The general family is proved by a binomial count, not by a finite test. AI-assisted draft, internally checked; not an external review or a claim of priority.
