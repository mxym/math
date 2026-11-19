# Which sign count gives the largest Bernoulli atom?

Yongxian Zhang

For an odd number of independent Bernoulli draws with fixed non-fair rational bias of even denominator, we prove the eventual periodicity asked for in [Singhal's Conjecture 4.1](https://arxiv.org/pdf/1912.02886v2). Singhal had already proved that signs attain the optimum among all nonzero real weights, and found the leading slope of the optimal sign count. Here the exact eventual count, its unique mode, and the **least even period** of the centered count follow by comparing adjacent integer candidates.

For example, at bias $1/4$ the centered count has least period 20 on odd sample sizes. At $n=201$ exact enumeration gives 161 positive signs and 40 negative signs, with most likely sum 30; at $n=221$ the eventual rule predicts 177 positive signs. We orient the signs so that at least half are positive. This does not classify all extremizing nonunit weights, give a uniform starting length, or apply the periodicity law to irrational biases. See the [proof](PROOF.md), [prior work and scope](SOURCES.md), and [independent internal review](REVIEW.md).

**Reproduction.** From this directory run:

```sh
sha256sum -c SHA256SUMS
python3 -O verify.py | diff - CHECKS.txt
python3 derive.py | diff - DERIVE-CHECKS.txt
```

The first Python script needs only the standard library; its 42 finite checks enumerate every sign count (up to global reversal) and every target by exact polynomial arithmetic, rather than sampling sums. The second, independently written, uses SymPy to recompute the two Gaussian coefficients symbolically; its two zero outputs are the leading expectation and the difference between the derived and stated shift. The general proof is analytical, not a consequence of the finite tests.

AI-assisted research manuscript with independent AI-assisted internal mathematical review. Not externally peer reviewed; no guarantee of priority.
