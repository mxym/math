# Odd iid lattice sums can be arbitrarily more concentrated with nonunit coefficients

**Yongxian Zhang · working paper · 19 November 2026.** AI-assisted with separate AI-assisted internal proof review; not externally peer-reviewed. No global priority claim.

Given independent copies of the **same** random integer, must some choice of signs produce at least as large an atom as every weighted sum? [Juškevičius and Kurauskas, §5, Conjecture 1](https://web.vu.lt/mif/v.kurauskas/files/2020/08/general_200704.pdf) asked this for lattice random vectors. They proved it for even numbers of terms.

**For every fixed odd number of terms $n\ge3$, the ratio can be arbitrarily large**, already for a uniform law on a finite subset of the integers. The competing nonunit coefficients are positive integers and can be kept fixed while the underlying set varies. Thus the unrestricted worst-case comparison factor is exactly 1 for even $n$ and infinite for odd $n\ge3$; it is 1 trivially for $n=1$.

There are two kinds of witnesses:

- The [explicit construction](PROOF.md) gives a rational, finitely supported law. With three summands one 512-atom law gives peak numerator **994151968413120** with coefficients $(1,1,10)$ versus **977280228179739** with the best signs, with the same denominator. The proof for all odd $n$ uses two biases: nearly rare Bernoulli digits favor balanced signs, while almost fair ones favor equal signs. A place-value shift lets the nonunit coefficients realize both local optima in one iid integer law.
- The [uniform-set extension](UNIFORM.md) proves existence of finite sets by independent sampling of extra labels. It does not present the 512-atom weighted example as a uniform-set example.

This resolves the **fixed-law** sign comparison, not the different question of optimizing over all laws subject to caps on their largest atoms. The [three-summand cap theorem](../three-summand-point-concentration/README.md) compares against *different* laws. Nor does this contradict sign optimality for iid Bernoulli summands.

[Sources and scope](SOURCES.md) · [main internal review](REVIEW.md) · [uniform-set internal review](UNIFORM-REVIEW.md).

~~~sh
sha256sum -c SHA256SUMS
python3 -O verify.py | diff - CHECKS.txt
python3 replay.py | diff - REPLAY-CHECKS.txt
~~~

The first checker enumerates the actual one-dimensional sum laws, including all 393,216 distinct totals of the weighted triple; the second independently computes each column and returns integer targets attaining the tabulated modes. These are checks of the finite example, not a substitute for the all-odd proof.
