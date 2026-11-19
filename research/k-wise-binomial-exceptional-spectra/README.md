# Which probabilities recur at exceptional transitions of optimal four- and six-wise independent bits?

**Yongxian Zhang · 19 November 2026**

For each number of bits $n$, maximize the chance that all bits equal one, subject to $k$-wise independence and a common Bernoulli probability $p$. As $p$ increases, the optimal count distribution changes support. Following [Berend, Ernst, Kontorovich and Kumar, §5](https://doi.org/10.1007/s10959-026-01487-4), a transition between consecutive positive-length phases is *exceptional* if at least two actual basis sites leave together. Fix $p$ and vary $n$. Which probabilities are exceptional infinitely often?

* **Four-wise:** every rational $0<p<1$ occurs infinitely often, and no irrational $p$ occurs at all. Nevertheless the integers $n\le X$ with any exceptional transition have density zero: their number lies between $c\sqrt X\log X$ and $C\sqrt X(1+\log X)^8$ for absolute $c,C>0$ and all sufficiently large $X$. Thus the power $1/2$ is sharp; the logarithmic order is not determined. [Proof and arithmetic test](FOUR-SPECTRUM.md)
* **Six-wise:** the only $p$ occurring infinitely often is $1/2$. At $p=1/2$, write $N=n-1$. Exactly two lists occur: $N=(4j^2+2)/3$ for $j\ge3$ not divisible by three (three departing sites), and $N=3h^2$ for odd $h\ge3$ (two). Their combined count up to $n\le X$ is $(\sqrt3/2)\sqrt X+O(1)$. A fixed nonsymmetric rational can occur at only finitely many sizes; this is not a proof that such sporadic exceptions never occur, or a count allowing $p$ to vary with $n$. [Proof](SIX-RECURRENCE.md)

The finite data in the original paper, the classical binomial quadrature inputs, and the earlier rationality implications at $k=4,6$ are prior. The statements above concern **recurrence across sizes**. They do not settle Conjecture 5.9 for general $k$. See the [source and overlap comparison](SOURCES.md).

## Reproduction

From this directory, verify the file hashes and reproduce the recorded checks (Python 3 and SymPy, tested with 1.14.0):

```sh
sha256sum -c SHA256SUMS
(python3 -B -O check.py && python3 -B -O symbolic.py) | diff - CHECKS.txt
```

The standard-library checker independently tests candidate supports; the symbolic checker reconstructs the quartic equations and elimination coefficients from the roots and binomial moments. Neither finite enumeration establishes the infinite-size results. [Four-wise internal review](FOUR-REVIEW.md) · [Six-wise internal review](SIX-REVIEW.md). AI-assisted research, with an independent internal AI proof review; not externally peer reviewed. The bounded literature comparison is not a claim of worldwide priority.
