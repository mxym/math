# Can mutually unbiased measurements give the narrowest entropy range?

A pure state can produce certain outcomes in one measuring device and nearly random outcomes in another. Suppose we choose the device uniformly from a fixed list. Average the devices’ Shannon entropies, then vary the input state. How small can we make the largest value of that average? How narrow can we make its range?

[Puchała, Rudnicki, Chabuda, Paraniak and Życzkowski (2015)](https://doi.org/10.1103/PhysRevA.92.032109) proposed that a complete family of mutually unbiased bases optimizes both quantities in prime-power dimension. The defining feature of these bases gives a reason to doubt this: any vector in one basis has perfectly uniform outcomes in *every other* basis. It therefore gives an unusually **large** average entropy. Independent random bases need not have such exceptional inputs.

**Result.** In dimension $d=2^{40}$, and in all sufficiently large prime-power dimensions, there are $d+1$ projective measurements with both a strictly smaller sharp upper endpoint and a strictly narrower entropy range than **every** complete MUB design in the same dimension. The competitor is proved to exist by a positive-probability argument; its matrices are not listed explicitly. No smallest counterexample dimension is claimed.

## What is being compared?

Use the equal-weight mean $F_B(x)$ of the $d+1$ measurement entropies at pure state $x$, in nats (natural logarithms). Write $m_B$ and $M_B$ for its minimum and maximum over **all** pure states. The Haar average of $F_B$ is the same for every design: $\mu_d=\sum_{j=2}^d 1/j$. This common center makes the contrast easy to see:

| Design at $d=2^{40}$ | Sharp upper endpoint $M_B$ | Width $M_B-m_B$ |
| --- | --- | --- |
| Every complete MUB | $>\mu_d+1/4$ | $>1/4$ |
| Some tuple of $d+1$ orthonormal bases | $\leq\mu_d+1/8$ | $\leq1/4$ |

The finite proof gives an upper-endpoint improvement of more than $1/8$ nat. As $d$ increases, suitably chosen tuples have their entire range within $o(1)$ of the Haar center; every complete MUB has an input whose average entropy exceeds that center by at least $1-\gamma-o(1)$, where $\gamma$ is Euler’s constant. This does not determine the exact optimal bases, make an assertion about mixed inputs, or disprove the 2015 paper’s nonsharp analytic inequalities. Small range is not identical to small Haar variance. The [companion note](../mub-shannon-extrema-variance/README.md) concerns the different sharp *lower* endpoint in dimension three and the Haar variance in general dimension.

**中文摘要。** 对每个纯态，先求各正交测量的 Shannon 熵，再在 $d+1$ 个测量之间等权平均。在 $d=2^{40}$ 及所有充分大的素数幂维数，都存在一组测量，其平均熵的最大值与取值区间宽度同时严格小于该维数每个完整互无偏基组的对应量。证明给出概率存在性，并未逐项列出这些矩阵；比较的是实际锐端点，而不是原文的非锐解析界。

## Two routes through the proof

1. [Concentration and the common center](PROOF.md). Test a complete MUB on a basis vector. For random measurements, start from a published bound for one fixed input and one basis, then use independence and a finite covering of the sphere to control **all** inputs. This proves the finite example and the asymptotic statement, including a rate.
2. [Direct finite probability calculation](FINITE.md). Normalize independent exponential random variables to generate the outcomes of one measurement. Truncation and elementary moment estimates prove the same dimension-$2^{40}$ example without using a concentration theorem on the sphere. The [elementary asymptotic version](ELEMENTARY.md) also recalls why complete MUBs exist in the dimensions being compared.

The [independent adversarial audit](REVIEW.md) records the checks, limits, and a repair of a small-dimensional intermediate estimate in the cited concentration proof. The elementary route needs no such estimate.

## What came from earlier work

The precise sharp-endpoint claim is Conjecture 1 on [p. 032109-10](https://chaos.if.uj.edu.pl/~karol/pdf/PRCPZ15.pdf#page=10); the width proposal is on [p. 032109-1](https://chaos.if.uj.edu.pl/~karol/pdf/PRCPZ15.pdf#page=1). [McNulty and Weigert, §3.5](https://arxiv.org/pdf/2410.23997#page=18) still discussed this width conjecture in their [2026 review](https://doi.org/10.22331/q-2026-04-01-2051). [Hayden, Leung, Shor and Winter](https://arxiv.org/pdf/quant-ph/0307104#page=15) already used random measurements, entropy concentration, and sphere nets for a uniform **lower** bound. [Adamczak et al., Theorem 16](https://arxiv.org/pdf/1412.7065#page=10) obtained further random-basis uncertainty bounds; [Singh, Zhang and Pati, Theorem 1](https://arxiv.org/pdf/1509.08939#page=3) give the explicit single-basis concentration input. The random-basis method and harmonic-number center are not discoveries of this note.

Both the research draft and its separate mathematical review were AI-assisted. Neither external peer review nor formal verification has been performed. A limited literature search did not locate a refutation of the precise upper-endpoint or width statement, but does not establish priority.

## Reproduce the arithmetic

From this directory run, with Python 3 and no external dependencies:

```sh
python3 -B verify.py
python3 -BO finite_check.py
```

These files check finite rational inequalities. Their success is not an exhaustive search over states or matrices: the proofs supply that universal control.
