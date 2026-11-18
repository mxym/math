# Two Shannon-entropy comparisons for mutually unbiased bases

Let a pure state $\psi$ be measured in orthonormal bases $B_b=(u_{bi})_i$ of $\mathbb C^d$. The outcome probabilities are $p_{bi}=|\langle u_{bi},\psi\rangle|^2$, and $H_b=-\sum_i p_{bi}\log p_{bi}$ is the Shannon entropy with natural logarithms. Two bases are mutually unbiased (MU) if every squared overlap between them is $1/d$.

In [*Certainty relations, mutual entanglement, and nondisplaceable manifolds*](https://doi.org/10.1103/PhysRevA.92.032109), Puchała, Rudnicki, Chabuda, Paraniak and Życzkowski (2015) asked whether a complete set of $d+1$ MU bases maximizes the lower endpoint and minimizes the upper endpoint of the average entropy (Conjecture 1), and minimizes its standard deviation over Haar-distributed pure states (Conjecture 2). The conjectures appear together in the [published text, p. 032109-10](https://chaos.if.uj.edu.pl/~karol/pdf/PRCPZ15.pdf#page=10).

**The sharp lower endpoint does not behave as conjectured.** In dimension three, keep three standard MU bases and apply $\mathrm{diag}(1,e^{it},e^{2it})$ to the fourth. The minimum $m(t)$ of the equally weighted average over all pure states satisfies
$$
 m(t)=\log 2+\frac{t^2}{48}\log(1/t^2)+O(t^2).
$$
Thus even a small perturbation raises the minimum above the complete-MUB value $\log 2$. The [qutrit proof](QUTRIT.md) controls the minimization over moving states; a [fully specified algebraic unitary](QUTRIT.md#a-fully-specified-algebraic-unitary) also gives a direct strict certificate. This is a statement about the sharp lower endpoint, not an assertion that every state's entropy increases relative to its own former entropy.

**The minimum-variance assertion holds.** For arbitrary fixed positive weights summing to one, if $L$ pairwise MU bases exist in $\mathbb C^d$, the Haar variance of $\sum_b w_b H_b$ is minimized exactly by such tuples. The [variance proof](VARIANCE.md) gives the variance difference as an explicit sum of nonnegative powers-of-overlap deficits, including a quantitative gap. Its equal-weight, complete-MUB specialization proves the Shannon assertion of Conjecture 2. This does not assume the existence of a complete MUB in arbitrary dimension.

**中文摘要。** 四组 qutrit 基的最小平均 Shannon 熵可在完整互无偏基附近由一个显式微扰严格提高，反驳猜想 1 关于锐下端点的断言；本文不处理上端点。猜想 2 方向相反地得到肯定：当给定数量的互无偏基组存在时，它们恰好最小化 Haar 纯态上的平均 Shannon 熵方差，且有显式方差差值公式。

## Prior work and scope

The 2015 paper distinguished numerically optimized endpoints from particular analytic bounds and proved an order-two Tsallis variance analogue in [Appendix C](https://link.aps.org/accepted/10.1103/PhysRevA.92.032109). The claims here concern **Shannon** entropy. The lower-endpoint and variance arguments here do not address the sharp upper endpoint, interval width, mixed-state variance, or the MUB existence problem.

**Subsequent result ([companion note](../mub-shannon-upper-endpoint-width/README.md), [#60](https://github.com/mxym/math/pull/60)).** For $d=2^{40}$ and all sufficiently large prime-power dimensions, the later draft gives a probabilistic counterexample: some tuple of $d+1$ bases has both a smaller sharp upper endpoint and a narrower range than every complete MUB in that dimension. This rules out the proposed MUB optimality in those dimensions; it does not identify the actual optimal values or basis tuples. The result is AI-assisted and internally reviewed, not externally peer reviewed.

**后续进展。** [后续稿](../mub-shannon-upper-endpoint-width/README.md)在 $d=2^{40}$ 及所有充分大的素数幂维数给出概率存在性反例：完整互无偏基组既不使锐上端点最小，也不使区间宽度最小。两个优化问题的真正最优值与最优基组仍未由这两篇稿件确定。

The collision identity, the qutrit MUB entropy minimum, and the Hesse states are prior facts. Relevant sources include [Dall'Arno (2014), Corollary 1](https://arxiv.org/pdf/1409.0341#page=5), [Stacey on qutrit SIC/MUB geometry](https://arxiv.org/abs/1404.3774), [Riccardi–Macchiavello–Maccone (2017)](https://arxiv.org/abs/1701.04304) and the [Serino et al. experiment](https://arxiv.org/abs/2507.05025). [Brierley–Weigert–Bengtsson](https://arxiv.org/abs/0907.4097) establish uniqueness of complete qutrit MUBs up to equivalence. [Huang et al., Fig. 3(d)](https://journals.aps.org/prresearch/pdf/10.1103/PhysRevResearch.6.013127#page=5) compare analytic lower bounds for another four-basis qutrit family; this differs from the actual statewise minimum off the MUB point. The Gaussian overlap transform and the Laguerre expansion used to cross-check it are classical probability identities, not claims of new probability theory.

This research draft and its [separate adversarial internal review](REVIEW.md) were AI-assisted. No external peer review or formal verification has been performed. Targeted searches found no earlier proof of the two precise comparisons, but do not establish priority.

## Verification

From this directory:

```sh
python3 -BO verify.py
python3 -B check_independent.py
OPENBLAS_NUM_THREADS=1 python3 -B diagnostics.py
```

The first command uses only the Python standard library and checks exact identities in the Eisenstein field and exact rational coefficients; it explicitly raises on failure even under Python's optimization flag. The second requires mpmath and uses independent spectral and Haar-moment calculations at high precision. The third requires NumPy and SciPy; its local optimizations and qubit spherical quadrature are numerical diagnostics, not a global optimization certificate. The analytic proofs establish the universal statements.
