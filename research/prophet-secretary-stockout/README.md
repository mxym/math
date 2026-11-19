# A sharp stockout rule for the multi-unit prophet secretary problem

**Yongxian Zhang (张永贤) · Research draft · November 19, 2026.** AI-assisted, with a separate internal mathematical review; not externally peer reviewed.

Suppose independent buyers with different value distributions arrive in a uniformly random order. A seller posts one price and accepts up to $k$ eligible buyers. Can the seller obtain the best possible worst-case welfare simply by targeting the probability of selling all $k$ units? **Yes.** The target is the chance that a Poisson random variable of mean $k$ is at least $k$. At that target, the seller achieves the known sharp ratio $1-e^{-k}k^k/k!$. The constant itself, and a different rule attaining it, were proved by [Arnosti and Ma](https://www.columbia.edu/~wm2428/papers/prophet_secretary.pdf). The rule based specifically on stockouts was their conjecture at the end of §5.

The same calculation answers a second question: if the offline benchmark averages the top $\ell$ values while the online seller has $k$ units, does the optimal large-horizon static guarantee for iid inputs persist for nonidentical inputs arriving in random order? The answer is again yes, with a target depending only on $k$ and $\ell$. This is the random-arrival question in [Molina, Gast, Loiseau and Perchet, §6](https://arxiv.org/pdf/2408.07616v2), not an assertion about adaptive stopping.

## Sharp statements

* **At every prescribed stockout target**, the worst ratio at finite $n$ is given by two explicit binomial expectations (Theorem 1). The utilization term matches the tail with $n$ buyers; when $n>k$, the surplus term matches it separately with $n-1$ competitors (if $n=k$, every eligible buyer is served). Continuous value distributions with a unique calibrated price approach each term.
* **Over all horizons**, write the target as $\Pr(Z_\lambda\ge k)$, where $Z_\lambda$ is Poisson with mean $\lambda$. The exact worst ratio of the online average to the offline average is
  $$\frac{\mathbb E\min(k,Z_\lambda)}{k}\min\{1,\ell/\lambda\}.$$
  It is uniquely maximized at $\lambda=\ell$. The published iid asymptotic upper bound then establishes sharpness even among instance-optimized static rules. At **finite** $n$, our exact formula is for **stockout-calibrated** rules; it does not optimize over all prices for each instance.

The proof uses classical relative log-concavity and the revenue/surplus decomposition of Arnosti and Ma. The one-sided throughput extremal at fixed availability, its Poisson limit, and the equal-capacity iid fixed-quantile calculation all have precedents. [Source comparison](SOURCES.md) gives attribution and limits of the search; there is no claim to historical priority.

**Read:** [full proof](PROOF.md) · [sources](SOURCES.md) · [independent internal review](REVIEW.md).

**Replay:** run these from this directory using Python 3.10+ (standard library only).

```sh
python3 -O verify.py | diff - CHECKS.txt
python3 -O independent.py | diff - INDEPENDENT-CHECKS.txt
sha256sum -c SHA256SUMS
```

The first script checks exact tail-matched comparisons, the welfare decomposition and extreme examples. The second enumerates every eligibility assignment on small rational grids and brackets the calibration with independent rational bisection. These are finite checks, not substitutes for the quantified proof.

**中文摘要。** 对于独立但不同分布、随机顺序到达的买家，只按售罄概率校准一个固定价格，即可达到已知的最优福利保证。本文给出任意售罄目标、任意有限人数下该类规则的精确最坏比值；在所有人数上的唯一最优目标是均值为 $\ell$ 的泊松变量至少为 $k$ 的概率。这里 $k$ 是在线选择数，$\ell$ 是离线基准选取数。不涉及自适应定价的最优性。
