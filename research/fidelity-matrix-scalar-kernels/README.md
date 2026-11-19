# When are matrices of pairwise quantum fidelities positive?

**Yongxian Zhang (张永贤) · Research draft · November 19, 2026.**

Let $R(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1$ be root fidelity and $F=R^2$ the squared Uhlmann fidelity. This note addresses two questions about positive semidefinite kernels on mixed states.

1. **Powers for a fixed list size.** Requiring $[F_{ij}^{\alpha}]$ to be positive semidefinite for every $K$-state list in every finite dimension allows all $\alpha>0$ for $K\le 2$, precisely $\alpha\ge 1/2$ for $K=3$, and **no positive exponent** for $K\ge4$. For every *prescribed* $\alpha>0$, four isospectral full-rank real qutrits with rational entries suffice. At $\alpha=1$ an explicit example has eigenvalue $(4-\sqrt{17})/5<0$, and both list size 4 and dimension 3 are minimal.
2. **All scalar functions, unrestricted list size and dimension.** With no continuity or measurability assumption, $[f(R_{ij})]$ is positive semidefinite for every list if and only if $f(r)=c$ for $0\le r<1$, with $0\le c\le f(1)$. The possible jump at 1 represents equality of the two states. In particular every continuous universal transform is constant. This does **not** classify arbitrary kernels in each fixed dimension.

[Fannes–de Melo–Roga–Życzkowski (2012), §4, p. 484](https://chaos.if.uj.edu.pl/~karol/pdf/FMRZ12.pdf) reported a numerical suggestion for **four mixed states and squared fidelity**. Their established four-state obstruction for *root* fidelity, and their separately numbered three-state Holevo conjecture, are different matters. Nonpositivity of fidelity matrices in general, and the two-mutually-unbiased-bases construction used to probe the exponent, are earlier observations. The prior-source comparison includes Sun–Luo–Lei (2021) and states the limits of the full-text search.

**Read:** [proof and explicit matrices](PROOF.md) · [prior work and search limitations](SOURCES.md) · [independent internal mathematical review](REVIEW.md).

**Reproduce:** from this directory, run `python3 -O verify.py` (standard library only) and compare [expected output](CHECKS.txt). The checker verifies the explicit algebra and sign tests for sample rational parameters. The quantified results are proved in the text, not inferred from samples. The published proof body is unchanged from the internally reviewed copy; only its draft-status line changes. The [hash manifest](SHA256SUMS) covers the public copies. AI-assisted derivation and separate internal AI review are not external peer review, independent human certification, Lean formalization, or a guarantee of historical priority. No result about Holevo entropy or a Gaussian covariance kernel is claimed here.

**中文摘要。** 对任意有限维混态，平方保真度矩阵逐项取正幂后，若要求对每个长度为 $K$ 的系综都半正定，则 $K=3$ 的精确范围为 $\alpha\ge1/2$，$K\ge4$ 时不存在这样的正指数。每个指定指数都可用四个满秩、实有理、等谱的三能级态构成反例。若允许态数和维数一起变化，任意只依赖两态保真度的普适半正定核，在两个态不相等时必须取同一常数；不假设函数连续。
