# When can a weighted difference increase Rényi entropy?

Take two independent copies $X,X'$ of the same random vector and subtract one from the other, after giving them weights $\lambda,\mu>0$ with $\lambda+\mu=1$. Can the result have higher entropy than either input? For log-concave densities, [Han, Zhan, Zhou and Zhu, Theorem 3](https://arxiv.org/html/2610.15716v1) prove the answer is **no** for Shannon entropy and all higher Rényi orders. Below order one, Rényi entropy gives greater weight to regions of small density. There the answer can change, even in the plane.

**The weights matter.** Fix any dimension $n\ge2$. For *each* $0<p<1$ there exist a log-concave density and positive weights for which
$$
h_p(\lambda X-\mu X')>h_p(X).
$$
One choice is $\mu=(1-p)^3/4$, $\lambda=1-\mu$; the law also depends on $p$. Together with the known positive theorem, this makes $p=1$ the exact threshold in each such dimension **when the inequality is required for every pair of weights**. This is not a claim that every pair fails below one.

**Equal weights.** Here we prove failure for $0<p<2-2^{1/n}$. For example, in dimension two, $p=4/7$ admits an explicit counterexample whereas the uniform triangle does not. The example has density proportional to
$$
\mathbf1_{\{x,y\ge0\}}\exp\!\left[-x-y-2^{-1512}\exp\!\left(\tfrac9{16}(x+y)\right)\right].
$$
Two rational estimates certify the sign without numerical integration. The [authors' earlier simplex examples, Theorem 5](https://arxiv.org/html/2610.15716v1), already show failure for any fixed $p<1$ in all sufficiently large dimensions. We do **not** determine the optimal unweighted constant, its extremizers, or the full set of orders giving equality in their fixed-dimensional question (61).

**Idea of the proof.** Independent exponential coordinates begin exactly at equality. We steepen their joint density in the tail. After differentiation, the entropy change is expressed in terms of two mixtures of elementary exponential laws. How much mass these mixtures put on their longest common scale decides whether this kind of perturbation can increase entropy.

- [Proof: criterion, quantifiers and finite counterexample](PROOF.md)
- [Independent mathematical review and second rational certificate](REVIEW.md)
- [Earlier results and limits of the search](SEARCH.md)

**中文摘要。** 固定任意维数 $n\ge2$，若要求加权差熵不等式对所有正权重都成立，准确门槛是 $p=1$：每个 $0<p<1$ 都有依赖于阶数的权重与对数凹反例。上界方向来自 Han、Zhan、Zhou、Zhu。两权相等时这里只证明 $p<2-2^{1/n}$ 的严格反例；没有求出一般等权最优常数。平面 $p=4/7$ 的显式例子有两份独立的有理估计。

**Reproduce:** from this directory, run the following with Python 3.8+ (standard library).
```sh
python3 -BO verify.py
python3 -BO independent.py
sha256sum -c SHA256SUMS
```

**Status:** AI-assisted research, including independent internal AI mathematical review. Not externally peer reviewed or formally verified. No claim of historical priority.
