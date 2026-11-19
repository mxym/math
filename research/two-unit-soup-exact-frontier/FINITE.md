# The exact finite-population throughput frontier at two units of supply

Yongxian Zhang

Let $X_1,\ldots,X_n$ be independent, not necessarily identically distributed random variables in $[0,1]$, with $n\ge2$. Put $S=\sum_i X_i$ and prescribe the availability $q=\Pr(S<2)$. The least possible absolute throughput $\mathbb E\min(S,2)$ is **attained by iid unit Bernoulli demands**: choose their success probability $p\in[0,1]$ so that $\Pr(\operatorname{Bin}(n,p)<2)=q$. Relative throughput is half the absolute throughput. More explicitly, the maximum shortage $H=\mathbb E(2-S)_+$ is
$$
 H_{n}(q)=q+z^n,\qquad nz^{n-1}-(n-1)z^n=q,\qquad z=1-p\in[0,1].
$$
The equation has a unique solution, since its left side increases strictly from zero to one (derivative $n(n-1)z^{n-2}(1-z)>0$ in the interior). The theorem includes both endpoints; for $n=1$ only $q=1$ is possible.

**Proof.** Write $f=(1-S)_+$, $a=\mathbb E f$, and $f_i=(1-S+X_i)_+$. We first prove the two pointwise inequalities
$$
 f^{n-1}\le\prod_i f_i,\qquad
 \sum_i(f_i-f)\le\mathbf1_{S<2}-f. \tag{1}
$$
For $S<1$, $f_i=f+X_i$ and $\prod_i(1+X_i/f)\ge1+S/f=1/f$, giving the first one. The sum is $S$, giving equality in the second. For $1\le S<2$ the first inequality is automatic. Put $b=S-1$; then $\sum_i(f_i-f)=\sum_i(X_i-b)_+\le1-b\le1$. If exactly one term is positive this uses $X_i\le1$, and if at least two are positive it uses $\sum_iX_i-2b=1-b$. If none is positive it is immediate. For $S\ge2$ every function vanishes.

Each $f_i$ omits input $i$. Consequently the product-space generalized Hölder (functional Loomis–Whitney) inequality and AM–GM give
$$
 a\le \mathbb E\prod_i f_i^{1/(n-1)}
     \le \prod_i (\mathbb E f_i)^{1/(n-1)},\qquad
 \sum_i\mathbb E f_i\ge n a^{1-1/n}.
$$
For clarity, the generalized Hölder bound follows by integrating one coordinate at a time: at the step for variable $j$ the $j$-th factor does not depend on it; to the other $n-1$ factors apply Hölder with equal exponents $n-1$, replacing each underlying function $f_i$ by its conditional average over that variable. The exponent $1/(n-1)$ remains the same. Iteration leaves the individual expectations. This applies also to $n=2$ and to zero-valued functions.

The second inequality in (1) therefore gives $q\ge n a^{1-1/n}-(n-1)a$. By monotonicity of the equation for $z$ we obtain $a\le z^n$. Finally $(2-S)_+\le\mathbf1_{S<2}+f$ pointwise, yielding $H\le q+z^n$. For $X_i$ iid Bernoulli$(1-z)$ we have $a=z^n$, $q=z^n+n(1-z)z^{n-1}$ and equality in the claimed shortage formula. This proves optimality rather than just exhibiting an approximation.

**Poisson limit.** The [Ganesh–Hartline–Sinha–vonAllmen soup-kitchen conjecture](https://arxiv.org/html/2402.19292v3) compares the same two quantities to ordinary unit-jump Poisson demand without fixing $n$. At $0<q<1$ let $(1+\lambda)e^{-\lambda}=q$. If $a>0$ then $n(a^{-1/n}-1)\ge-\log a$, so the proof implies $q\ge a(1-\log a)$ and hence $a\le e^{-\lambda}$; $a=0$ is immediate. Thus $H\le(2+\lambda)e^{-\lambda}$. This is sharp in the closure: as $n\to\infty$ choose the iid Bernoulli parameter $p_n$ by the exact-$q$ construction; bracketing $np_n$ by fixed constants on either side of $\lambda$ and using the binomial-to-Poisson limit yields $np_n\to\lambda$ and $H_n(q)\to q+e^{-\lambda}$. At $q=1$ take $\lambda=0$. At $q=0$ shortage is zero, the frontier point is $(q,\text{relative throughput})=(0,1)$, approached only as $\lambda\to\infty$ on the Poisson curve; no finite Poisson has zero availability. This is an exact two-unit result for real-valued demands, not a theorem about all integer or real supplies.
