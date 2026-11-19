# Stockout-calibrated static thresholds in the prophet secretary problem

Yongxian Zhang (张永贤). AI-assisted research draft, November 19, 2026. Internally reviewed, not externally peer reviewed. See the [prior-work comparison](SOURCES.md).

## Model and statements

Let $V_1,\ldots,V_n$ be independent, not necessarily identically distributed, nonnegative random variables, revealed in a uniformly random permutation independent of the values. Fix selection capacity $1\le k\le n$ and benchmark capacity $1\le\ell\le n$. The offline benchmark $P_\ell$ is the expected sum of the largest $\ell$ values, with $0<P_\ell<\infty$. A static rule with price $t\ge0$ accepts the first $k$ eligible observations. A value above $t$ is eligible; one equal to $t$ is eligible with probability $\theta$, using **individual independent** coins with a common parameter. Write $D$ for the total number eligible, including those arriving after stocks have been exhausted, and $S$ for expected reward. Thus $\Pr(D\ge k)$ is the observable stockout probability, including exact exhaustion. We study the ratio of means $R=(S/k)/(P_\ell/\ell)$, equal to the usual sum ratio when $\ell=k$.

For each target $0<\phi<1$, write $p_N=p_{N,k}(\phi)$ for the unique $p\in(0,1)$ satisfying $\Pr(\mathrm{Bin}(N,p)\ge k)=\phi$ when $N\ge k$; let $B_N$ have this binomial law. Throughout $a_k(j)=\min(1,k/(j+1))$. Any ties in the stockout calibration on the constructed continuous instances do not affect their performance.

**Theorem 1 (exact finite-size envelope).** At fixed $n,k,\ell,\phi$, the infimum of $R$ over independent instances and rules calibrated to $\Pr(D\ge k)=\phi$ is
$$
  \min\left\{\frac{\mathbb E\min(k,B_n)}{k},\
     \frac{\ell}{k}H_{n-1}\right\},\qquad
  H_{n-1}=
  \begin{cases}
     \mathbb E a_k(B_{n-1}),&n>k,\\
     1,&n=k.
  \end{cases}                                                     \tag{1}
$$
The infimum is unchanged if the inputs must all be atomless or the rule may choose among calibrated prices to maximize its performance. The first coordinate involves $n$ trials, the second involves $n-1$ trials at its **own** matched parameter, not $p_n$.

For $\lambda>0$, let $Z_\lambda\sim\mathrm{Pois}(\lambda)$, $m_k(\lambda)=\mathbb E\min(k,Z_\lambda)$ and $\phi_k(\lambda)=\Pr(Z_\lambda\ge k)$.

**Theorem 2 (sharp all-horizon profile).** For fixed $k,\ell$ and target $\phi=\phi_k(\lambda)$, the infimum in Theorem 1 now also over $n\ge\max(k,\ell)$, and the limit of (1) as $n\to\infty$, both equal
$$
    \frac{m_k(\lambda)}{k}\min\{1,\ell/\lambda\}.                 \tag{2}
$$
This is uniquely maximized by $\lambda=\ell$, giving $m_k(\ell)/k$ uniformly in $n$.

Two applications have different prior status.

* At $\ell=k$, $\phi_k(k)$ attains $1-e^{-k}k^k/k!$, as conjectured by Arnosti and Ma in the closing paragraph of their Section 5. Their optimal ratio for static thresholds and a different optimal policy are **already known**; it is the proposed stockout rule that this answers. The $k=1$ case is also already known.
* For general $k,\ell$, Molina, Gast, Loiseau and Perchet established the limiting optimal static ratio for iid values and asked in their Section 6 about nonidentical laws in random order. Our $\phi_k(\ell)$ achieves that same normalized ratio for all $n$. Their prior iid upper bound then rules out any larger limiting uniform guarantee even if the price (and common tie coin) is optimized for the given instance. We do **not** infer an exact finite-$n$ optimal-instance-specific ratio from (1) or claim adaptive optimality. This conclusion is about existence of a static policy, not the heterogeneous performance of an expected-demand rule.

## Matched-tail comparison

Write $b_j=\Pr(D=j)$ for any sum of $N$ independent Bernoulli variables with individual means in $[0,1]$. These probabilities have contiguous support. The sequence $b_j/\binom Nj$ is log-concave by Newton's inequalities for the real-rooted generating polynomial $\prod_i(1-h_i+h_i z)$. This includes degenerate means: approximate by means in $(0,1)$ and pass coefficientwise to the limit. For completeness, in the nondegenerate case differentiate the polynomial $j-1$ times. For a polynomial $Q$ with $m=N-j+1$ real roots, at $0$ with $Q(0)\ne0$, writing $Q'/Q$ as a sum of root reciprocals and applying Cauchy–Schwarz gives $Q(0)Q''(0)\le(1-1/m)Q'(0)^2$. Substituting $Q(0)=(j-1)!b_{j-1}$, $Q'(0)=j!b_j$, $Q''(0)=(j+1)!b_{j+1}$ gives the normalized inequality for $1\le j<N$; the derivative has real roots by Rolle. This is a classical inequality, not a new characterization.

Consequently $b_j/q_j$ is log-concave if $q$ is any $\mathrm{Bin}(N,p)$ law with $0<p<1$ (multiply the normalized sequence by a geometric sequence). The same holds if $q$ is any $\mathrm{Pois}(\lambda)$ law with $\lambda>0$: the ratio of a binomial probability to a Poisson probability is log-concave, since the ratio of successive terms is $(N-j)p/((1-p)\lambda)$, decreasing in $j$. Multiply the two log-concave factors and extend by zero after $N$.

Suppose $q$ is such a reference law with the **same** probability $\phi$ of $j\ge k$. Then the differences $h_j=b_j-q_j$ sum to zero separately on $L=\{0,\ldots,k-1\}$ and $H=\{k,k+1,\ldots\}$ (cut off at $N$ for the binomial reference). Each part contains at least one index with $h_j\ge0$, and the set of all such indices on the reference support is an interval, by log-concavity and contiguous support. Thus on $L$ the signs can be arranged as nonpositive then nonnegative; on $H$ they are nonnegative then nonpositive (if a part is identically zero there is nothing to check). In particular, for each prefix within $L$ the cumulative difference is nonpositive and for each prefix within $H$ it is nonnegative, by the separate zero totals. This works also when $k=1$ or $k=N$ in the binomial comparison: use the weak upper level set so a part of identically zero differences is allowed. Equivalently, conditional on $L$, the Bernoulli sum is stochastically larger than the reference; conditional on $H$, it is stochastically smaller. Since $\min(k,j)$ is increasing on $L$ and constant on $H$, while $a_k$ is constant on $L$ and decreasing on $H$,
$$
 \mathbb E\min(k,D)\ \ge\ \mathbb E_q\min(k,j),\qquad
 \mathbb Ea_k(D)\ \ge\ \mathbb E_q a_k(j).                       \tag{3}
$$
The lower-side utilization extremal is related directly to earlier work of Chawla, Devanur and Lykouris. The sign argument uses the established relative-log-concavity method; see [SOURCES](SOURCES.md).

## Lower bounds for welfare

Calibration always exists. Let $Y$ be the $k$th largest value. Choose a quantile $t\ge0$ with $\Pr(Y>t)\le\phi\le\Pr(Y\ge t)$. At that price varying the common $\theta$ from 0 to 1 varies stockout continuously between these endpoints: it is a polynomial in the independent eligible probabilities $\Pr(V_i>t)+\theta\Pr(V_i=t)$. The same coupling gives monotonicity. Binomial calibration $p_N$ exists uniquely by continuity, endpoints and strict increase on $(0,1)$ (or the derivative $N\Pr(\mathrm{Bin}(N-1,p)=k-1)>0$).

Write $D_{-i}$ for demand excluding $i$. Relative order inside the set of eligible buyers is uniform. Conditional on $i$ eligible and $D_{-i}=d$, buyer $i$ receives a unit with probability $a_k(d)$. Independence across buyers gives the exact decomposition
$$
  S=t\,\mathbb E\min(k,D)+
       \sum_i \mathbb E(V_i-t)_+\,\mathbb E a_k(D_{-i}).          \tag{4}
$$
This is the revenue/surplus decomposition in the proof of Arnosti–Ma's Lemma 1, keeping each buyer's leave-one-out count rather than relaxing it to the full count. Ties contribute zero surplus. Pointwise summing only the top $\ell$ gives $P_\ell\le \ell t+\sum_i\mathbb E(V_i-t)_+$. All terms are nonnegative.

For $n>k$, $\Pr(D_{-i}\ge k)\le\phi$. Increase the other buyers' eligible probabilities along a continuous line to the vector of ones; some intermediate vector gives tail exactly $\phi$ (possibly the starting vector). Coupling by independent uniforms increases the count and hence decreases $\mathbb Ea_k$. Apply (3) to this enlarged count against $B_{n-1}$ to conclude that $\mathbb Ea_k(D_{-i})\ge H_{n-1}$. If $n=k$, $D_{-i}\le k-1$ gives $a_k(D_{-i})=1$ directly. Apply (3) to $D$ against $B_n$ for the first term of (4). Dividing the resulting bound by $k$ and comparing to $P_\ell/\ell$ proves the lower bound (1).

There is also a direct all-$n$ bound: (3) against $Z_\lambda$ for $D$, and $a_k(D_{-i})\ge a_k(D)$ pointwise, show
$$
 R\ge \min\{\mathbb E\min(k,Z_\lambda)/k,\;(\ell/k)\mathbb E a_k(Z_\lambda)\}.
$$
The Poisson shift identity $\lambda\mathbb E a_k(Z_\lambda)=\mathbb E[Z_\lambda a_k(Z_\lambda-1)]=m_k(\lambda)$, interpreting the zero term as zero, gives (2) as a lower bound. In particular the proof of Arnosti–Ma's conjecture alone needs only the Poisson comparison on the full count and their original Lemma 1.

## Upper examples and limits

Fix $n,k,\ell,\phi$ throughout this paragraph. For the first coordinate take iid uniform values on $[1,1+\varepsilon]$. The unique calibrated price is the upper-$p_n$ quantile. The accepted count is $\min(k,B_n)$ and every value in both objectives is between $1$ and $1+\varepsilon$. As $\varepsilon\downarrow0$, $R\to\mathbb E\min(k,B_n)/k$.

For the second coordinate when $n>k$, set $0<\varepsilon<\min(\phi,1/2)$ and $M=\varepsilon^{-2}$. One distinguished value is uniform on $[M,M+1]$ with probability $\varepsilon$ and on $[0,1]$ otherwise. Each of the other $n-1$ values is uniform on $[1,2]$ with probability $q_\varepsilon$, and on $[0,1]$ otherwise. Take all draws independent, and $t=1$. Choose $q_\varepsilon$ so that for $B\sim\mathrm{Bin}(n-1,q_\varepsilon)$ and independent $C\sim\mathrm{Bern}(\varepsilon)$,
$$
    \Pr(B+C\ge k)=\Pr(B\ge k)+\varepsilon\Pr(B=k-1)=\phi .
$$
The left side increases continuously and strictly from at most $\varepsilon$ to one. By continuity and uniqueness of the limiting root, $q_\varepsilon\to p_{n-1}$. The price $1$ is the only calibrated price: just below or just above it the competitors' eligible probabilities vary strictly and move the stockout probability strictly; monotonicity handles all other prices. Conditional on the distinguished value being large its probability of selection is $\mathbb E a_k(B)$, independent of its size; the prophet always includes it in that case. Other contributions are bounded by $2n+1$, while $\varepsilon M\to\infty$. Hence $R\to(\ell/k)H_{n-1}$.

If $n=k$, let all eligibility probabilities be $p=p_n=\phi^{1/n}$ at $t=1$. For each buyer put mass $1-p$ uniformly on $[0,1]$ and $p$ uniformly on $[1,2]$, except that for one buyer transfer a probability $\varepsilon<p$ from the upper uniform component to a uniform component on $[M,M+1]$ as before. Price 1 remains uniquely calibrated and all eligible buyers are served; both unnormalized rewards are $\varepsilon M+O(n+1)$. Thus $R\to\ell/k$ also at this endpoint. These are actual instances, not separate extremizers of only an auxiliary distributional lower bound. The construction styles have clear prior precedents.

For fixed $\phi=\phi_k(\lambda)$, $Np_N\to\lambda$: for any $0<x<\lambda<y$, the stockout tails of $\mathrm{Bin}(N,x/N)$ and $\mathrm{Bin}(N,y/N)$ converge to the Poisson tails at $x$ and $y$, which strictly bracket $\phi$. Monotonicity then sandwiches $Np_N$. Thus $B_n$ and $B_{n-1}$ converge in distribution to $Z_\lambda$ and bounded expectations in (1) converge. Combined with the all-$n$ lower bound this proves (2) both as a limit and an infimum.

Finally $m_k(\lambda)$ is strictly increasing, and $m_k(\lambda)/\lambda=\mathbb Ea_k(Z_\lambda)$ is strictly decreasing: use the independent-increment coupling of two Poisson laws and the positive probability of crossing a strictly varying part of the respective bounded function. This gives the unique optimum $\lambda=\ell$. At $\lambda=k$, the recursion $j\Pr(Z_k=j)=k\Pr(Z_k=j-1)$ gives $m_k(k)=k[1-\Pr(Z_k=k-1)]=k[1-\Pr(Z_k=k)]$. At any $\ell$, $m_k(\ell)/k=k^{-1}\sum_{j=1}^k\Pr(Z_\ell\ge j)$, the same incomplete-gamma expression used by Molina et al. Their Theorem 4 or Proposition 10 gives a sequence of iid instances on which even the optimal static threshold has asymptotic normalized ratio at most this number. Since these instances are admissible under uniformly random arrivals, the same upper bound applies to the optimal-static heterogeneous random-order limit; coupled with our lower bound this proves the equality claimed in the second application.
