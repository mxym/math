# Two fixed-law tests of the single-threshold claims, and a Gumbel example for every finite k

This appendix uses the results and symbols in PROOF.md. The comparison is with the **single-threshold** positive claims in Livanos and Mehta, [EC 2025, Theorem 1.5, p. 1165 (restated p. 1173), and Remark 4.1, p. 1174](https://par.nsf.gov/servlets/purl/10659245). The theorem proposes an $O((\log n)^{-\gamma})$ factor for every law in the minimum domain $D_\gamma$, $\gamma<0$; the remark and the text preceding that theorem assert a bounded factor in $D_0$. The authors' [full version, arXiv:2411.19851v1, §4.1, Eq. (19)](https://arxiv.org/html/2411.19851v1#S4.SS1) replaces a quantile ratio at a multiplier growing with $n$ by a pure power of that multiplier. Regular variation alone justifies this substitution for *fixed* positive multipliers, not all growing ones. The examples do not contradict the paper's unrestricted optimal stopping theorem or its worst-case single-threshold lower bound. They are different from the bounded example outside all classical extreme-value domains in [the earlier counterexample](../fixed-law-min-prophet-counterexample/).

**Domains for minima.** With $b_n=Q(1/n)$, for every $s>0$ the minimum's survival at $Q(s/n)$ is $(1-s/n)^n\to e^{-s}$ for our continuous strictly increasing quantiles. If $Q\in RV_r$ with $r>0$, $(Q(s/n)-b_n)/(r b_n)\to(s^r-1)/r$. Monotonicity and bracketing the arguments by two such quantile points give the minimum EVT limit with survival $\exp[-(1+rt)^{1/r}]$ when $1+rt>0$, and 1 otherwise: index $\gamma=-r$ in the paper's Definition 1.2. Similarly, if $(Q(s/n)-b_n)/a_n\to\log s$ for all $s>0$ and some $a_n>0$, the standardized survival converges to $\exp(-e^t)$ for real $t$, the minimum Gumbel law $D_0$.

## Positive index: the pure big-O factor fails

Fix any $r>0$. For $y\ge e^2$ define
$$
 Q(e^{-y})=\exp[-ry-h(y)],\qquad h(y)=y/\sqrt{\log y}.
$$
Extend $Q$ continuously and strictly increasingly up to $Q(1)=1$ (linear interpolation suffices), with $Q(0)=0$. This defines a bounded continuous strictly increasing quantile and hence a nonatomic law. The extension may be smoothed away from zero; no such modification is needed. Since $h'(y)=(\log y)^{-1/2}(1-1/(2\log y))\to0$, differences $h(y+O(1))-h(y)$ tend to zero, so $Q\in RV_r$ and the law belongs to $D_{-r}$ as verified above.

Put $y=\log n$ and $s=r\log n$. Since $\log s\sim\log y$ and $h'(u)\sim1/\sqrt{\log y}$ uniformly for $y-\log s\le u\le y$, one obtains
$$
 \frac{Q(s/n)}{s^r Q(1/n)}
 =\exp[h(y)-h(y-\log s)]
 =\exp[(1+o(1))\sqrt{\log\log n}]\longrightarrow\infty.
$$
Formula (1) of PROOF.md with $k=1$ shows that *even the best* single-threshold ratio divided by $(\log n)^r$ tends to infinity for this one fixed law. Its logarithmic exponent is still $r+o(1)$, and a pure-power quantile does have asymptotic order $(\log n)^r$; those are different statements from the universal big-O assertion.

## Zero index: one lower-Gumbel law defeats every fixed threshold budget

Let $t_1=4$, $t_{j+1}=e^{t_j}$ and take $\delta(y)=1$ for $0\le y<t_1$, $\delta(y)=1/j$ for $t_j\le y<t_{j+1}$. Define $h(y)=\int_0^y\delta(z)dz$ and $Q(e^{-y})=e^{-h(y)}$ for $y\ge0$. The piecewise linear $h$ is continuous strictly increasing to infinity: on level $j$, $h(y)\ge y/j$ and $t_j/j\to\infty$. Hence $Q$ determines one bounded atomless distribution with full support $[0,1]$. For fixed $L<\infty$, $\delta(u)/\delta(y)\to1$ uniformly when $|u-y|\le L$: for large $y$ such an interval meets at most one jump and successive height ratios tend to 1. Thus, for each fixed $s>0$,
$$
 \log(Q(s/n)/b_n)
   =\int_{y-\log s}^y\delta(u)du
   =\delta(y)(\log s+o(1)),\qquad y=\log n .
$$
In particular $Q$ is slowly varying; since $\delta(y)\to0$, $(Q(s/n)-b_n)/(b_n\delta(y))\to\log s$. The minimum therefore lies in $D_0$, without presuming that slow variation by itself always implies that domain condition.

For the recursion in PROOF.md, $w_1=1+h(y)+\log\mu\ge y/(2j)$ when $y$ is on a sufficiently large level $j$. For every fixed subsequent iteration,
$$
 \log(v_i/b_n)
   =\int_{y-\log w_i}^y\delta(u)du\ge(\log w_i)/j,
 \qquad w_{i+1}\ge1+(\log w_i)/j .
$$
The integrals are in the defined range because $1\le w_i=O(1+y)=o(n)$ for fixed $i$. For each fixed $i\ge1$ we have, eventually,
$$
 w_i\ge \frac{\log^{(i-1)}y}{2j},\qquad \log^{(0)}y=y .
$$
In the induction step $\log(2j)=o(\log^{(i)}y)$ uniformly on level $j$, since $y\ge t_j$ and $\log^{(i)}t_j=t_{j-i}$ once $j>i$. Thus $\log(v_k/b_n)\ge(\log w_k)/j\to\infty$ for *every fixed* $k$. The slow-variation theorem gives $H_k(n)/M_n\to\infty$. The law does not change with $k$, and this is full-sequence divergence, not just a subsequence assertion.

**The unrestricted online cost still is asymptotic to the prophet.** Here is a direct check, in fact valid for every continuous lower quantile slowly varying at zero with finite mean. In a block with $h\ge2$ draws remaining use $m=\lfloor h/2\rfloor$ trials at quantile $p=1/m$, then recurse with $\lceil h/2\rceil$ remaining; if only the final draw remains take it. At $m=1$ use an always-accept cutoff. Index the blocks from $i=0$. Each block is reached with probability at most $e^{-i}$, since each preceding block has failure probability at most $e^{-1}$. For every fixed $i$, $p_i\sim2^{i+1}/n$, so the conditional acceptance mean $A(p_i)\sim b_n$. For an integrable uniform bound on the contributions, $h=\lceil n/2^i\rceil$ and $m\ge h/3$ when $h\ge2$, hence $np_i\le3\cdot2^i$. While $p_i\le d$ for a fixed small $d>0$, Potter bounds give $A(p_i)/b_n\le C(3\cdot2^i)^\epsilon$ for $0<\epsilon<1$. The bound $Ce^{-i}(3\cdot2^i)^\epsilon$ is summable over blocks. When $p_i>d$ (or only the forced draw remains), $h$ is bounded in terms of $d$ and $i\ge(\log n)/\log2-O_d(1)$. These last $O_d(1)$ blocks each have expected contribution at most $e^{-i}\mu=o(b_n)$, using $A(p)\le\mu$ and $b_n=n^{o(1)}$. For the finitely many first blocks, expected cost divided by $b_n$ differs by $o(1)$ from their total acceptance probability, and these probabilities over all blocks sum to one. Summable tail control now yields total cost asymptotic to $b_n\sim M_n$. The lower bound is the prophet itself. This confirms directly that it is the *bounded number of thresholds*, not unverifiable membership in a domain or any failure of the unrestricted algorithm, that produces the gap.
