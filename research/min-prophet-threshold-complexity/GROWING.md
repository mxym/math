# The threshold complexity of a constant factor is log-star, up to an additive constant

Use the same one-choice model as in PROOF.md and suppose $Q\in RV_r$ with $r>0$. Define $T_0=1$, $T_{j+1}=\exp(T_j)$ and $\log^* x=\min\{j\ge0:x\le T_j\}$ for $x>0$. Write $b_n=Q(1/n)$ and $\Lambda_r=(1+r)^r/\Gamma(1+r)$, the limiting unrestricted optimal ratio. For integer budgets $k(n)\ge1$:
* $H_{k(n)}(n)/M_n$ stays bounded if and only if $\log^* n-k(n)$ stays bounded above.
* For every fixed target $C>\Lambda_r$, the *least* number of thresholds attaining ratio at most $C$, for all sufficiently large $n$, is $\log^*n+O_{F,C}(1)$ at horizon $n$. In particular, $k(n)-\log^* n\to+\infty$ suffices for asymptotic recovery of the unrestricted ratio. No claim about exact attainment at the boundary $C=\Lambda_r$ is made.

The statements are for one fixed law and positive index. They are not uniform in that law, and do not result from applying a fixed-$k$ error term at a growing $k$.

## Lower bound uniform in the budget

As in PROOF.md, $H_k(n)\ge B_n^{\circ k}(\mu)$, by an exact finite-horizon relaxation. For $0<v\le\mu$, write $z=v/b_n$. There exist $a,c>0$ and $z_0$ depending only on $F$ such that for all sufficiently large $n$ and all $z\ge z_0$ in this range,
$$
 B_n(v)/b_n\ge c(\log z)^a.                                            \tag{1}
$$
Indeed set $w=\log z$, $p_0=w/(2n)$. Uniformly $w\le\log(\mu/b_n)=O(\log n)$ and $p_0\to0$. For $p\le p_0$ the failure term normalized by $b_n$ is at least $\exp(w/2-O(w^2/n))$. For $p>p_0$ the success probability is at least $1-e^{-w/2}$, and $A(p)\ge A(p_0)\ge c_1 Q(p_0)$ by Karamata. Potter's lower bound applied at $1/n$ and $w/(2n)$ gives $Q(p_0)/b_n\ge c_2 (w/2)^{r/2}$ for $w\ge2$. These estimates give (1) with $a=r/2$.

Set $z_j=\max(2,B_n^{\circ j}(\mu)/b_n)$. Since all input costs are $\le\mu$, increasing constants $A,B\ge1$ if needed gives the uniform inverse inequality $z_{j-1}\le\exp(Az_j^B)$ for every step (the bounded $z_{j-1}$ case is automatic). If the final ratio is bounded, then $z_k\le C'$ since $M_n/b_n\to\Gamma(1+r)$. Choose $J$ so large that $C'\le T_J^{1/(2B)}$ and $A\sqrt{T_j}\le T_j/(2B)$ for all $j\ge J$. Thus $u\le T_j^{1/(2B)}$ implies $\exp(Au^B)\le T_{j+1}^{1/(2B)}$. Inducting backwards $k$ times bounds $z_0\le T_{J+k}^{1/(2B)}$. Since $\mu/b_n=n^{r+o(1)}$, $n\le\exp(z_0)$ for large $n$. It follows that $\log^* n\le J+k+1$. The argument works on any subsequence with bounded ratio, with the same constants.

## A bounded-factor construction

Given any fixed allowed deficit choose an integer $D\ge1$ at least that deficit. Set $y_i=\min(T_{i+D},\log n)$ for $i=1,\ldots,J$, where $J=\min\{i\ge1:T_{i+D}\ge\log n\}$. For large $n$, $J=\log^* n-D-1$. Use $m_i=\lfloor n/2^i\rfloor$ trials in block $i$ at quantile $p_i=K 2^i y_i/n$. Take $K>2(r+3)$. For large $n$, $J=O(\log^* n)$ implies $K2^J\log n/n\to0$ and $m_i\ge n/2^{i+1}$. The total block lengths are at most $n-1$, leaving the forced draw; add any unused discretionary trials to the last block. Its failure then only decreases and the following bounds use its original length. All cutoffs are deterministic and require at most $J$ threshold values.

The probability that stage $i$ is reached, for $i\ge2$, is at most $\exp[-Ky_{i-1}/2]$. Potter bounds and $A(p)\le Q(p)$ give $A(p_i)/b_n\le C_1(K2^iy_i)^{r+1}$. The first stage therefore contributes a bounded normalized cost depending on $D,F$. For $i\ge2$, $y_{i-1}=T_{i-1+D}$ and $\log y_i\le y_{i-1}$. The normalized stage costs are bounded by a summable sequence in $i$:
$$
 C_1(K2^i)^{r+1}\exp[-(K/2-r-1)T_{i-1+D}].
$$
The probability of the forced fallback is at most $\exp[-K\log n/2]=n^{-K/2}$, making its cost $o(b_n)$. This proves the uniform bounded-factor upper bound. In particular a suffix of length $m$ can always be handled with at most $\log^*m+O_F(1)$ thresholds for cost $\le D_0 b_m$ at all large $m$, for some finite $D_0$.

## Approaching any strictly attainable constant

Fix $0<\eta<1$, reserve $m=\lfloor\eta n\rfloor$ last observations for the preceding suffix strategy, and write costs in units of $b_n$. Its cost has limsup at most $D_0\eta^{-r}$ by regular variation. Take a fixed upper bound $x_0>D_0\eta^{-r}$. Partition the first $n-m$ observations into $J'$ blocks of lengths $hn+O(1)$ where $h=(1-\eta)/J'$. Define recursively, backwards from the last of those blocks, $x_{i+1}=\Phi_h(x_i)$, where
$$
 \Phi_h(x)=x\frac{1+r e^{-h x^{1/r}}}{1+r}.
$$
Use the *cost threshold* $x_i b_n$ in that block. For each fixed $x_i>0$, $nF(x_ib_n)\to x_i^{1/r}$ by inversion of regular variation (or bracket $x_ib_n$ by $Q((x_i^{1/r}\pm\epsilon)/n)$). Its pass-conditioned cost divided by $b_n$ tends to $x_i/(1+r)$ by Karamata and continuity, so the block's normalized limsup is at most $\Phi_h(x_i)$ if its continuation limsup is at most $x_i$. Finite backwards induction bounds the policy's limsup by $x_{J'}$.

As $h\downarrow0$, $\Phi_h(x)=x-h r x^{1+1/r}/(1+r)+O(h^2)$ uniformly on $[0,x_0]$. The vector field is Lipschitz there; iteration of the one-step error $e_{i+1}\le(1+Lh)e_i+O(h^2)$ on $J'$ steps gives convergence to the ODE flow at time $1-\eta$. Solving explicitly,
$$
 \lim_{J'\to\infty}x_{J'}=
 [x_0^{-1/r}+(1-\eta)/(1+r)]^{-r}\le[(1+r)/(1-\eta)]^r .
$$
Choose $\eta$ small enough and then $J'$ finite large enough that $x_{J'}< C\Gamma(1+r)$. Since $M_n/b_n\to\Gamma(1+r)$, this concrete policy achieves the target for all sufficiently large $n$. Its total budget is at most $J'+\log^*m+O_F(1)\le\log^*n+O_{F,C}(1)$. The uniform lower bound above applies to every policy at that target, giving the asserted additive-order result.

For clarity the unrestricted leading constant used here is prior (Livanos–Mehta, EC 2025, Theorem 1.3 for negative minimum index), not a consequence asserted only on faith in their single-threshold theorem. It can also be recovered directly: $F\in RV_{1/r}$, so $D(x)=\int_0^xF(t)dt\sim r xF(x)/(1+r)$. At $g=G_n\to0$ a Bellman step is $g'=g-D(g)$ with $g'/g\to1$; regular variation of $D$ implies $\int_{g'}^gdt/D(t)\to1$. Thus $\int_{G_n}^c dt/D(t)\sim n$. By Karamata this integral is asymptotic to $(1+r)/F(G_n)$, so $G_n\sim Q((1+r)/n)\sim(1+r)^r b_n$. Dividing by $M_n$ gives $\Lambda_r$. For $k(n)-\log^* n\to+\infty$, the upper construction works for each fixed $C>\Lambda_r$, and unrestricted optimality bounds the liminf. This proves convergence to $\Lambda_r$.
