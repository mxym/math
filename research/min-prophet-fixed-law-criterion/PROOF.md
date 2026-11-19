# A distribution-only criterion for a bounded fixed-law i.i.d. minimum prophet ratio

**Model.** Let $X$ be a nonnegative random variable, with $0<\mathbb EX<\infty$. For each $n$ take $n$ i.i.d. draws from this *same known law*, exactly one of which must be taken online, without recall. Set $F(x)=\Pr(X\le x)$, $S=1-F$, $G_n$ equal to the minimum expected cost of a stopping rule, and $M_n=\mathbb E\min_{i\le n}X_i$. Both are finite and strictly positive. The question is whether $\sup_n G_n/M_n<\infty$, allowing the bound to depend on $F$. The all-zero law has an undefined $0/0$ ratio and is excluded.

## The criterion

1. If $e=\operatorname{ess\,inf}X>0$, the ratio tends to one.
2. Suppose $e=0$ and $\Pr(X=0)=0$. Choose any $c>0$ with $0<F(c)<1$. For $0<x\le c$ put
   $$
   D(x)=\int_0^x F(t)\,dt,\qquad
   L(s)=\frac{-\log(1-s)}s\ (0<s<1),\quad L(0)=1,\qquad
   T(x)=\int_x^c\frac{dt}{D(t)L(F(t))}.
   $$
   The map $T:(0,c]\to[0,\infty)$ is a continuous decreasing bijection and
   $$
   G_n\sim T^{-1}(n).
   $$
   In particular the following **nonrecursive condition involving the lower tail alone** is necessary and sufficient for bounded ratio:
   $$
   \liminf_{x\downarrow0}\frac1x\int_0^c S(t)^{T(x)}\,dt>0.                 \tag{1}
   $$
   In fact the reciprocal of this liminf is exactly $\limsup_n G_n/M_n$, with $1/0=+\infty$. No density, power expansion, fitted tail index or extremal limit is required. The cutoff $c$ is immaterial.
3. Suppose $0<\Pr(X=0)<1$. The ratio is bounded **if and only if** the conditional positive cost $Y=(X\mid X>0)$ has strictly positive essential infimum. If its essential infimum is zero then $G_n/M_n\to\infty$, not just along a subsequence.

This supplies an integral test, not an assertion that the test always holds, or a finite-number-of-moments characterization. The Bellman equation and the integral for the prophet are standard. On smooth maps the differential defining $T$ is exactly the Buff form used in iteration theory (see the attribution below); the argument here proves an error bound valid for arbitrary distribution functions, including jumps.

## The Bellman clock

The forced last draw and independence give $G_1=\mathbb EX$ and
$$
G_{n+1}=f(G_n),\qquad f(g)=\mathbb E\min(X,g)=g-D(g).
$$
The increasing continuous function $f$ satisfies $f(g)<g$ if $g>e$, and $f(e)=e$. Thus $G_n\downarrow e$ (including the degenerate constant case). Likewise $M_n\downarrow e$, by the almost sure convergence of coupled sample minima and domination by the first draw. This gives case 1.

In case 2, $F(x)>0$ for every $x>0$, $F(0)=0$, and a $c$ as above exists. In particular $D(t)>0$ for every $t>0$. The integrand of $T$ is positive and locally bounded on $(0,c]$; since $D(t)\le t$ and $L(F(t))\le L(F(c))<\infty$, its integral to zero diverges. These facts prove the claimed bijection.

Consider a single step from $g\le c$ to $g'=g-D(g)>0$. Set $a=F(g)$, $b=F(g')$; then $0\le b\le a<1$. For $g'\le t\le g$, monotonicity gives
$$
D(g)-a(g-t)\ \le D(t)\ \le D(g)-b(g-t).
$$
All denominators here are positive, since $g-g'=D(g)$ and $a<1$. Integrating their reciprocals on this exact interval gives
$$
L(b)\le\int_{g'}^g\frac{dt}{D(t)}\le L(a).
$$
Indeed the linear integral for slope $s$ equals $\int_0^1(1-su)^{-1}\,du=L(s)$, increasing with $s$. This identity includes $s=0$. Hence
$$
\frac{L(b)}{L(a)}\le T(g')-T(g)\le\frac{L(a)}{L(b)},\qquad
|T(g')-T(g)-1|\le L(a)-L(b),                                      \tag{2}
$$
using $L\ge1$. Left/right jumps of $F$ cause no issue: interval integrals are Lebesgue integrals and the endpoints above bound all interior values. Starting at the first $G_{n_0}\le c$, the errors in (2) are absolutely summable. Their total absolute size is at most $L(F(G_{n_0}))-1$ by telescoping. Consequently $T(G_n)-n$ has a finite limit; the size of the remaining tail of errors is at most $L(F(G_n))-1$.

We have $G_{n+1}/G_n=1-D(G_n)/G_n\to1$, since $D(g)/g\le F(g)\to0$. Choose an integer $K$ greater than $1+\sup_{n\ge n_0}|T(G_n)-n|$. Then $G_{n+K}\le T^{-1}(n)\le G_{n-K}$ for sufficiently large $n$, giving $G_n\sim T^{-1}(n)$. No expansion of $F$ near zero is used.

**Prior on the differential.** When differentiable, $f'(t)=1-F(t)$ at continuity points; the a.e. expression $(f'-1)dt/[(f-t)\log f']$ is $dT$. This is Xavier Buff's known differential, e.g. [Petersen and Zakeri, *Buff forms and invariant curves of near-parabolic maps*, §1, p. 2](https://arxiv.org/pdf/2412.17125). Their setting is holomorphic dynamics. There is no holomorphy requirement in (2), and no claim that $T$ is an exact conjugacy to translation.

## Removing the online recursion and upper tail

For real $s\ge1$ let $M(s)=\int_0^\infty S(t)^s\,dt$, so $M(n)=M_n$. By log convexity of these integrals (Cauchy–Schwarz) the ratios $M_{n+1}/M_n$ are nondecreasing and at most 1. Their limit equals $\lim_n M_n^{1/n}$ by telescoping logarithms. For every $u>0$, $M_n\ge u S(u)^n$, and $M_n\le\mathbb EX$, so this root tends to 1 since $S(u)\to1$ as $u\downarrow0$. Thus $M_{n+1}/M_n\to1$. This argument permits atoms at positive costs.

For $n\le s\le n+1$, both $T^{-1}(s)$ and $M(s)$ lie between their respective neighboring integer values; their ratios over one such step tend to one. It follows that $\limsup_nG_n/M_n=\limsup_{s\to\infty}T^{-1}(s)/M(s)$. Finally choose $0<u<c$ with $S(u)>S(c)$, possible since $F(0)=0<F(c)$. The integrable upper tail satisfies
$$
\int_c^\infty S(t)^s\,dt\le S(c)^{s-1}\mathbb EX=o(uS(u)^s),
\qquad \int_0^c S(t)^s\,dt\ge uS(u)^s.
$$
Replacing $M(s)$ by its integral on $[0,c]$ gives an asymptotically equivalent quantity. Take $s=T(x)\to\infty$ and invert the resulting ratio to obtain (1), including its exact limsup statement.

## When zero itself has positive mass

Let $q=\Pr(X>0)\in(0,1)$ and $U(x)=\Pr(Y>x)$ for $Y=(X\mid X>0)$. Then $M_n/q^n=\int_0^\infty U(x)^n\,dx$ is the expected conditional sample minimum.

If $\delta=\operatorname{ess\,inf}Y>0$, once $G_n\le\delta$ we have $G_{n+1}=qG_n$. Such an index exists because $G_n\downarrow0$. Thus $G_n/q^n$ eventually equals a fixed positive constant and $M_n/q^n\to\delta$, proving boundedness and convergence of the ratio.

If instead $\operatorname{ess\,inf}Y=0$, $U(x)<1$ for every $x>0$ and $U(0)=1$. Waiting for zero or otherwise taking the last draw gives $G_i\le q^{i-1}\mathbb EX=x_i$. Fix $i_0\ge1$ large enough that $U(x_{i_0})>0$ and put $P_j=\prod_{i=i_0}^jU(x_i)$, with $P_{i_0-1}=1$. Since $x_i\downarrow0$, $\log P_j=o(j)$. The Bellman equation gives $G_{i+1}\ge q G_i U(x_i)$ for $i\ge i_0$. Hence $G_n/q^n\ge (G_{i_0}/q^{i_0})P_{n-1}$.

For fixed $x>0$ the functions $U(x)^n/P_{n-1}$ tend to zero. To integrate this limit, for $x\ge x_{i_0}$ each denominator factor is at least $U(x)$, so this quotient is at most $U(x)^{i_0}\le U(x)$ (directly zero if $U(x)=0$). For $x_m\le x<x_{m-1}$, $m>i_0$, all factors with $i\ge m$ are at least $U(x)$, giving quotient at most $1/P_{m-1}$ when $n\ge m$. If $n<m$, the same upper bound holds because $P_{n-1}\ge P_{m-1}$. These bounds are integrable: $\int U=\mathbb EY<\infty$ and the cell lengths are $O(q^m)$ while $1/P_{m-1}=\exp(o(m))$. Dominated convergence gives $M_n/(q^nP_{n-1})\to0$. The online lower bound now proves divergence to infinity.
