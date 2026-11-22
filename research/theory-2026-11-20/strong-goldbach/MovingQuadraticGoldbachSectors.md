# Both moving quadratic signs among genuine Goldbach pairs at almost all four-divisible targets

**Theorem.** There is an absolute $c>0$ such that, apart from a set of relative density zero among $N\equiv0\pmod4$, **each** of the two signs occurs in at least $cN/(\log N)^4$ unordered prime representations
$$
N=r+s,\qquad (s/r)=\pm1 .
$$
The symbol is the Legendre symbol. Both primes are odd and coprime; they are opposite modulo 4, so interchanging them preserves the sign. The character on an endpoint is $\chi_N(r)=(N/r)$, which can have conductor of order $N$; this is not a statement about prime summands in a fixed progression. Perfect-square $N$ have no negative sector, so a qualification really is necessary. We do not assert an all-target estimate, a natural-scale $N/\log^2 N$ lower bound, or parity of the sector size.

For prime legs the fundamental discriminant is $-rs$. The negative sign gives $h(-rs)\equiv2\pmod4$ and the positive sign gives $4\mid h(-rs)$ by the two-prime case of [Chen–Garvan, Theorem 2.3](https://arxiv.org/pdf/2010.14315). In particular the incidence count of the marked primitive rows at these targets exceeds by a power margin the $O(N^{1/3})$ rows with a higher odd prime-power leg (even allowing either leg). This conclusion counts **genuine prime pairs**, not just nonzero Hurwitz weights; see [the class-weight distinction](HurwitzCubicRoughRows.md).

## A pair-preserving switch that reverses the sign

Fix a prime $a\equiv1\pmod {12}$ and restrict to $N\equiv0\pmod4$ with $(N/a)=-1$. Since $N$ is a positive quadratic discriminant, it is a fundamental discriminant times a square (including the trivial character case). Its positive quadratic character $\chi_N$ on units has conductor dividing $N$. Thus if $r'=ar-bN$ and both $r,N-r$ and $r',N-r'$ are genuine pairs, the signs are opposite:
$$
\chi_N(r')=\chi_N(a)\chi_N(r)=-\chi_N(r).
$$
A prime leg dividing $N$ would force the two legs equal, impossible here for $N>4$. Equivalently the sign identity follows from quadratic reciprocity applied to the squarefree part of $N$.

Put $X\le N<2X$. For each $1\le b\le a-2$, $b\equiv0\pmod3$, count genuine primes in the four forms
$$
L=(r,\ N-r,\ ar-bN,\ (b+1)N-ar)
$$
with $X/4<ar-bN<X/2$. For any fixed $N$ the real interval in $r$ has length $H=X/(4a)$ independent of $N$. All four values lie between positive multiples (depending on the fixed $a$) of $X$ and $2X$. As $b$ varies these intervals are disjoint.

We prove that for each fixed $a,b$, with relative-density-zero exceptions among the eligible $N$, the genuine four-prime count is $\gg H/(\log X)^4$ with an **absolute** lower constant.

## Conditional first and second moments

Let $F(N)=H^{-1}\sum_r\prod_{i=1}^4\vartheta(L_i)$ over the indicated interval, where $\vartheta(t)=\log t$ for a prime $t$ and is otherwise zero. For every prime $\ell$ define
$$
c_\ell(t)=(1-1/\ell)^{-4}\,\ell^{-1}
 \#\{u\bmod\ell:\ \ell\nmid \textstyle\prod_i L_i(t,u)\}.
$$
For $\ell=2$, at even $t$ only $u=0$ is forbidden and $c_2=8$. At 3, $a=1,b=0$ modulo 3 and the forbidden classes are $0,t$. At $\ell=a$, for eligible $t$ the last two forms never vanish ($1\le b\le a-2$ and $t$ is a unit), so the forbidden classes are again $0,t$. At every other $\ell\ge5$ there are at most four forbidden classes. Hence every product of the eligible local factors, taken over an initial interval of primes including $2,3,a$, is bounded below by an **absolute** positive constant: away from $2,3,a$ use
$$
 \prod_{\ell\ge5}(1-4/\ell)(1-1/\ell)^{-4}>0.
$$
The factor at $a\ge13$ is bounded below absolutely as well.

For $w\ge a$, fix one residue class $N\bmod W$, $W=4\prod_{3\le\ell\le w}\ell$, satisfying the target conditions, and put $C_W=\prod_{\ell\mid W}c_\ell(N)$. On this progression the [Green–Tao finite-complexity prime asymptotic](https://annals.math.princeton.edu/2010/171-3/p08), completed in all complexities by [Green–Tao–Ziegler](https://arxiv.org/abs/1009.3998), gives for $j=1,2$:
$$
 \mathbb E_{N} F(N)^j =
 C_W^j\prod_{\ell>w} B_{\ell,j}+o_{a,b,W}(1),
 \qquad B_{\ell,j}=\ell^{-1}\sum_{t\bmod\ell}c_\ell(t)^j .
$$
Here the average is over the fixed class in $[X,2X)$ and $X\to\infty$ first. Explicitly substitute $N=Wm+t_0$. The first system is the four forms $L(Wm+t_0,r)$; the second is these **and** the four forms $L(Wm+t_0,s)$ with $r,s$ independent. In one block the four rational forbidden slopes $0,1,b/a,(b+1)/a$ are distinct; across blocks the separate free coordinates give independence of the corresponding linear parts. The joint real region is a convex polytope, each fiber has volume $H^j$, and normalizing by the number of progression indices cancels the factor $1/W$ in the volume. At $\ell\mid W$ the input $N$ is fixed and the $j$ free local coordinates are independent; at $\ell\nmid W$ the $N$ residue is uniform, giving exactly the stated factors. Using $\vartheta$ instead of von Mangoldt does not affect these limits: a proper prime power on one fixed form allows $O(X^{1/2}\log X)$ possible values and $O_{a,b,W}(X^j)$ preimages per value before normalization, with only logarithmic weights. This also covers the diagonal of the second moment.

Take $w$ past the finitely many determinant primes of the fixed block. For $\ell>w$, at $t=0$ exactly one root is forbidden, at $t\ne0$ exactly four. Thus $B_{\ell,1}=1+O(\ell^{-2})$, and
$$
 B_{\ell,2}-B_{\ell,1}^2
 =\ell^{-1}(1-\ell^{-1})
 \big[3\ell^{-1}(1-1/\ell)^{-4}\big]^2=O(\ell^{-3}).
$$
Consequently the first limiting mean has an absolute positive lower bound for all sufficiently large $w$ and the relative variance has limsup $O(\sum_{\ell>w}\ell^{-3})$ (the Euler-product ratio is $1+O(\sum_{\ell>w}\ell^{-3})$). Chebyshev bounds the exceptional fraction for, say, half this absolute lower bound. For fixed $w$ there are finitely many eligible residue classes and each has the same bound on its limiting exceptional fraction. First $X\to\infty$, then $w\to\infty$, give the desired density-zero exceptions. Dividing out at most $\log^4(2X)$ per tuple proves the four-prime claim.

## Absolute constant and the menu of multipliers

For fixed $a$ we may discard the union of the finitely many exceptional sets for the allowed $b$. There are $\gg a$ such integers (uniformly for primes $a\ge13$). The disjoint input intervals together yield $\gg X/\log^4 X$ different switches. Each produces one unordered pair of each sign. For a given output pair at the same $N$, at most two inputs realize it as the first pair by choosing $r$; at most two realize it as the second pair by choosing $r'$ and recovering the unique $0<r<N$ with $ar\equiv r'\pmod N$, then $b$. This proves the absolute sign-sector lower bound for density one in every fixed eligible slice.

Finally take $k$ distinct fixed primes $a_i\equiv1\pmod {12}$, which exist by Dirichlet's theorem. Among multiples of 4 the limiting fraction not eligible for **any** multiplier is
$$
 \prod_{i=1}^k \frac{a_i+1}{2a_i}
$$
by the Chinese remainder theorem (a nonunit also counts as not eligible). The finitely many eligible slices have a density-zero union of failures. The common lower constant does not deteriorate with $k$. Letting $k\to\infty$ proves the theorem; dyadic interval statements imply natural density by summing intervals, with an initial small segment discarded. No effective growing-modulus assertion is involved.

**Comparison.** [Dominguez–Miller–Wong](https://arxiv.org/abs/1211.2605) and [Blum et al.](https://arxiv.org/abs/1302.3453) use restricted binary representations at polynomial targets for class groups. The changing character here is attached to the actual target $N$, and the two pairs at that target are linked by a genuine sign-changing multiplicative unit. Ordinary almost-all Goldbach or prime summands in a fixed congruence class does not directly give this switch.

Direct prior question: [“Quadratic patterns in summands of Goldbach's conjecture” (MathOverflow, July 2022)](https://mathoverflow.net/questions/426188/quadratic-patterns-in-summands-of-goldbachs-conjecture) asks about the signed sum over Goldbach pairs and discusses the reciprocity reduction to the moving target character. Our lower bounds give both signs on a density-one set; they do not prove the suggested sign equidistribution.
