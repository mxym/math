# Both quadratic sectors at the natural binary scale for almost all targets

**Theorem.** For relative density one of $N\equiv0\pmod4$, at least $cN/\log^2N$ unordered pairs of genuine primes $r+s=N$ have $(s/r)=+1$, and at least $cN/\log^2N$ have $(s/r)=-1$, for an absolute $c>0$. Thus the moving two-prime fundamental class-number mark has both sectors at ordinary binary scale. This is not cancellation with a specified leading constant, not a proof of sign equidistribution as asked in [this 2022 question](https://mathoverflow.net/questions/426188/quadratic-patterns-in-summands-of-goldbachs-conjecture), and not an all-target theorem. See [the fixed multiplier proof](MovingQuadraticGoldbachSectors.md) for the underlying switch, earlier work and class-number interpretation.

## 1. Switches and normalization

Fix a prime $g\equiv1\pmod {12}$. Work first on eligible targets $(N/g)=-1$, $4\mid N$, $X\le N<2X$. Write $L_0=\log X$, $T=L_0^8$, and take all primes $t\in[T,2T]$ exceeding $g$, their count $J\asymp T/\log T$. Put $A=gt^2$. For each $t$ use
$$
 1\le b\le A-2,\quad b=0\bmod3,\quad (b(b+1),A)=1.
$$
There are $\gg A$ such offsets, with an absolute constant: on the multiples of 3 the two forbidden residues each modulo the distinct primes $g,t$ remove at most $2/g+2/t+O(1/A)$ of the interval in relative terms. For each chart $(t,b)$ count genuine primes in
$$
 r,\quad N-r,\quad y=Ar-bN,\quad N-y,\qquad 1/4<y/N<1/2 .
$$
The $r/N$ interval is $I_{A,b}=((b+1/4)/A,(b+1/2)/A)$. All prime values in these charts and the simultaneous charts below are $\gg X/\log^{O(1)}X$. On any genuine edge $t\nmid N$ (otherwise $y>t$ is divisible by $t$). Since $\chi_N=(N/\cdot)$ on units has conductor dividing $N$, $\chi_N(A)=-1$ and the pairs at $r$ and $y$ have opposite signs. Treat these as oriented edges $r\to y$; multiplicities across $t$ are retained. For each $t$ there is at most one outgoing edge per input and at most one incoming edge per output since $(A,N)=1$ on existing edges.

Write $E$ for the edge count, $D_+,D_-$ for the sums of squares of all outdegrees and indegrees, **not** for quadratic signs. For either desired sign, count the incidences of that sign with all the edges; each edge has exactly one. At most four oriented endpoint integers correspond to an unordered pair counted by its two roles and two choices of endpoint. Cauchy–Schwarz gives at least $E^2/[4(D_++D_-)]$ distinct unordered pairs of either sign.

We establish for density one in the eligible slice, with a common local normalization specified below, the bounds
$$
 E\gg \mathcal S^3 J X/L_0^4,\qquad
 D_++D_-\ll \mathcal S^5 J^2 X/L_0^6 .
$$
It suffices to prove these with an exceptional limsup tending to zero as an auxiliary fixed cutoff $w$ grows. The implied constants do not depend on $g,w$ or the target residues, and $\mathcal S\ge1$. The diagonal $t=u$ in each squared degree contributes at most $J(2X)$, negligible on the indicated upper scale since $J/L_0^6\to\infty$.

## 2. A uniform conditional moment fact

Take $w\ge\max(g,13)$ fixed, $W=4\prod_{3\le\ell\le w,\,\ell\ {\rm prime}}\ell$, and fix an eligible target residue $N\bmod W$. Put
$$
 \mathcal S=\prod_{\ell\mid(W,N)}(1-1/\ell)^{-1}.
$$
The row charts here take $k=4$ or 6 integral homogeneous forms in $(N,z)$ with distinct rational directions and nonzero coefficients on $z$. Each has an exact real fiber in $z$ of length $\lambda N$, with $\lambda\gg_g L_0^{-C}$ an explicit rational interval length; all coefficients and denominators in this section are polylogarithmic with absolute exponents, with $g,W$ fixed. Normalize the sum of products of $k$ prime logarithms on each fiber by its length. For convenience divide the dyadic target interval into comparable slabs of relative length $\asymp1/L_0$ and normalize in a slab starting at $X_0$ by $\lambda X_0$; this changes the normalization by $1+O(1/L_0)$ uniformly.

Let $c_\ell(n)$ be $(1-1/\ell)^{-k}$ times the allowed fraction of $z\bmod\ell$ on the fiber at $n$. Define
$$
 \mu=\prod_{\ell\mid W}c_\ell(N)\prod_{\ell>w}\mathbb E_n c_\ell(n),
$$
where the latter means the uniform local average. The conditional first and second moments of the normalized row sum are respectively
$$
(1+o_{g,W}(1))\mu,\qquad
(1+o_{g,W}(1))\prod_{\ell\mid W}c_\ell(N)^2
                            \prod_{\ell>w}\mathbb E_n c_\ell(n)^2 .
$$
This is [Bienvenu, *A higher-dimensional Siegel–Walfisz theorem*, Theorem 1.3](https://www.impan.pl/shop/en/publication/transaction/download/product/92171): substitute $N=Wm+n_0$ and in the second system use independent $z,z'$ at the same $N$. Across blocks nonzero $z$ coefficients give distinct directions. Volumes in dimensions 2 and 3, after the fixed progression substitution, are comparable to $X^d/\log^{O(1)}X$ or larger; relative slab variation gives $1+O(1/L_0)$ in each first or second volume. The theorem's relative error is uniform over these systems and slabs; the scale parameter can be a fixed multiple of $X$ as all variables (including the CRT coordinate below) lie in that box. Removing proper prime powers costs $O(X^{d-1/2}\log^{O(1)}X)$ before normalization. For any nonzero singular series its size here is at least $\log^{-O(1)}X$: small fixed-prime factors on a positive residue class are bounded below in terms of $W$, and for $\ell>\max(w,2k)$ each joint factor is at least $1-O_k(\ell^{-2})$ by the union bound on $k$ lines in two variables (provided no identically zero form), likewise for the replicas. A zero local factor blocks all physical prime points because a corresponding prime divisor is fixed or divides a polylogarithmic coefficient minor and the physical prime values are larger. Such charts can be omitted. The same applies to nonprimitive or proportional forms at any point of our construction if they cannot occur at a genuine collision.

Away from primes dividing $gtu$ (omit $u$ for the four-form case), every fiber coefficient on $z$ is a unit modulo $\ell$ (as verified below). Homogeneity shows that $c_\ell(0)$ excludes one $z$, and $c_\ell(n)$ for $n\ne0$ excludes a constant number at most $k$. Even at a determinant prime the difference is $O_k(1/\ell)$. Hence for $\ell>w$
$$
 \frac{\mathbb E c_\ell^2}{(\mathbb E c_\ell)^2}
 =1+O_k(\ell^{-3}).
$$
At $t,u>w$ the exceptional coefficients may make a homogeneous form vanish for all $z$ when $n=0$; at nonzero $n$ the permitted fraction is still $1-O_k(1/\ell)$ unless a whole form was zero modulo $\ell$, already excluded. The ratio there is $1+O_k(1/\ell)$ and there are at most two such primes. Thus each nonzero chart count after normalization differs from $\mu$ in conditional mean absolute error at most
$$
 \mu\,[O((\textstyle\sum_{\ell>w}\ell^{-3}+1/T)^{1/2})+o_{g,W}(1)].
$$
This holds uniformly. For any finite positive weighted sum of charts it holds with the sum of their means in place of $\mu$, by the triangle inequality, **without** assuming independence of the charts. Consequently each of the three aggregates (first, outgoing collisions, incoming collisions) is within, say, half its own log-weighted mean except on a fraction tending to zero in the ordered limits $X\to\infty$, $w\to\infty$. We now bound those means, restoring the real fiber lengths.

## 3. First mean and a collision majorant

For the four forms in a switch the first mean per unit length is at least $c_1\mathcal S^3$. For $\ell\mid(W,N)$ the four forms coalesce at one excluded root, giving $(1-1/\ell)^{-3}$; $\ell\mid A$ in that range cannot divide $N$ (only $g$ is that small, and eligibility excludes it). At $\ell=3$ the only forbidden roots are $0,N$ since $A\equiv1,b\equiv0\bmod3$. At $\ell=g$ (or $t$ for a unit $N$) the last two forms never vanish. At all remaining unit target residues with $\ell\ge5$, use $(1-4/\ell)(1-1/\ell)^{-4}$. Its product converges positively. The single large prime $t$ costs only a bounded factor, and the tail local averages over $\ell>w$ are bounded below by a positive absolute product, by the union bound just used. Summing the lengths $\lambda N=N/(4A)$ over $\gg A$ offsets and $J$ prime multipliers gives $\gg\mathcal S^3 JX$. Dividing by $\log^4(2X)$ gives the desired lower bound for $E$.

For six nondegenerate forms let $\Delta$ comprise all the nonzero projective determinants after discarding factors supported on $gtu$, i.e. it need only cover primes outside $gtu$ where rational directions can merge. Then uniformly
$$
 \mu\ll \mathcal S^5\,F(\Delta),\qquad F(h)=\prod_{\ell\mid |h|}(1+C/\ell)
 \quad(h\ne0)
$$
for an absolute $C$. At a small prime dividing $N$ away from $gtu$ the factor is $(1-1/\ell)^{-5}$; at the eligible $g$ and large $t,u$ bounded factors suffice. At a unit residue away from $\Delta gtu$ distinct slopes give $(1-6/\ell)(1-1/\ell)^{-6}$; for large-prime local averages this includes the $n=0$ residue of density $1/\ell$ and gives $1+O(\ell^{-2})$. At determinant primes all corrections are at most $1+O(1/\ell)$ for large $\ell$, and the finite small primes cost an absolute constant. Here and below enlarging $\Delta$ by repeat factors or powers is harmless. We use repeatedly the elementary uniform bound $\sum_{1\le h\le Z}F(h)^m\ll_m Z$ for each fixed $m$: expand the product over squarefree divisors with weights bounded by $C_m^{\omega(d)}/d$, and sum using $\lfloor Z/d\rfloor\le Z/d$. Hölder bounds products of any fixed number of such factors by their corresponding fixed moments.

## 4. Outgoing collisions

Fix distinct primes $t,u\in[T,2T]$, and put $A=gt^2$, $B=gu^2$. The two switched outputs at one input are $Ar-bN$ and $Br-dN$. The interval in $r/N$ is $I_{A,b}\cap I_{B,d}$ and has width at most $1/(4A)$; if positive its width is at least $1/(16AB)$ by rational endpoints. The six forms at this collision correspond to the rational slopes
$$
 0,\ 1,\ b/A,\ (b+1)/A,\ d/B,\ (d+1)/B .
$$
These are distinct: both fractions on each side are reduced by the offset restrictions and have different full denominators across sides. All free-variable coefficients are units away from $gtu$.

There are $O(A)$ overlapping offset charts: for each $b$ there are $O(1)$ choices of $d$ since $B/A$ is bounded, and likewise in reverse. Determinant primes outside $gtu$ divide the product of
$$
 b,b+1,A-b,A-b-1,\quad d,d+1,B-d,B-d-1,
 \quad t^2(d+j)-u^2(b+i)\quad(i,j=0,1).
$$
Each one-variable factor has mean bounded for all fixed $F$-moments when summed over the overlapping charts and divided by $A$. For the cross terms put $h=t^2d-u^2b$. Overlap implies $|h|\ll T^2$ (write $b=A\theta+O(1)$, $d=B\theta+O(1)$ for the same $\theta$). Since $(t,u)=1$, for a fixed $h$ the possible $b$ form one class modulo $t^2$, hence there are at most $g+1$ charts. Every shifted cross term is nonzero and has size $O(T^2)$; the fixed-moment bound for each follows on dividing $O(g T^2)$ by $A$. Applying Hölder proves $\sum_{b,d}F(\Delta)\ll A$ over the overlapping charts with an absolute constant. After restoring their width, their total mean is $\ll\mathcal S^5 X$ per ordered $(t,u)$.

## 5. Incoming collisions

For a common output $y$, the inputs are $(y+bN)/A$ and $(y+dN)/B$. Since $(N,g)=1$, feasibility requires $b\equiv d\bmod g$. Let $M={\rm lcm}(A,B)=gt^2u^2$, and take $0\le e<M$ with $e\equiv b\bmod A$, $e\equiv d\bmod B$. Write $y=Mz-eN$. The exact interval in $z$ has length $N/(4M)$, and the six forms are now integral, with free-variable coefficients among $\pm M,\pm M/A,\pm M/B$. There is no Jacobian or density factor to add beyond the interval width $1/(4M)$. When expressed before the invertible rational coordinate change, their slopes in $y/N$ are
$$
 0,\quad1,\quad -b,\quad A-b,\quad-d,\quad B-d .
$$
Omit duplicates: a duplicate of two inverse-input directions or their two complements requires $b=d$ or $A-b=B-d$. Then two positive prime legs are in ratio $A/B=t^2/u^2$, impossible. The negative and positive internal slopes cannot coincide with one another or with 0,1 since $1\le b\le A-2$, $1\le d\le B-2$. Similarly any form identically divisible by a prime after the CRT substitution cannot give an actual collision; that divisor is at most polylogarithmic since the coefficients are. We need only upper bounds after omitting these cases.

Outside $gtu$ the coefficient transformation is invertible and all exceptional primes divide differences of the six integer slopes. The one-variable factors are among $b,b+1,A-b,A-b-1,d,d+1,B-d,B-d-1$. Each $b$ occurs with $O(B/g)$ choices of $d$ and conversely, so the sums of fixed $F$-moments are $O(AB/g)=O(M)$. Each genuine two-offset difference, up to sign, is $d-b+c$ for a fixed $c\in\{0,A,-B,A-B\}$, divisible by $g$. It is nonzero and $|d-b+c|\ll A+B$. Divide out its factor $g$ (the $F(g)$ penalty is bounded); each integer $(d-b+c)/g$ occurs $O(A)$ times, and has absolute value $O(T^2)$. Thus each cross-factor fixed moment also sums to $O(A T^2)=O(M)$, with absolute constants. Hölder gives $\sum_{b,d}F(\Delta)\ll M$ for these charts. Multiplying by the real width gives $\ll\mathcal S^5 X$ per ordered $(t,u)$ again.

Summing the log-weighted upper bounds in §§4–5 gives $\ll\mathcal S^5 J^2X$ on the conditional mean for each off-diagonal squared degree. All actual legs exceed $X/\log^{O(1)}X$, so unweighting costs a divisor $\gg L_0^6$. The concentration from §2 now proves the claimed density-one bounds of §1 on each eligible slice. Cauchy–Schwarz gives $\gg\mathcal S X/L_0^2\gg X/L_0^2$ pairs of each sign. Finally take a fixed finite menu of primes $g\equiv1\pmod{12}$ and then enlarge the menu: the residual target fraction is $\prod_g(g+1)/(2g)\to0$ by CRT. The constants in the lower bound are independent of the menu and all conditionings are taken before its enlargement. This proves the theorem.
