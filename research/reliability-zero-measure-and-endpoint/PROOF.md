# Proofs

Let $G=(V,E)$ be a connected simple graph on $n\ge2$ vertices with $m$ edges. In the all-terminal model each edge **fails** independently with probability $q$. Write
$$
R_G(q)=\sum_{A\subseteq E:\,(V,A)\ {\rm connected}}(1-q)^{|A|}q^{m-|A|}.
$$
We use this polynomial also for complex $q$; the probability interpretation is needed only on $[0,1]$.

## A. Which graph sequences equidistribute?

**Theorem A.** Along a sequence of finite connected simple graphs, the probability measures assigning equal mass to each zero of $R_G$, counted with algebraic multiplicity, converge weakly on $\mathbb C$ to normalized arclength on the unit circle if and only if $2m/n\to\infty$.

**The tree expansion.** Put $r=n-1$ and fix a total order of the edges. For each spanning tree $T$ call an outside edge *forbidden* if it precedes the largest edge on its $T$-path. Write $a(T)$ for the number of forbidden edges. Increasing-order Kruskal on a connected set returns $T$ exactly when all edges of $T$ are present and all forbidden edges are absent. Indeed, every included but unchosen edge must have an earlier chosen path; conversely, induction in edge order shows that the stated conditions allow only edges of $T$ to be chosen. The other outside edges may be in either state. Summing over trees gives the classical activity expansion
$$
R_G(q)=(1-q)^r H_G(q),\qquad H_G(q)=\sum_T q^{a(T)}.
$$
The two sides agree on $[0,1]$, hence identically. In the **decreasing**-order Kruskal tree every excluded edge has a path of strictly larger edges. All of its $m-r$ outside edges are therefore forbidden for increasing Kruskal. Thus $H_G$ has degree $m-r$, with positive integer leading coefficient and $H_G(1)=\tau(G)>0$, where $\tau(G)$ counts the spanning trees. In particular $\deg R_G=m$, $R_G(0)=1$, and the root at 1 has multiplicity exactly $r$. This includes trees.

**Sufficiency.** The sum of absolute coefficient values of $R_G$ satisfies
$$
\|R_G\|_{\mathrm{coeff},1}\le 2^r\tau(G)\le 2^r\binom mr\le(2em/r)^r.
$$
The middle inequality counts all $r$-edge subsets. For a polynomial $P$ of degree $m$ with nonzero end coefficients $c_0,c_m$, define $L(P)=\log\|P\|_{\mathrm{coeff},1}-\frac12\log|c_0c_m|$. The deterministic theorem of [Hughes–Nikeghbali](https://arxiv.org/pdf/math/0406376) gives angular equidistribution and a fraction $1-o(1)$ of the zeros in every fixed annulus about the unit circle when $m\to\infty$ and $L(P)=o(m)$. Their per-polynomial bounds (Theorems 2–3) allow repeated or skipped degrees. Here $|c_0|=1,\ |c_m|\ge1$. If $d=m/r\to\infty$, then $m\to\infty$ and
$$
0\le L(R_G)/m\le \log(2ed)/d\longrightarrow0.
$$
For a bounded continuous test function, compare its value at a zero to the value at its radial projection on the circle. On a thin compact annulus uniform continuity gives an arbitrarily small error; off the annulus the error is bounded by twice the supremum times a vanishing fraction. Angular equidistribution now proves the weak limit.

**Necessity.** The closed singleton $\{1\}$ has mass $r/m$ for each graph and zero mass for arclength. Portmanteau gives $r/m\to0$. Because $n\ge2$, $m/(n-1)\to\infty$ is equivalent to $2m/n\to\infty$. This argument is why the trivial roots must be counted. $\square$

## B. A shrinking window for negative complete-graph roots

Write $R_n=R_{K_n}$, $M_j=j(j-1)/2$, and take $R_1=1$.

**Theorem B.** There is a real root in $(-1,0)$ for every $n\ge3$ with $n\equiv0,3\pmod4$. For any sequence $n\to\infty$ and any choices of roots $q_n\in(-1,0)$,
$$
1+q_n\sim\frac{2\log n}{n}.
$$

**Two expressions for the same coefficient.** For $q\ne0$ put
$$
F_{n,q}(z)=\sum_{j=0}^{n}q^{-M_j}\frac{z^j}{j!}.
$$
Give an operational edge weight $v=(1-q)/q$. All graphs on $j$ labelled vertices then have total weight $(1+v)^{M_j}=q^{-M_j}$. A graph is a set of its nonempty connected labelled components, so the exponential formula gives
$$
R_n(q)=q^{M_n}n![z^n]\log F_{n,q}(z).
$$
The identity only uses coefficients through degree $n$; it does **not** assert convergence of an infinite exponential series for $|q|<1$. Expanding the formal logarithm and ordering blocks gives the polynomial identity
$$
R_n(q)=\sum_{\pi}(-1)^{b-1}(b-1)!\,q^{c(\pi)},\qquad
c(\pi)=\tfrac12\Big(n^2-\sum_{S\in\pi}|S|^2\Big),
$$
where $\pi$ ranges over partitions of $[n]$ into $b$ blocks and $c(\pi)$ counts the cross-block edges.

**Interior exclusion.** For each partition other than the single block, choose a largest block, breaking ties deterministically, and write $\ell=n-|S_{\max}|\ge1$. Since every block has size at most $n-\ell$, we have $c(\pi)\ge n\ell/2$. The sum of $(b-1)!$ over partitions with this $\ell$ is at most $\binom n\ell\ell!2^{\ell-1}\le(2n)^\ell$. To see it, choose the exterior labels and count their ordered partitions. Every ordered partition is represented by listing its labels block by block and choosing divider positions; allowing all permutations and cuts is an upper bound. Thus if $|q|\le e^{-t}$,
$$
|R_n(q)-1|\le\sum_{\ell=1}^{n-1}(2ne^{-tn/2})^\ell.
$$
For fixed $\epsilon>0$ and $t\ge(2+\epsilon)\log n/n$ the ratio is at most $2n^{-\epsilon/2}$, so this entire disk is root-free for large $n$.

**Endpoint exclusion.** Now $q=-e^{-t}$, with $0\le t\le(2-\epsilon)\log n/n$ for fixed $0<\epsilon<2$. The polynomials $F_{n,q}(z)$ converge to $f(z)=\cos z+\sin z$, uniformly in $t$ on each fixed $z$-disk. In fact, for fixed $j$ the coefficient tends uniformly to $(-1)^{M_j}/j!$. For $3\le j\le n$ and $|z|\le R$, the inequalities $\log n/n\le\log j/j$ and $j!\ge(j/e)^j$ give the summable majorant
$$
e^{tM_j}\frac{R^j}{j!}\le(eR)^j j^{-\epsilon j/2}.
$$
Treat $j=0,1,2$ separately; beyond $n$ the coefficients are zero. Cauchy's formula on a larger disk also yields uniform derivative convergence.

The simple zero $-\pi/4$ is the only zero of $f$ in $|z|\le3/2$. Apply Rouché both on the boundary and on a small circle around $-\pi/4$ contained in $\{-1<\operatorname{Re}z<-1/2,\ |z|<1\}$. Uniformly for the allowed $t$ and all large $n$, $F=F_{n,q}$ has just one simple zero $\zeta$ in the larger disk, lying inside the smaller circle. Real coefficients and uniqueness give $\zeta\in(-1,0)$. On $|z|=3/2$, $F'/F$ is uniformly bounded and $|z-\zeta|\ge1/2$. Subtract its simple pole $1/(z-\zeta)$ to obtain a holomorphic remainder uniformly bounded on the boundary. Cauchy's estimate and the Taylor expansion of the pole at zero give
$$
n[z^n]\log F=[z^{n-1}]F'/F=-\zeta^{-n}+O((3/2)^{-(n-1)}).
$$
Only the germ of $\log F$ at zero is used. The real leading term has magnitude at least 1 and sign $(-1)^{n-1}$. Thus $R_n(-e^{-t})$ has sign $(-1)^{M_n+n-1}$ and no zero throughout the endpoint side for large $n$.

**Existence for each stated order.** At $q=-1$, $F_{n,-1}$ agrees with $f$ through degree $n$. The series $g(z)=f'(-z)/f(-z)=\tan(\pi/4+z)$ has strictly positive coefficients, by $g(0)=1$ and $g'=1+g^2$. Hence $[z^{n-1}]f'(z)/f(z)$ has sign $(-1)^{n-1}$, and $R_n(-1)$ has sign $(-1)^{M_n+n-1}$ for **every** $n\ge1$. This sign is negative precisely in the two indicated congruence classes. Since $R_n(0)=1$, the intermediate value theorem gives existence. This classical endpoint evaluation is not a novelty claim.

Finally, for a selected negative root write $t_n=-\log(-q_n)$. The two uniform exclusions put $nt_n/\log n$ between $2-\epsilon$ and $2+\epsilon$ eventually for every fixed $0<\epsilon<2$. As $1+q_n=1-e^{-t_n}\sim t_n$, the asserted first-order rate follows. $\square$
