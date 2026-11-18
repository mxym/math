# Large transversals for large inclusion-maximal independent sets
This is a lower-bound construction, not a determination of the extremal order or a disproof of the conjectured sublinear upper bound. Natural logarithms throughout.

**Claim.** Fix $0<c<1$. For every sufficiently large integer $n$ there is a simple undirected graph $G$ of order $n$ such that every inclusion-maximal independent set has size at least $cn$, yet every set meeting all such independent sets has size at least $b_c\sqrt{n\log n}$ for some constant $b_c>0$. In particular $\max_{|V(G)|=n}i(G)\tau(G)/n=\Omega(\sqrt{n\log n})$, where $i$ denotes minimum size of a maximal independent set and $\tau$ its family's transversal number. This says nothing comparable for transversals of *maximum* independent sets.

### The graph and the large independent sets
Let $a=(1-c)/2$, $s=1-a=(1+c)/2$, and $\lambda=\min\{1,\tfrac12\log(s/c)\}>0$. Then $s e^{-\lambda}\ge\sqrt{sc}>c$. For $m\ge2$ set $\ell_m=\lceil m\log m\rceil$ and choose $m$ maximal with $m\ell_m\le an$. Write $\ell=\ell_m$ and $L=n-m\ell$. Thus $L\ge sn$, $m\to\infty$, and since the ratio of consecutive $m\ell_m$ tends to 1, $m^2\log m\sim an$. In particular $m\log m\sim\sqrt{a n\log n/2}$. Start with $m$ disjoint cliques $Q_1,\dots,Q_m$ of order $\ell$ and an independent reservoir $A$ of order $L$. Add each edge between $A$ and the cliques independently with probability $p=\lambda/m$. No edges are added between different cliques.

For any choice of at most one representative per clique with set $S$, the number $X_S$ of reservoir vertices with no neighbor in $S$ is binomial with mean $L(1-p)^{|S|}\ge sn(1-\lambda/m)^m\ge(c+\eta)n$ for all large $m$, for a constant $\eta>0$ depending only on $c$. Hoeffding gives $\Pr(X_S<cn)\le \exp[-2\eta^2 n^2/L]\le e^{-2\eta^2 n}$. There are $(\ell+1)^m=\exp(o(n))$ possible $S$. Hence with probability $1-o(1)$ every such $S$ has at least $cn$ reservoir nonneighbors. A maximal independent set with clique-part $S$ must include *every* one of these vertices because $A$ is independent. This is the reservoir argument from Cooper–Hollars, Lemma 3.1, specialized here.

### Robust uniform covering in any half of the cliques
Write $u=\log m$. Fix a small constant $d>0$ depending only on $\lambda$ such that $d<1$, $2\sqrt d<1/8$, $d<\lambda/8$, and

$$
\sup_{0<y\le d}\left[2\lambda y+2\sqrt y\log\frac{2}{\lambda\sqrt y}\right]<1/4.
$$

Such a $d$ exists because the expression tends to zero at zero. Write $t=\lfloor dmu\rfloor$ and $h=\lceil m/2\rceil$. A half-pool is the union of any $h$ of the cliques. We claim whp both the following hold simultaneously:

1. For every $x\in A$ and every half-pool $P$, more than $t$ vertices of $P$ are adjacent to $x$.
2. For every $R\subseteq A$ with $m/8\le r=|R|\le t$, put $k(r)=\lceil\sqrt{ru/m}\rceil$. In every half-pool $P$, more than $t$ vertices each have at least $k(r)$ neighbors in $R$.

For property 1, for fixed $x,P$ the number is $\operatorname{Bin}(h\ell,p)$ of mean at least $\lambda m u/2$. Since $t$ is less than half the mean, the lower Chernoff tail is at most $\exp(-\lambda m u/16)$. There are at most $n2^m$ choices of $x,P$, so the union of bad events has probability $o(1)$. This estimate and the one below concern all potential pools, not a pool sampled independently of the graph.

For property 2, fix $R$ and a candidate vertex in $P$. Its degree into $R$ has law $\operatorname{Bin}(r,p)$. Put $y=r/(mu)\le d$ and $k=k(r)$. Uniformly in the stated range, $u\sqrt y=\sqrt{ru/m}\ge\sqrt{u/8}\ge1$ eventually. Then $k\le 2u\sqrt y\le r$ for all large $m$, and $\lambda\sqrt y/2<1$. Using $\binom rk=\prod_{i=0}^{k-1}(r-i)/(k-i)\ge(r/k)^k$ and $\log(1-p)\ge-2p$ for $p\le1/2$, we get

$$
\begin{aligned}
\Pr(\operatorname{Bin}(r,p)\ge k)
&\ge (rp/k)^k(1-p)^r\\
&\ge (\lambda\sqrt y/2)^{2u\sqrt y}\exp(-2\lambda y u)\\
&\ge \exp(-u/4)=m^{-1/4}.
\end{aligned}
$$

The second bound holds even if $rp/k>1$: replace the base first by $\lambda\sqrt y/2$, then increase the exponent. The count of successful candidate vertices in $P$ is binomial (distinct vertices use disjoint cross edges), with mean at least $h\ell m^{-1/4}\ge m^{7/4}u/2$. For large $m$, $t$ is at most half of this, so the bad probability is at most $\exp(-m^{7/4}u/16)$. The number of $P,R$ pairs is at most $2^m(t+1)n^t=\exp(O(m(\log m)^2))$. This proves 2 without assuming independence across $R$ or across overlapping pools.

### A maximal set avoiding an arbitrary mixed test
Take a realization satisfying the hollow and both uniform covering properties; their intersection has probability approaching one. Fix any $T\subseteq V(G)$ with $|T|\le t$, and let $F=T\setminus A$, $R=T\cap A$. We select at most one vertex from each clique, never in $F$. For as long as $r=|R|\ge m/8$, take any pool formed from $h$ unselected cliques. Property 2 gives more candidates than $|F|$, so select one not in $F$ and remove all of its neighbors from $R$. The drop from $r$ to $r'$ obeys

$$
\sqrt r-\sqrt{r'}=(r-r')/(\sqrt r+\sqrt{r'})\ \ge\ k(r)/(2\sqrt r)\ \ge\ (1/2)\sqrt{u/m}.
$$

As the initial $r\le dmu$, at most $2\sqrt d\,m<m/8$ such choices can occur. This induction justifies that the required half-pool exists at every step: at any intermediate stage the same drop bound applies to the choices already made. When fewer than $m/8$ elements remain, take one at a time and use property 1 in an arbitrary unused half-pool to select a fresh representative adjacent to it outside $F$. At most a further $m/8$ cliques are used. There are still at least $h$ unused cliques whenever either type of choice is called for (for all large $m$).

Fill each remaining clique with one arbitrary representative outside $F$, possible since $|F|\le t<\ell$. Now $S$ consists of exactly one representative per clique, and all elements of $T\cap A$ are dominated by $S$. Define $J=S\cup\{x\in A:N(x)\cap S=\varnothing\}$. Then $J$ is independent and $J\cap T=\varnothing$. It is maximal in the **whole** graph: every omitted clique vertex is adjacent to its clique's representative, and every omitted reservoir vertex has a neighbor in $S$. This is an explicit extension, not a use of an arbitrary maximal completion in $G-T$. Thus $\tau(G)>t$. The estimates on $m,n$ give the claim.

For the constructed family the order is also $O_c(\sqrt{n\log n})$, but this is **not** a universal upper bound. Indeed every maximal independent set is uniquely determined by its partial representative set $S$, so there are at most $(\ell+1)^m$ such sets. Once $G$ is $c$-hollow, $k$ independent uniform draws from its vertices miss some maximal independent set with probability at most $(\ell+1)^m(1-c)^k$. Take $k>m\log(\ell+1)/[-\log(1-c)]$; the distinct sampled vertices give a transversal. This proves the family-specific upper bound and no more.

**Scope and attribution.** The preprint [Cooper–Hollars, arXiv:2607.15486v1](https://arxiv.org/abs/2607.15486v1), Theorem 1.7, uses a random independent reservoir joined to a *complete join* of $m$ cluster graphs $mK_m$, and a Janson estimate, giving $\Omega_c(n^{1/3}/\log n)$. We use one cluster graph, larger cliques, the same hollowing mechanism, and a uniform greedy covering argument. This strengthens that specific quantitative bound for their Question 7.1 but does not determine its answer, prove or disprove BET's $o(n)$ conjecture, or address their different maximum-set version. AI-assisted research with internal AI review; no claim of priority or external review.
