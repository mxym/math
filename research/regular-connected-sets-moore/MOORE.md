# A larger regular graph beating a girth-six Moore graph

This is a separate consequence of the constructive estimate in the rate proof. In the notation of Cambie, Goedgebeur and Jooken (EJC 2025), $c(G)=N(G)^{1/|G|}$, and $c_d(n)$ is its maximum on simple $d$-regular graphs of order $n$. Their Conjecture 2 says that if $M$ is a degree-$d$ graph attaining the Moore bound at its girth and order $n$, then every $n'>n$ satisfies $c_d(n')<c_d(n)=c(M)$. It is not a conjecture about connected dominating sets or a comparison restricted to competitors of the same girth.

**Result.** For all sufficiently large prime powers $Q$, the incidence graph $M$ of the projective plane over the field of $Q$ elements has strictly smaller connected-set base than the connected-dominating-set base of arbitrarily large graphs of the same degree. This refutes Conjecture 2. We do not assert which graph maximizes at the Moore graph's own order, nor a refutation for cubic graphs.

## 1. A bound for the Moore comparator

Let $J$ be any $d$-regular simple graph of order $n$ with no 4-cycle. Select each vertex independently with probability $1/2$. Write $E_v$ for the event that $v$ is selected but all its neighbors are unselected; $p=2^{-(d+1)}$ is its probability. When $u,v$ are adjacent their two events cannot both occur. When they are nonadjacent they have at most one common neighbor (otherwise there is a 4-cycle). Hence their joint event fixes at least $2d+1$ distinct independent bits, so its probability is at most $2p^2$. The first two inclusion-exclusion terms give
$$
\Pr(\text{some } E_v)\ge np-n(n-1)p^2 .
$$
A nonempty connected selection with an isolated selected vertex must be a singleton; a singleton has total probability $n2^{-n}$. Consequently
$$
1-N(J)/2^n\ \ge\ np\,[1-(n-1)p-2^{d+1-n}].
$$
If $a=1-(n-1)p-2^{d+1-n}>0$, concavity at 1 gives
$$
2-c(J)\ge 2[1-(1-npa)^{1/n}]\ge 2pa=2^{-d}a .
$$
In this use $0\le npa\le1$ follows from the preceding probability bound.

For a prime power $Q$, let the points and lines of $\mathrm{PG}(2,Q)$ be the 1- and 2-dimensional subspaces of a 3-dimensional space over the finite field, with incidence given by inclusion. Its incidence graph $M$ has degree $d=Q+1$ and order $n=2(Q^2+Q+1)=2(d^2-d+1)$. Indeed each nonzero vector represents one point up to a nonzero scalar, and dually the same count holds for lines; each line has $Q+1$ points and each point is on as many lines. The graph is bipartite. Distinct points have a unique common line, excluding 4-cycles, and three noncollinear points and their pairwise lines give a 6-cycle. In any $d$-regular graph of girth at least six, branching to distance two on both sides of a fixed edge without using the edge again gives $2[1+(d-1)+(d-1)^2]$ distinct vertices: any premature meeting would give a cycle of length at most five. Thus $M$ attains the girth-six Moore bound.

Here $(n-1)p+2^{d+1-n}=o(1)$ as $Q\to\infty$. The finite-graph construction in the rate proof gives a graph $G$ of the same degree at every order $4mt$ for sufficiently large even $m$, $t=\lfloor d/4\rfloor$. For every such $G$ and all large $d$,
$$
2-N_{\rm dom}(G)^{1/|G|}\le 1820\,2^{-4t}/t
= O(2^{-d}/d)
< 2^{-d}[1-(n-1)p-2^{d+1-n}]\le 2-c(M).
$$
Choose any such $m$ making $4mt>n$. Then $c_d(4mt)\ge c(G)\ge N_{\rm dom}(G)^{1/|G|}>c(M)$, the claimed contradiction. Only the connected-set comparison is needed for the numbered conjecture.

## 2. An explicit finite pair

Take the prime $Q=8191$ (trial division up through $\lfloor\sqrt{8191}\rfloor=90$ suffices), $d=8192$, $t=2048$, and $m=2d=16384$. No residue matchings are needed. The comparison graph is the independent $2048$-fold blow-up of $C_4\square C_{16384}$; it is bipartite. It has $4mt=2d^2=134217728$ vertices, strictly more than the $2(d^2-d+1)=134201346$ vertices of $M$. Since $1820\,2^{-8192}<1/2$, the finite lower construction bounds its gap, even for connected domination, by
$$
(1820/2048)2^{-d}=(455/512)2^{-d}.
$$
In the comparator, $(n-1)p<2^{27}2^{-8193}<1/32$ and $2^{8193-n}<1/32$. Hence $2-c(M)>(15/16)2^{-d}=(480/512)2^{-d}$. The rational gap coefficients give a strict comparison without numerical extraction of large roots or enumeration of subsets. This one pair is not claimed to be smallest.
