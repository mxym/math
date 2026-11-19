# Which double caterpillars give an upper profile boundary?

For a rooted binary tree, sample a uniform subset of its leaves of a fixed size. Take the spanning rooted subtree, rooted at their lowest common ancestor and with all unary vertices suppressed. Write $C_j$ for the limiting probability of obtaining the $j$-leaf caterpillar $\mathrm{Cat}_j$ (one leaf splits off at each nonterminal branch), and $E$ for that of obtaining the six-leaf even tree $E_6$, whose two root branches have three leaves apiece. There is only one three-leaf rooted binary tree shape. Limits here are coupled densities along a single sequence of trees with strictly increasing numbers of leaves. This is the tree-profile of Brosch and Puges, *Getting to the root of the problem: sums of squares for limits of trees*, §2.3. The upper boundary at $C_k=x$ means the largest achievable $E$ at that very same $x$.

Their Conjecture 1 proposes that joining two caterpillars of asymptotic leaf masses $p,1-p$ at a root gives an upper-boundary point for every $k\ge4$ and every $p\in[0,1]$. Their equations (12) and (13) already give its two coordinates:
$$
F_k(p)=p^k+q^k+k(pq^{k-1}+qp^{k-1}),\qquad H(p)=20p^3q^3,\quad q=1-p.
$$
They rigorously certified, in particular, the midpoint $p=1/2$ for $k\in\{4,5,6\}$. These coordinates and midpoint results are not new.

**Theorem.** For $k=4,5,6$, the entire double-caterpillar arc is the upper boundary for $x$ in $[(k+1)/2^{k-1},1]$. For each fixed $k\ge7$ and for every sufficiently small $p>0$ (depending on $k$), there is a three-caterpillar construction whose limiting $C_k$ equals $F_k(p)$ and whose limiting $E$ strictly exceeds $H(p)$. Thus the assertion for every $p$ holds exactly at $k=4,5,6$. We do not determine the upper boundary to the left of these arcs, either lower boundary, the optimizing construction past the first failure, or all parameters at which failure occurs for $k\ge7$.

## Finite constructions and the passage to limits

Use a finite rooted binary skeleton with a positive probability weight on each terminal, summing to one. To sample $j$ leaves, choose $j$ terminal labels independently with those weights. A terminal receiving $h$ labels represents an $h$-leaf caterpillar ($h=0$ means empty). Retain the occupied branches, suppress unary vertices, and join the caterpillars at occupied terminals. These probabilities are realized by actual sequences: replace each terminal by a caterpillar with its prescribed limiting proportion of the $n$ leaves, rounding to integers with total $n$. The terminal counts of a uniform $j$-subset converge by the multivariate hypergeometric formula to the multinomial law just specified. The behavior at each terminal is exact, since every subset of leaves of a finite caterpillar induces a caterpillar. This supplies a simultaneous limiting model for *all* fixed patterns, not just the two marginals. A zero-weight terminal, when needed at an arc endpoint, can be omitted.

Conversely, use any given ordinary $n$-leaf tree as a skeleton, giving its terminals weight $1/n$. For a fixed $j$, the probability of a repeated label is at most $\binom{j}{2}/n$. Conditional on no repetitions the induced shape agrees with genuine finite-tree sampling. Thus every universal continuous inequality in the finitely many densities proved on weighted skeletons passes to every profile point. In the following arguments a child density is always normalized by its own total weight. Both child weights are positive at a nonterminal split.

## Three sharp inequalities

Put $D_j=1-C_j$, $S=E/20$. Then on all weighted skeletons and hence all limiting profiles,
$$
 D_4\ge 6S^{2/3},\qquad D_5\ge10S^{2/3},\qquad
 D_6\ge15 S^{2/3}-10 S.
 \tag{1}
$$
We prove the three together by induction on the number of nonterminal branches. On a terminal, $S=D_j=0$. At a nonterminal with child weights $p,q=1-p$, use subscripts 1 and 2 for the normalized children. Set
$$
 r=pq,\quad u=p^2 S_1^{1/3},\quad v=q^2 S_2^{1/3}.
$$
All six leaves may fall in one child; when both are represented, the only split inducing $E_6$ is $3+3$. Hence exactly $S=r^3+u^3+v^3$.

For the caterpillar split, all allocations with both child sample sizes at least two fail immediately. If one side gets exactly one, the other must induce a caterpillar. If all leaves fall on one side, recurse there without any new constraint. For $j\ge4$ this gives
$$
D_j=g_j(p)+p^jD_{j,1}+q^jD_{j,2}
 +j\big(p^{j-1}qD_{j-1,1}+q^{j-1}pD_{j-1,2}\big),
$$
where $g_j(p)=1-F_j(p)$ and $D_3=0$. Direct binomial expansion yields
$$
g_4=6r^2,\qquad g_5=10r^2,\qquad g_6=15r^2-10r^3.
$$
In particular the $j=6$ mixed counts are $15(p^2q^4+p^4q^2)+20p^3q^3$. Since $(r^3+u^3+v^3)^{2/3}\le r^2+u^2+v^2$, the $j=4$ recursion and the inductive $D_4$ bounds prove the first inequality. For $j=5$, applying both the $D_5$ and $D_4$ bounds on each child gives
$$
D_5/10\ge r^2+(p+3q)u^2+(q+3p)v^2\ge S^{2/3}.
$$

For $j=6$ write $B=(D_6+10S)/15$. The root toll for $B$ is $r^2$, and its two all-in-one terms are $p^6 B_1+q^6B_2$. The remaining terms are $(6/15)(p^5qD_{5,1}+q^5pD_{5,2})$. Using $B_i\ge S_i^{2/3}$ and the child $D_5$ bounds gives
$$
B\ge r^2+(p^2+4pq)u^2+(q^2+4pq)v^2.
$$
If both $p,q\ge1/3$, both coefficients are at least one since $p^2+4pq-1=q(3p-1)$. It remains, by symmetry, to consider $0<p<1/3$. Here the $v^2$ coefficient is at least one. The small coefficient on $u^2$ suffices too: $S_1^{1/3}\le1$ since $E_1\le1$, so $u/r\le p/q$. Because $q>2/3$, $4pq\ge 2p/(3q)\ge 2u/(3r)$. Concavity at $r^3>0$ now gives
$$
(r^3+u^3)^{2/3}\le r^2+\frac{2u^3}{3r}
\le r^2+(p^2+4pq)u^2.
$$
Adding $v^2$ and using subadditivity of the power $2/3$ finishes $B\ge S^{2/3}$ and the induction.

For a double caterpillar the children are terminals, so $S=r^3$ and $D_j=g_j$. All three inequalities in (1) hold with equality. For $j=4,5$ their right sides are strictly increasing in $S$. For $j=6$ the function $15t^2-10t^3$ is strictly increasing for $0\le t\le1$, which includes $t=S^{1/3}$. Thus no other limit with the same $C_j$ has larger $E$. As $p$ runs from $0$ to $1/2$, $r$ increases from 0 to $1/4$ and each $g_j$ strictly increases. The arc covers exactly the horizontal interval stated in the theorem.

## Why the claim changes at seven leaves

Fix $k\ge7$. Use a root with one small child of mass $a$ and a terminal of mass $1-a$. Split the small child equally into two terminals. Write $D_j^*=1-F_j(1/2)$. The limiting coordinates of this three-terminal construction are exactly
$$
\widetilde F_k(a)=F_k(a)-a^kD_k^*-k(1-a)a^{k-1}D_{k-1}^*,
\qquad
\widetilde H(a)=H(a)+\frac5{16}a^6.
\tag{2}
$$
These identities follow from the same split sampling: modifying the small child only changes the caterpillar event for $k$ or $k-1$ samples falling there, while its extra $E_6$ contribution comes from all six samples falling there. In particular $0<D_{k-1}^*,D_k^*<1$ and $\widetilde F_k(p)<F_k(p)$ for $0<p<1$.

To compare at *exactly* the same limit density, let $s=p-p^{k-2}$. For fixed $k$, as $p\downarrow0$, $F_k(p)=1-\binom{k}{2}p^2+O_k(p^3)$ and $F_k'(p)=-k(k-1)p+O_k(p^2)$ by the binomial formula. By the mean value theorem, $F_k(s)-F_k(p)=(k(k-1)+o(1))p^{k-1}$. Also $s^kD_k^*+k(1-s)s^{k-1}D_{k-1}^*=(kD_{k-1}^*+o(1))p^{k-1}$. Their difference is positive for all sufficiently small $p>0$. Thus $\widetilde F_k(s)>F_k(p)>\widetilde F_k(p)$. Continuity gives an $a\in(s,p)$ with $\widetilde F_k(a)=F_k(p)$.

On this interval $H'(x)=O(p^2)$ and $p-a\le p^{k-2}$, so $H(a)-H(p)=O(p^k)$. On the other hand $a^6=p^6(1+o(1))$, and $p^k=o(p^6)$. By (2),
$$
\widetilde H(a)-H(p)=\left(\frac5{16}+o(1)\right)p^6>0 .
$$
Each real $a$ here gives a legitimate simultaneous limit through the finite integer leaf counts above. The two sequences need not have exactly equal finite densities at each order; the original conjecture is about limiting profiles. This proves the claimed counterexamples for every fixed $k\ge7$, while leaving open the best shape for those horizontal slices.
