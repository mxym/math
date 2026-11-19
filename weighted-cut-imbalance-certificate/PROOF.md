# The weighted cut-imbalance bound of Braverman–Efremenko–Kol–Saxena–Zhang: a finite rational certificate

**AI-assisted research note, independently checked internally; not externally peer reviewed.** This is a computer-assisted proof, not a formalization in a proof assistant. All inequalities used by the certificate are exercised using rational or integer arithmetic, with no floating point, optimizer, third-party data or graph enumeration required for verification.

## 1. Statement, scale and prior work

For a finite undirected graph with nonnegative weights on pairs of distinct vertices let $W=\sum_{i<j}w_{ij}$, $C$ its maximum cut weight and $d_i=\sum_{j\ne i}w_{ij}$. Write $K(a)=\mathbb E|\sum_i a_i\epsilon_i|$ for independent uniform random signs. Then
$$ C\ \ge\ \tfrac25 W+\tfrac4{15}K((d_i)). \tag{1}$$
This includes edges of zero weight, arbitrary graph order, isolated vertices, all real nonnegative weights and all ties. Parallel edges may be added on a single pair. No self-loops are contemplated. Weight zero is immediate; normalize $W=1$ by homogeneity from now on. If $S=\{i:\epsilon_i=+1\}$ and $w(S)$ is total edge weight within $S$, then $2(w(S)-w(S^c))=\sum_i d_i\epsilon_i$ and $\mathbb E[w(S)+w(S^c)]=1/2$. Thus $\mathbb E\min(w(S),w(S^c))=(1-K(d))/4$, so (1) is exactly [ITCS 2025, Conjecture 3](https://doi.org/10.4230/LIPIcs.ITCS.2025.22), or [ECCC TR22-179 rev.1, Conjecture 1.3](https://eccc.weizmann.ac.il/report/2022/179/revision/1/download/). Their §11 proves the equal-edge clique case, including equality for cliques of order 3 and 5, and the equal-edge case with at least $10^9$ edges. Repository [#110](https://github.com/mxym/math/pull/110) addressed arbitrary equal-edge graphs; [#115](https://github.com/mxym/math/pull/115) addressed arbitrary weights when the positive support is eight-colorable. Neither is needed below. No result is asserted for their separate Conjecture 1.5. No priority guarantee.

By BEKSZ's **own** Theorems 1.2, 1.4 and 9.1, once (1) is established, their one-feedback adversarial binary corruption channel has optimal asymptotic resilience $7/23$: for each fixed $\varepsilon>0$ (in the nontrivial range), constant rate depending on $\varepsilon$ is attainable at resilience $7/23-\varepsilon$, and the upper threshold is $7/23$. No new protocol construction, endpoint positive-rate assertion, computational efficiency guarantee, multi-feedback or erasure-channel result is claimed.

## 2. Majorization: where graph order disappears

Order the degrees nonincreasingly, padding by isolated vertices so there are at least $T=32$ coordinates. We continue to append zeros to any finite vector when needed. Let $u_k=\sum_{i=1}^k d_i$, $d=d_1$, $c=C$ and $B(c)=(15c-6)/4$. Thus $u_1=d$ and $u_k\le2$ for every $k$, not just $k\le T$; $\sum_i d_i=2$. We will prove $K((d_i))\le B(c)$.

We use: if two nonincreasing vectors $a,b$ of equal total satisfy $\sum_{i\le k} a_i\le\sum_{i\le k} b_i$ for every $k$, then $K(a)\le K(b)$. Brief proof: in a common padded dimension, $K(v)=\max_h v\cdot g(h)$ with $g_i(h)=\mathbb E[\epsilon_i h(\epsilon)]$, the maximum over all functions $h$ into $[-1,1]$. A pointwise signed maximizer exists. The attainable $g$ are invariant under coordinate permutations. For sorted $a$, an optimizing $g$ may be rearranged in nonincreasing order (swapping an inversion cannot lower the scalar product). Summation by parts gives $a\cdot g\le b\cdot g\le K(b)$. Also $K$ is convex by the triangle inequality. Since $d_i\le1$, the vector $(1,1,0,\dots)$ majorizes $(d_i)$, and $K(1,1)=1$. This proves (1) if $c\ge2/3$. A uniformly random cut gives $c\ge1/2$ and a singleton cut gives $d\le c$.

Our only remaining parameters are $(c,d)$. Put the highest-degree vertex on side 0; put all others independently on side 1 with probability $p$. The expected cut is $pd+g(1-d)$, $g=2p(1-p)$. Therefore every pair still under consideration belongs to the **closed** convex polygon $\mathcal D$ obtained from $[1/2,2/3]\times[0,2/3]$ by intersecting the thirteen halfplanes
$$ c-g+(g-p)d\ge0,\qquad p=j/12,\quad j=0,\ldots,12. \tag{2}$$
No converse is needed: some points of the polygon may not come from any graph.

## 3. Bounds on top-degree partial sums

Fix $2\le k<T$. Split the graph into $H$ its top vertex, $G$ the next $b=k-1$ vertices, and $R$ the rest. Denote the masses of edges $GG,HG,RR$ by $A,L,D$ respectively. The masses $HR$ and $GR$ are therefore $d-L$ and $1-d-A-D$ respectively. Counting degrees of $H\cup G$ gives
$$u_k=1+A+L-D.\tag{3}$$
The following constraints are universal:
$$ -A\le0,\quad -L\le0,\quad -D\le0,\quad L\le d,\quad A+D\le 1-d;\quad A\le 0\ \text{if }b=1.\tag{4}$$

Put $H$ on side 0, put a uniformly random $r$-subset of $G$ on side 1, then independently place each vertex of $R$ there with probability $p=j/12$. Write $t=r/b$, $g=2p(1-p)$, $x=t(1-p)+(1-t)p$. A $GG$ edge is cut with probability $h=2r(b-r)/(b(b-1))$ for $b>1$ (use $h=0$ for $b=1$, since then $A=0$). The crossing probabilities for $HG,RR,HR,GR$ are $t,g,p,x$. Since the expected cut cannot exceed $c$,
$$ (h-x)A+(t-p)L+(g-x)D\le -x+c+(x-p)d.\tag{5}$$
This uses only the size of $G$. No probabilistic limit or assumptions on the number or dependence of tail edges occur.

For each $k$ we allow trivial bounds $u_k\le2$ and $u_k\le kd$. To obtain more, write each row in (4) or (5) as $v\cdot(A,L,D)\le s_0+s_1 c+s_2d$. Any nonnegative combination of up to three rows with $\sum\lambda v=(1,1,-1)$ yields the affine upper bound
$$u_k\le\ell_k(c,d)=1+\sum\lambda(s_0+s_1c+s_2d).\tag{6}$$
Only actual nonnegative identities are used: no completeness or optimization theorem for this class of upper bounds is needed.

## 4. Finite covering lemma and interpolation

The substantive finite rational calculation is:

**Finite lemma.** The closed polygon (2) is a union of 957 convex polygons. For each such polygon $P$ there is *one fixed choice* of bounds $\ell_k$ of the preceding types for $2\le k\le31$. At every vertex $z=(c_z,d_z)$ of $P$ there is a nonincreasing nonnegative vector $a^z$ with 32 entries, total 2, and
$$ a^z_1\ge d_z,\qquad \sum_{i\le k}a_i^z\ge\ell_k(z)\quad(2\le k\le31),\qquad K(a^z)\le B(c_z).\tag{7}$$

**Why a finite lemma suffices at all orders.** Choose any actual graph with $v=(c,d)\in P$, and write $v=\sum_z\theta_z z$ with $\theta_z\ge0$, $\sum_z\theta_z=1$. Put $a=\sum_z\theta_z a^z$; it is sorted, nonnegative and has total 2. At rank 1 it dominates $d$, since $d$ is affine. At each $2\le k\le31$, $u_k\le\ell_k(v)=\sum_z\theta_z\ell_k(z)\le\sum_{i\le k}a_i$. For **every** larger rank $k\ge32$ the sum on the right is exactly 2 after zero-padding $a$, while $u_k\le2$. In particular we never set the actual graph's $u_{32}$ equal to 2 and never discard a nonzero degree. Majorization and convexity give
$$K((d_i))\le K(a)\le\sum_z\theta_z K(a^z)\le\sum_z\theta_z B(c_z)=B(c).$$
The same reasoning holds on every shared edge and corner; strict inequalities are unnecessary. As a check on the two classical tight points: the unit-weight-total triangle has $(c,d,K)=(2/3,2/3,1)$ and the equally weighted 5-clique has $(3/5,2/5,3/4)$ by the three- and five-sign binomial distributions. Both have $K=B(c)$. We do not classify equality.

## 5. Exact proof of the finite lemma

The two included files `certificate.json` (a list of finite choices) and `verify.py` (a stand-alone Python 3 standard-library replay) specify the full computation. Run `python3 -B -O verify.py`. There are no silent assertions, floating-point inequalities, solver/library imports or dependencies on the discovery files.

1. For each $k$ the row numbering starts at zero, first (5) lexicographically in $(r,j)$, $0\le r\le k-1$, $0\le j\le12$; the additional rows are exactly (4) in displayed order. Each list entry in the bound catalog contains up to three row IDs (or the literal `mass` or `max` for the trivial bounds). For each support the verifier finds a nonsingular square subsystem, solves by rational determinants and **checks all three identities** and every multiplier's nonnegativity before deriving the three affine coefficients. No precomputed multiplier or coefficient is trusted.
2. The tree starts at the exact rectangle clipped by (2). For an internal node $[(k,i,j),L,R]$ use $f=\ell_{k,i}-\ell_{k,j}$ and intersect the current polygon with $f\ge0$ and $f\le0$, recursing on the respective closed polygons. Opposite signs at consecutive vertices give the exact affine line intersection; vertices on the line are retained. Starting from a counterclockwise convex polygon this is ordinary convex halfplane clipping. Each split is checked to have positive signed area on each side and to preserve the sum of twice areas. The halves cover their parent by the sign alternative, not merely because their areas agree. A leaf is a one-entry list containing 30 catalog indices, used unchanged at all its corners.
3. For such a leaf and corner set $y_0=0,y_1=d_z,y_k=\ell_k(z)$ for $2\le k\le31$, and $y_{32}=2$. To construct $a^z$, from index $i$ choose $j>i$ maximizing $(y_j-y_i)/(j-i)$, breaking ties by largest $j$. Use that slope on coordinates $i+1,\ldots,j$ and repeat. The verifier **directly checks** all inequalities on the sums, nonnegativity, monotone order, length and total; correctness does not depend on the optimality of this construction.
4. If $\sum_i(a^z_i)^2\le B(c_z)^2$, (7) follows by Cauchy–Schwarz, independence and $B(c_z)>0$. Otherwise clear a common denominator $D$ and omit zero coordinates, which do not affect $K$. Each group of $s$ equal entries $b=Da_i$ has integer signed sum $(s-2j)b$ with multiplicity $\binom sj$, $0\le j\le s$. Multiply the distributions on two disjoint sets of groups. For a value $x$ in the first distribution and values $y$ in the second, sum $|x+y|$ by sorting the second distribution; use the minus sign exactly for $y<-x$. Divide the final multiplicity-weighted sum by $D 2^{\#\{i:a_i\ne0\}}$ and check (7).
5. The deterministic replay checks 2,286 catalog entries, 956 splits, 957 leaves and 3,791 corner incidences, with repeated evaluations cached by the exact pair (point, all leaf choices). Of the 3,729 distinct such pairs, 2,318 pass by the square-moment shortcut and 1,411 by exact absolute first moment. The twice-area of the root and the sum of the leaf twice-areas are both $130792/765765$. These are cross-checks, not assumptions. The finite lemma follows, completing the proposed proof of (1).

The 32 slots, cut probabilities with denominator 12, and the finite choices were selected computationally. The certificate only uses the explicit rational choices and does not depend on how they were found. Completeness of a cut-polytope catalog, numerical optimization tolerances or graph orders through some cutoff are not substitutes for the replay.
