# The Keough–Shane domination-count conjecture at every order at least 160

**Theorem.** If $G$ is a finite simple undirected graph on $n\ge160$ vertices and $\partial(G)$ counts its dominating vertex sets, then
$$
 \partial(G)+\partial(\overline G)\le 2(2^{\lfloor n/2\rfloor}-1)(2^{\lceil n/2\rceil}-1)+2 .
$$
Equality occurs precisely for the balanced complete bipartite graph or its complement, up to isomorphism. This gives the exact answer at each indicated order, not just a leading equivalent. It does not settle the all-orders conjecture. Our cutoff is sufficient and not asserted minimal.

## 1. The loss and the separation of three centers

For each vertex $i$, write $A_i=N_G(i)$ and $B_i=N_{\overline G}(i)$. These sets partition $V\setminus\{i\}$. Write $p(L)$ for all subsets of $L$. Since a set fails to dominate $G$ if and only if it is contained in some $B_i$, our objective is equivalent to minimizing
$$ D=\left|\bigcup_i p(A_i)\right|+\left|\bigcup_i p(B_i)\right|. $$
The two families are always counted separately. This is the common-neighbor interpretation in BIRS 24w5298, §3.4. For $K_{x,y}$ with both sides of size at least two, the first union comprises all pure-side sets (ones contained within either single side); the second all pure-side sets except the two entire sides. Hence $D(K_{x,y})=2(2^x+2^y)-4$. Set $m=\lfloor n/2\rfloor$, $D_*=2^m+2^{n-m}$ and $D_0=2D_*-4$.

Fix a minimizer, so $D\le D_0$. The previously known degree constraint (Keough–Shane, Lemma 2.1 and Thm. 3.1) implies all $|A_i|,|B_i|\in[m-2,m+2]$. Indeed $2^{|A_i|}+2^{|B_i|}\le D_0$, ruling out sizes $\ge m+3$ for either parity or $\ge m+2$ in even order, and the two sizes sum to $n-1$.

Use the Hamming distance $d(i,j)=|A_i\triangle A_j|$. Then $|B_i\triangle B_j|\ge d(i,j)-2$, as the diagonal changes in at most two places. When $d(i,j)\ge32$, the sum of the $A$-cube and $B$-cube intersection counts is at most $3\cdot2^{m-14}$; at distance at least 16 it is at most $3\cdot2^{m-6}$. In fact $|L\cap M|=(|L|+|M|-|L\triangle M|)/2$, so the two underlying intersection sizes are at most $m+2-d(i,j)/2$ and $m+3-d(i,j)/2$.

No three rows are pairwise at distance at least 32. Otherwise the three individual two-family contributions (before intersections) sum to at least $2D_*$: each is at least $(3/2)2^m$ for even and $2\cdot2^m$ for odd $n$, by balancing the exponents. Subtract at most $9\cdot2^{m-14}$ for their three pair intersections. For any fourth vertex $j$, take a closest center $i$ among the three. Both remaining centers are at distance at least 16 from $j$ by the triangle inequality. The coordinate $i$ belongs to one of $A_j,B_j$ but neither $A_i$ nor $B_i$. Subsets of this $j$ cube containing $i$ therefore add at least $2^{m-3}$ relative to the matching $i$ cube; the two remaining centers may remove at most $6\cdot2^{m-6}$ more. The excess $2^{m-3}-6\cdot2^{m-6}-9\cdot2^{m-14}>0$ contradicts $D\le D_0$.

A maximal 32-separated family thus gives at most two centers and covers all rows by balls of radius 31. One center cannot cover all: each column of the symmetric adjacency matrix contains at least $m-2>31$ copies of either bit, yet a single constant column template would give at most $31n$ total errors over the matrix. Consequently there are two centers $u,v$ (regarded as binary adjacency rows) and nonempty groups $X,Y$ of vertices whose rows are assigned to their respective centers at distance $\le31$. The total number of template errors is at most $31n$.

## 2. Short certificates from opposite groups have little overlap

Let $b=||X|-n/2|$, so the larger group has size $n/2+b$. In each column its template is constant. The true number of either bit is at most $n-(m-2)\le n/2+5/2$, forcing at least $b-5/2$ errors within this group in every column. Thus $b\le 31+5/2$ and each group has size at least $n/2-33.5\ge46.5$.

In each column where $u=v$ at least $m-2$ entries disagree with the prediction. There are at most $31n/(m-2)\le 62n/(n-5)\le64$ such columns. Therefore opposite-group rows have $A$-distance at least $n-64-62=n-126$ and $B$-distance at least $n-128$. Underlying intersection sizes on either side are at most $m+66-n/2$. In particular for certificates involving at most 11 vertices from each group, the sum of all the opposite-group, same-family intersection counts is at most
$$ 2\cdot11^2\,2^{m+66-n/2}<2^{m-6}, $$
since $n/2\ge80$ and $242<256$. In combining certificates from two groups we may always subtract this amount to account for any duplicate subsets; there are no cross-family intersections to subtract.

## 3. Every extremal group has a cohort of twins

In each group choose a largest same-degree cohort $R$, of size $r\ge\lceil46.5/5\rceil=10$. Let $h_A,h_B$ count its distinct $A_i,B_i$, respectively. No vertex belongs both to a nontrivial $A$-duplicate class and a nontrivial $B$-duplicate class. Indeed if $A_i=A_j$, $ij$ is a nonedge; if $B_i=B_k$, $ik$ is an edge; thus $j\ne k$. For three distinct vertices these two equalities would force $jk$ to be an edge by the first, and a nonedge by the second. Since supports of all nontrivial duplicate classes on the two sides are disjoint, $(r-h_A)+(r-h_B)\le r-1$: each nontrivial class loses its size minus one, and if both partitions consist only of singletons the inequality is immediate. In particular $\max(h_A,h_B)\ge (r+1)/2$, so one side has at least six distinct generators in $R$.

The union of the cubes of $k$ distinct equal-size $s$-sets has at least $2^{s+1}(1-2^{-k})$ elements. From each of the first $j-1$ sets choose an element of the $j$th that it misses; the subsets of the $j$th set containing all these elements are new, at least $2^{s-(j-1)}$ of them. Sum over $j$.

Choose six distinct generators on the side with many, of coordinate size $s$; include a representative on the other side, coordinate size $t=n-1-s$. With at most seven rows, this certifies
$$ M(s)=(1-2^{-6})2^{s+1}+2^t\ \ge\ D_*-2^{m-5} $$
in the group's two-family contribution. For transparency, $M(s)/2^m=(63/64)2^{j+1}+2^{n-2m-1-j}$ for $j=s-m\in\{-2,-1,0,1,2\}$. The minima of the five finite values for even and odd $n$ are respectively $2-1/64$ at $j=-1$ and $3-1/32$ at $j=0$. Here $D_*/2^m$ is respectively 2 and 3. If the other side has at least two distinct generators, a second one increases its certified size by at least $2^{t-1}\ge2^{m-3}$, using at most eight rows. The other group always has its seven-row baseline. Section 2 then implies $D\ge 2D_* -2\cdot2^{m-5}+2^{m-3}-2^{m-6}>D_0$. Contradiction. Thus in each selected cohort the other side has exactly **one** generator.

## 4. Propagate the twins and recover the graph

If the identical generators are the $A_i$, write them as $T$ and take ten vertices $R_0$ from the cohort. They lie outside $T$ because there are no loops, and $B_i=T^c\setminus\{i\}$ for each of them. The cohort subcubes cover all of $p(T)$ and all of $p(T^c)$ except those subsets containing every vertex of $R_0$. Hence they contribute at least $D_*-2^{m-7}$: $2^{|T|}+2^{n-|T|}\ge D_*$ and $n-|T|\le m+3$ because the complement-side generators have size at most $m+2$. If the identical generators are the $B_i$, exchange the letters. In either case write $T_A,T_B$ for the resulting complementary templates for the $A,B$ families in this group.

For any row $j$ of this group, if $A_j\not\subseteq T_A$ or $B_j\not\subseteq T_B$, choose one offending coordinate. At least $2^{m-3}$ subsets of the corresponding true cube contain it, entirely outside the matching cohort template and hence new in that family. This certificate uses at most eleven rows. After adding the other group's baseline and subtracting cross overlaps, $D\ge 2D_*-2^{m-7}-2^{m-5}+2^{m-3}-2^{m-6}>D_0$. Thus every row of the group satisfies both subset relations; since $A_j,B_j$ partition $V\setminus\{j\}$, necessarily $A_j=T_A\setminus\{j\}$, $B_j=T_B\setminus\{j\}$.

Each group now induces a clique or an independent set: for two different group indices $i,j$, symmetry of their adjacency asserts $\mathbf1_{T_A}(i)=\mathbf1_{T_A}(j)$. All cross edges likewise have a constant bit, being represented at $(i,j)\in X\times Y$ both by a function only of $j$ and by one only of $i$. If cross edges are present, neither group can be a clique (universal vertices violate the degree bound); if none are present, neither group can be independent (isolates violate it). Therefore $G$ or $\overline G$ is complete bipartite. The exact formula in §1 and integer balancing force side sizes $m,n-m$, proving the claim.
