# The first two shells of the marked coset

Suppose a Conway graph exists. Let $r$ be its Seidel rank over the field of seven elements. The [determinant-49 reduction](../maximal-marked-lattice/README.md) supplies a graph lattice $L$, an even rank-44 overlattice $U$ of determinant 49, and 99 marks $v_i=3u_i$ in $C=v_0+3U$. Every such integral extension satisfies the same bound, including the original lattice $L$.

| $r$ | 36 | 38 | 40 | 42 |
|---|---:|---:|---:|---:|
| Upper bound on antipodal root pairs in $U$ | 4 | 4 | 4 | 4 |

Here a root has squared norm two. At rank 42 this also gives $N_{14}\le8$ for the number of oriented norm-14 integral graph eigenvectors. The bounds allow the case of a rootless lattice.

## Short vectors in the marked coset

The Gram matrix of the $u_i$ is $3I-A+J/9$ and their sum is zero. Their evaluation map has image the $-4$ eigenspace and satisfies $\sum_i(x,u_i)^2=7\|x\|^2$. For $x\in C$ write $N=\|x\|^2$ and $g_i=(x,v_i)$. All $g_i$ have the same residue $k\in\{1,4,7\}$ modulo nine. Indeed $v_0$ has inner products $28,-8,1$ with the marks, and $(x-v_0,v_i-v_j)$ is a multiple of nine. Evenness gives $N\equiv2k-28\pmod{18}$ by expanding $\|x-v_i\|^2$. The numbers $g_i/9$ have sum zero and square sum $7N/9$. Each belongs to $k/9+\mathbb Z$. Summing $(g_i/9-k/9)(g_i/9-k/9+1)\ge0$ gives
$$7N/9\ge99k(9-k)/81.$$
The residues and inequality rule out all $N<22$. At 22 equality holds. The entries of $g/9$ equal $7/9$ at a set $B$ of 22 vertices and $-2/9$ elsewhere. The eigenvector equation becomes $A\chi_B=4(\mathbf1-\chi_B)$. Thus $B$ is independent and each vertex outside it sees four of its members.

Conversely an independent set of size 22 attains the eigenvalue bound $99\cdot4/(14+4)=22$. To see its equality condition, decompose its indicator into its mean and a centered vector. Its adjacency quadratic form is zero, and the centered part attains the least eigenvalue $-4$. For each such $B$ set
$$y_B=\tfrac17\sum_{i\in B}u_i,\qquad w_B=y_B-u_0.$$
Then $(y_B,u_i)=\chi_B(i)-2/9$ and $\|y_B\|^2=22/9$. Hence norm-22 points in $C$ correspond bijectively to the independent 22-sets with $w_B\in U$, by $x=3y_B$. Every $w_B$ lies in $L^*$ by pairing with the generators $u_i-u_j,3u_0$, and has even norm $6-2\chi_B(0)$. Its class in $L^*/L$ is isotropic. If $D$ is a second independent 22-set then
$$7(w_B,w_D)=|B\cap D|+20-7(\chi_B(0)+\chi_D(0)).$$
A family of sets therefore occurs together in the marked coset of some maximal extension exactly when every two meet in $1\pmod7$ vertices. This is the criterion for their isotropic classes to span a totally isotropic subspace, which extends to a maximal one. Distinct compatible sets can meet in 1, 8 or 15 sites.

At $N=28$, put $n_i=(g_i-1)/9$. The sum, square sum and neighbor sums are
$$\sum n_i=-11,\qquad \sum n_i^2=23,\qquad An=-4n-2\mathbf1.$$
Only the following nonzero profiles can occur. Superscripts denote multiplicities.

| Entries of $n$ | Interpretation |
|---|---|
| $3^1,(-1)^{14}$ | One of the 99 marks |
| $2^1,1^3,(-1)^{16}$ | Reflection of a mark in a root |
| $1^6,(-1)^{17}$ | Six positive and seventeen negative sites |

For the finite check, $\sum n_i(n_i+1)=12$ bounds every entry between $-4$ and 3. Enumerate the counts at $-4,-3,-2,1,2,3$, pad at $-1,0$ by the sum and length, and test the minimum and maximum possible sum of fourteen entries other than the site in question. The only additional profile is $2^2,(-1)^{15}$. Both sites at 2 would need at least ten negative neighbors among fifteen, giving them at least five common neighbors. Run `python3 verify.py` to check the enumeration.

An entry 3 gives $(x,v_i)=28$, forcing $x=v_i$. At an entry 2, $b=(v_i-x)/3$ is a root with $(u_i,b)=1$. Conversely a root with that evaluation gives $x=v_i-3b$ by reflection. Each antipodal pair has fourteen sites with nonzero evaluation and a unique sign with evaluation one at each such site. The second profile has a unique entry 2, so there are exactly fourteen of these points per root pair. In the last profile let $P,N_-$ be the positive and negative sites and let $e_P,e_-$ be their internal edge counts. Summing the neighbor equations on both sides gives $e_-=1+e_P$. Each negative site sees $d_P=2+d_-$ positives. Thus it accounts for at least $1+2d_-$ unordered pairs of positives, and all negative sites together account for at least $21+4e_P$ pairs counted with multiplicity. The graph common-neighbor bound allows at most $30-e_P$. Hence $e_P\le1$.

## Roots and pairs of independent sets

An integral norm-14 eigenvector is the signed indicator of a bipartite Fano configuration with sides $P,N$ of size seven. Its incidence blocks are the complements of lines of the Fano plane. Each same-side pair already has both common neighbors in the opposite side. By the signed eigenvalue equation each external site therefore sees either one site of each side or neither. There are 70 sites $X$ of the first kind, by counting the ten external neighbors of each positive site. The other 15 form a set $Y$. For any $y\in Y$ and each $p\in P$, both common neighbors lie in $X$. Each such neighbor sees just one $p$, using all fourteen neighbors of $y$. Consequently $Y$ is independent and both $Y\cup P$ and $Y\cup N$ are independent 22-sets. Conversely, the indicator difference of two such sets meeting in fifteen sites is a norm-14 eigenvector and recovers this configuration. [Short-vector classification and Fano triple closure](../short-support-packing/README.md)

An independent 22-set $B$ has at most one partner meeting it in fifteen sites. The four neighbors in $B$ of each external vertex give blocks of a $2$-$(22,4,2)$ design on $B$. A partner gives a seven-subset $P$ of $B$ and seven four-blocks contained in it. These blocks cover every pair of $P$ twice, so each of the other seventy blocks meets $P$ at most once. There are exactly $7(14-4)=70$ remaining incidences, giving equality for every block. For two distinct partners the two seven-block families must be disjoint, since a shared block has four points in both seven-subsets and three same-side points determine the signed Fano configuration. Counting incidences with the first seven-subset across the second family now gives $7=4|P_1\cap P_2|$, which is impossible.

For any independent 22-set $B$, put $a=|B\cap P|$ and $b=|B\cap N|$. Counting neighbors in $B$ at the seven sites of $P$ gives
$$|B\cap X|=28-4(a+b),\qquad |B\cap Y|=3(a+b)-6.$$
For a set distinct from the two endpoints, interchange the sign sides to arrange $a\ge b$. Two selected positives have just one common nonneighbor in the seven negatives, so $b\le1$. If $b=1$, independence gives $1\le a\le3$. If $b=0$, the displayed counts give $a\ge2$. The intersection with $Y\cup P$ has size $4a-6$. Two distinct independent 22-sets meet in at most fifteen sites, since the indicator difference is a nonzero integral $-4$ eigenvector and its squared norm is at least fourteen. Thus $a\le5$. The unordered pair of intersection sizes of the set with the two endpoints belongs to
$$\mathcal S=\{(1,1),(0,2),(3,6),(6,10),(9,14),(4,5),(7,9)\}.$$

## Every integral extension has at most four root pairs

Write $t_i=(s,u_i)$ for the eigenvector of a Fano root $s$, oriented from $N$ to $P$. Its entries are the difference of the two endpoint indicators. Consider distinct antipodal pairs in $U$, with endpoint pairs $(B_1,B_2)$ and $(D_1,D_2)$. All four endpoints are distinct by uniqueness of the partner. Put $h_{ij}=|B_i\cap D_j|$. Each row and each column of $h$, as an unordered pair, belongs to $\mathcal S$. The roots in $U$ are orthogonal by the [integral-overlattice root argument](../maximal-marked-lattice/README.md). Hence their evaluation vectors are orthogonal and
$$h_{11}-h_{12}-h_{21}+h_{22}=0.$$
The only such matrix is the all-ones matrix. For example, the seven allowed pairs form a loop at 1 and the paths $0,2$; $3,6,10$; $4,5$; and $7,9,14$. On each path any length-four closed walk traverses each used edge twice. A two-vertex walk alternating on a single edge has nonzero alternating sum. A three-vertex walk could have zero alternating sum only if the middle vertex were the average of its two neighbors, which fails for both three-vertex paths. The checker also tests all matrices directly.

For $p$ root pairs, center each of the $2p$ endpoint indicators by subtracting $(2/9)\mathbf1$. The Gram entries are $154/9$ on the diagonal, $91/9$ within a pair and $-35/9$ across pairs. The squared norm of their sum is $(2p/9)(315-70p)$, so $p\le4$. This applies simultaneously to every integral extension under consideration. At rank 42 the discriminant is anisotropic, so every norm-14 integral eigenvector gives a root already in $L$ by the short-vector dictionary. Each antipodal root pair contributes two oriented eigenvectors. The existence of the 99 marks in any of the four ranks remains open.
