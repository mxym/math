# Equality in the full weighted BEKSZ inequality

**AI-assisted follow-up; independently checked internally, not externally peer reviewed. No priority claim.** This note uses the already public [full weighted certificate, repository #123](https://github.com/mxym/math/pull/123). The inequality and its coding interpretation are not reproved. The result here is a characterization of equality, not a change in the channel threshold.

**Theorem.** A finite loopless undirected graph with total nonnegative edge weight $W>0$ has
$$15C=6W+4\mathbb E\left|\sum_i d_i\epsilon_i\right|$$
where $C$ is the maximum cut weight, $d_i$ are weighted degrees, and $\epsilon_i$ are independent uniform signs, if and only if its positive edges form a uniformly weighted triangle or a uniformly weighted five-clique, up to isolated vertices. Edges with zero weight are ignored and parallel edges are aggregated per pair. When $W=0$, both sides are zero independently of the number of vertices.

**Known examples / scope.** [BEKSZ, full text, Conjecture 1.3 and §11.1](https://eccc.weizmann.ac.il/report/2022/179/revision/1/download/) already identified these two equal-weight clique examples; [repository #110](https://github.com/mxym/math/pull/110) classifies them for equal-weight simple graphs. [#115](https://github.com/mxym/math/pull/115) checks facets in a bounded-color class. [#123](https://github.com/mxym/math/pull/123) proves the inequality for arbitrary weights, without an equality classification. This note treats necessity for arbitrary real nonnegative weights. Tightness of an auxiliary bound need not mean equality for a graph.

## 1. Extracting precisely the tight corner vectors

Normalize $W=1$, sort $d_1\ge\cdots\ge d_N\ge0$, pad to $N\ge32$, and write $v=(c,d)=(C,d_1)$, $B(c)=(15c-6)/4$, $K(s)=\mathbb E|s\cdot\epsilon|$. If $c>2/3$, $B(c)>1\ge K((d_i))$, so (normalized) equality is impossible. For $c\le2/3$, take any closed leaf polygon $P$ containing $v$ in #123's two-parameter cover. For each corner $z=(c_z,d_z)$, let $a^z$ denote the sorted 32-coordinate dominating vector constructed from that cell's specified prefix bounds, padded with zeros to dimension $N$; $\sum a_i^z=2$. Its construction depends on the cell as well as the corner. The published proof shows $K(a^z)\le B(c_z)$. The companion exact replay establishes that the complete set of pairs $(z,\text{positive entries of }a^z)$ with equality here is:

| $c_z$ | $d_z$ | Nonzero coordinates of $a^z$ |
|---|---|---|
| $2/3$ | $2/3$ | $2/3$ three times |
| $3/5$ | $2/5$ | $2/5$ five times |
| $3/5$ | $107/260$ | $107/260$ three times; $199/520$ twice |

This table retains **both** the parameters and the constructed vector. A single geometric corner can be used with different witnesses in different leaves. The checker verifies the hashes of the published certificate and verifier, reconstructs 2,286 valid bounds, exhaustively visits 956 splits, 957 leaves and 3,791 corner incidences, deduplicating only equal (corner, vector of indices for all bounds) cases, and tests equality on the exact signed first moment whenever the square-moment shortcut does not apply. It also checks the entire polygon twice-area and exact equality of the set of found pairs to the displayed table. For the shortcut, if $\sum a_i^2\le B^2$ then $K(a)<B$: the vector cannot have just one nonzero entry since it totals 2 and $B\le1$. With at least two positive entries, $|a\cdot\epsilon|$ is not constant, since the all-positive outcome has absolute sum 2 and reversing just one of the positive coordinates yields strictly less. Thus the Cauchy–Schwarz step is strict **even if the variance test is an equality**. This finite replay concerns a particular published auxiliary proof and not any assertion about all possible majorizers.

## 2. What equality forces inside each closed polygon

Write $v=\sum_z\theta_z z$, $\theta_z\ge0$, $\sum_z\theta_z=1$ and $a=\sum_z\theta_z a^z$. By #123, the nonincreasing vector $a$ majorizes $(d_i)$: their totals are 2 and every prefix of $a$ dominates the corresponding true degree prefix. For ranks $k\ge32$ its cumulative sum is 2, regardless of how many vertices the actual graph has.

Define $h(\epsilon)=\mathrm{sgn}(\sum_i d_i\epsilon_i)$, setting $\mathrm{sgn}(0)=0$, and $g_i=\mathbb E[\epsilon_i h(\epsilon)]$. Then $K((d_i))=\sum_i d_i g_i$ and $g$ is nonincreasing: for $i<j$, condition on the remaining signed sum $T$; averaging the two signs gives
$$g_i-g_j=\tfrac12\mathbb E[\mathrm{sgn}(T+d_i-d_j)-\mathrm{sgn}(T-d_i+d_j)]\ge0.$$
Consequently summation by parts, then the pointwise estimate $(a^z\cdot\epsilon)h\le|a^z\cdot\epsilon|$, yields
$$K((d_i))=d_{\rm vec}\cdot g\le a\cdot g=\sum_z\theta_z\mathbb E[(a^z\cdot\epsilon)h(\epsilon)]\le \sum_z\theta_z K(a^z)\le \sum_z\theta_z B(c_z)=B(c).$$
If the two ends are equal, every $z$ with $\theta_z>0$ must be a table entry **and the same $h$ must maximize each one**. In particular, wherever $a^z\cdot\epsilon\ne0$ this forces $h(\epsilon)=\mathrm{sgn}(a^z\cdot\epsilon)$ pointwise (the cube vertices have positive probability).

The table's three-positive entry has the unique maximizing function $M_3=\mathrm{sgn}(\epsilon_1+\epsilon_2+\epsilon_3)$. Both five-positive entries have $M_5=\mathrm{sgn}(\epsilon_1+\cdots+\epsilon_5)$: their total is 2 and in each case even the sum of the two largest entries is strictly less than 1. There are no ties. These majority functions differ, for instance at $(+,+,-,-,-)$, so three- and five-positive corners cannot both have positive interpolation weight. Thus either $c=2/3$ and $h=M_3$, or $c=3/5$ and $h=M_5$. This reasoning does not assume strict convexity of $K$, uniqueness of the interpolating decomposition, or a special incidence pattern among the leaf corners.

If $h=M_s$ for $s=3,5$, then $g_i=0$ at all $i>s$ by independence, whereas for $i\le s$ its value is $2^{-(s-1)}\binom{s-1}{(s-1)/2}$ (condition on the other signs; only a tie among them contributes). This is $1/2$ or $3/8$ respectively. If $s=3$, then $B(2/3)=1$; if $s=5$, then $B(3/5)=3/4$. The identity $\sum_i d_i g_i=B(c)$ in both cases forces $\sum_{i=1}^s d_i=2$. Hence every remaining degree is zero. We derived the finite support of the **actual** graph instead of assuming it matched the support of its comparison vector.

## 3. Recovering the physical weights

In the three-vertex case all singleton cuts have sizes $d_i\le c=2/3$ and their three degrees sum to 2. Every degree is $2/3$ and the three edge weights are each $1/3$. In the five-vertex case pad the support by zero degrees to 5 if necessary and choose a uniformly random two-element side. Each edge crosses with probability $\tfrac{2\cdot3}{\binom52}=3/5$. The average cut weight is therefore $3/5$ and no cut exceeds $c=3/5$: all ten cuts must be exactly $3/5$. For every $i\ne j$,
$$d_i+d_j-2w_{ij}=3/5.$$
Summing over $j\ne i$ gives $4(3/5)=4d_i+(2-d_i)-2d_i=2+d_i$, so $d_i=2/5$ for all $i$ and then $w_{ij}=1/10$ for every pair. In particular the extra corner with $d_z=107/260$ is not the parameters of an equality graph; one must not declare it a third family. In both cases the known cliques do give equality by direct binomial evaluation of their sign sums (respectively $K=1$ and $3/4$ at $W=1$). Scaling all weights by the same positive factor and adjoining isolates preserves equality.
