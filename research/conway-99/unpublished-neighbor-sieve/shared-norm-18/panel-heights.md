# Rooted overlaps of norm-18 markings at all four ranks

At any rank, take two oriented norm-18 vectors with dot product nine sharing a positive root and its four negative neighbors. Their common nine sites consist of four positives and five negatives. Their rooted incidences belong to at most **six types**, all with exactly two shared positive pair labels. Distinct markings sharing three such labels have dot product eight or ten. The [final counting contradiction](#the-three-label-exclusion-and-the-rank-38-contradiction) excludes the rank-38 two-type alternative. The difference of the markings has norm 18 and therefore has only signed unit nonzero entries. This rules out opposite signs on their common sites and gives the three 4-regular bipartite supports used below.

The local conclusion holds for every short-labeling population. In the [earlier two panel exclusions](higher-moments.md#a-forced-overlap-at-rank-38), the tests on a given dot-nine pair used the two-type hypothesis only to bound exterior heights, their multiplicities and their adjacencies. The [height-three theorem](height-three.md) now supplies those conditions without the hypothesis. Separately, at Seidel rank 38, when norms 18 and 24 are the only two of the twelve selected unit types, the rooted count would force **at least 4,645 distinct unordered pairs of oriented vectors** with three shared labels, contradicting the final exclusion. The earlier bounds in that alternative were 1,549 distinct pairs and 22 types.

## Changing the root

The common nine sites and the two exclusive nine-sets form three panels. On the common panel use the original signs and on the exclusive panels reverse them. Each norm-18 marking is the difference of the signed indicators of two panels, up to overall sign. In each panel edges change color. Between panels they preserve color. A vertex of internal degree $d$ has $4-d$ neighbors in each of the other two panels. All three panels have the same color sizes, since each two-panel marking has nine positives and nine negatives.

Let $x$ be **any** internal degree-four site. The two markings through its panel can be oriented to agree positively at $x$ and negatively at its four internal neighbors $Q$. Among the other sites of the same color in this panel write $c$ for the number meeting $Q$ twice and $z$ for the number missing $Q$. Then
$$2+2z\le c\le3.$$

Indeed, in either marking the eight other positives receive twelve incidences from $Q$. Each receives at most two, by the common-neighbor bound with $x$. If $n_0$ miss $Q$, exactly $4+n_0$ meet it twice. Each such vertex is the unique second common neighbor of one of the six pairs in $Q$. A vertex cannot represent two different pairs since it would then have at least three common neighbors with $x$. The two marked subsets of the six pair labels intersect at exactly the $c$ common positives meeting $Q$ twice. Each marking has $n_0\ge z$, so inclusion-exclusion gives the lower bound. The [four-label exclusion](exclusion.md#nine-shared-sites-force-a-tenth) gives the upper bound.

Rows below are binary incidence masks from the positive to the negative side, with the root first and its four neighbors in the low bits. In $(15,19,60)$ the site with row 60 meets the other two rows in two and one positions. It gives $c=1$. In $(15,16,19,28)$ the first row meets the other three in zero, two and two positions. It gives $(c,z)=(2,1)$. Both contradict the displayed inequality. The other three-positive candidate, $(15,51,60)$, was excluded previously. An eligible positive root therefore has at most five possible negative neighbors in its panel. Two eligible positive roots would have four neighbors each among those five and would share at least three, which is impossible. A given oriented pair occurs at most once in the earlier count of 4,645 rooted pairs.

## A panel with eleven edges has minimum internal degree two

The rooted census now permits four and five as the color sizes, and 11, 12 or 13 internal edges. The number $e$ of internal edges is the same for all three panels. Indeed the cross edges between two sides of the same color and size $n$ number $4n-e$ when counted from either panel. Label the side of size four first in all three panels.

For a marking let the height of an off-support site be its number of neighbors of either sign. The two numbers agree. The [height-three counting theorem](height-three.md) gives height at most three, at most one site of height three, and no edge between that site and another off-support site of height at least two. A site in the omitted panel has height $4-d$ for this marking. Each panel therefore has minimum internal degree one, at most one leaf and no edge between a leaf and a degree-two site.

For one marking write $P,N$ for its two sides, each of size nine, and $h$ for the off-support height. For $y\notin P\cup N$ count two-step walks from $y$ to $P$. There are $18-h(y)$ in total and $4h(y)$ with middle vertex in $P\cup N$. For $y\in P$ the total is $14+2\cdot8=30$ and sixteen use a middle vertex in the support. For $y\in N$ the total is fourteen and none use such a middle vertex. Hence
$$
\sum_{x\sim y,\ x\notin P\cup N} h(x)=
\begin{cases}
18-5h(y) & y\notin P\cup N,\\
14 & y\in P\cup N.
\end{cases}
$$

Let $D_0,D_1,D_2$ be the panels, $E$ the 72 outside sites, and $h_j$ the height for the marking omitting $D_j$. For $y\in D_0$ the preceding identities give
$$
\begin{aligned}
\sum_{x\in E,\ x\sim y}h_0(x)&=d(y)-2+\sum_{z\in D_0,\ z\sim y} d(z),\\
\sum_{x\in E,\ x\sim y}h_j(x)+\sum_{z\in D_j,\ z\sim y}(4-d(z))&=14 \quad(j=1,2).
\end{aligned}
$$
These equations allow us to test $D_0$ knowing just the two color degree sequences of each companion.

### Counts over the six sides

For $x\in E$ write $(u_j,v_j)$ for its contacts in the two sides of $D_j$. The three differences $u_j-v_j$ agree, and $h_j=u_{j+1}+v_{j+2}$ with indices taken modulo three. Every count is between zero and three. If $D_j$ already contains a leaf then $h_j\le2$ on $E$. Otherwise at most one exterior site has $h_j=3$.

Index the six sides by $a$, write $n_a$ for the side size, $m_a(x)$ for its contact count and $\bar a$ for the opposite side of the same panel. The first moments are $\sum_E m_a=6n_a+e$, because a site of internal degree $d$ has $8-d$ neighbors in the core. The target second moments count all common neighbors of pairs of sites and subtract those already in the three panels. The following rows use $d=d(z)$ in each sum.

| Moment on $E$ | Target |
|---|---|
| $\sum\binom{m_a}{2}$ | $n_a(n_a-1)-\sum_{z\in\bar a}\binom d2-\sum_{z\text{ in other sides of the same color}}\binom{4-d}{2}$ |
| $\sum m_a m_b$, opposite sides in the same panel | $2n_a n_b-e$ |
| $\sum m_a m_b$, same color in different panels | $2n_a n_b-(4n_a-e)-\sum_{z\text{ in the third side of this color}}(4-d)^2$ |
| $\sum m_a m_b$, different colors in different panels | $2n_a n_b-\sum_{z\in\bar a\cup\bar b}d(4-d)$ |

For example, a core common neighbor of two sites in different panels and of the same color must belong to the third panel. There its $4-d$ contacts to either side give $(4-d)^2$ pairs. For different colors the middle vertex is instead in one of the two named panels, using one internal and one cross edge.

### Exact finite check

Enumerate all four-by-five binary panels up to independent permutations of their two sides. Impose the pair quotas, the degree and leaf restrictions, and the change-of-root inequality. At $e=11$ there are eighteen panels, twelve with a leaf and six without. Together they have seven different pairs of color degree sequences. Fix one of the twelve panels as $D_0$. The two companions have an unordered pair of these seven degree profiles, with repetition allowed. This gives $12\binom82=336$ cases.

In each case the moment table, the total of 72 sites and the three height-three budgets have nonnegative count variables for the contact profiles. In 295 cases these equations already give an integer separating inequality. For the other 41 cases, refine the variables as follows.

* Label the actual contact subset of $D_0$ for each exterior profile. A contact subset must respect the pair quotas within $D_0$ and meet each closed panel neighborhood in at most two points. It must respect the forbidden height-three adjacencies.
* For each companion panel, color and degree $d$, distribute its indicated number of sites among the possible $(4-d)$-element contact subsets of that color in $D_0$. These subsets must also respect the pair quotas and common-neighbor caps.
* At each site in $D_0$ enforce its $6+d$ exterior neighbors, its $4-d$ neighbors per companion, and the two-step walk identities above. At each pair in $D_0$ enforce its common-neighbor quota exactly, including the known neighbors in $D_0$ and the contributions from both companions and $E$.

After slack variables for upper bounds, every graph would give $M n=b$ with nonnegative $n$. For every case the [archived integers](panel-height-duals.json.gz) give $M^t y\ge0$ and $b^t y<0$. The [checker](panel_heights.py) regenerates the catalogues, every column and every target, and checks the signs using Python integers. Thus every eleven-edge panel has minimum degree two.

## Ten shapes before the thirteen-edge test

| Internal edges | Rooted row masks |
|---:|---|
| 11 | $(15,3,17,28)$, $(15,3,20,25)$, $(15,3,20,28)$ |
| 12 | $(15,3,21,22)$, $(15,3,21,26)$, $(15,3,21,28)$, $(15,17,19,22)$, $(15,17,19,28)$, $(15,17,22,26)$ |
| 13 | $(15,19,21,26)$ |

Every remaining rooted shape has four positives. Reorienting at any degree-four site shows that such a site must lie on the side of four, and there can be at most one in each panel. At thirteen edges the four degrees on the smaller side sum to thirteen, so each of the three panels has a degree-four site. Consequently all three must have the last shape in the table.

Run `python panel_heights.py --genbg /path/to/genbg` with NumPy, pynauty and nauty's genbg. The test cross-checks the original rooted catalogue against all 26 one-support graphs, then verifies the 336 inequalities. None of the ten entries is asserted to extend to a graph on 99 vertices. The existence of an overlap of this kind has only been forced here in the specified rank-38 alternative.

## Thirteen internal edges are impossible

At thirteen edges all three panels have the shape $(15,19,21,26)$. Naming the four neighbors of a distinguished root in every one of the 26 supports gives 128 one-support charts on two panels. Exactly 104 have the prescribed shape also on the second panel. Glue a pair of these along their named first panel, then enumerate both color-preserving cross matrices with the required row and column sums. Reject any violation of the common-neighbor quotas. The result has **1,959** distinct cores up to vertex relabeling and permutation of the three panels. For the isomorphism test append one distinct auxiliary vertex per panel and join it to all nine sites of its panel. Use three color classes for the small sides, the large sides, and these three auxiliary vertices.

For each core use the [exterior degree, pair and height tests](higher-moments.md#one-common-panel-is-excluded). In 1,181 cases an integer separating inequality refutes the contact equations. In the other 778 cases also consider two proposed exterior contact sets $W,V$. If the corresponding exterior vertices were adjacent, $|W\cap V|\le1$. Put
$$q_W(i)=2-1_{i\in W}-|W\cap N_{\rm core}(i)|.$$
The second exterior site can neighbor the first only if $q_W(i)>0$ for every $i\in V$, and likewise with $W,V$ exchanged. A height-three site for any marking cannot neighbor an exterior site of height at least two for that marking.

If $W$ occurs and $q_W(i)>0$, there must be at least $q_W(i)$ distinct exterior neighbors of that site whose words contain $i$. Impose this as an implication on the available copies of compatible words. Keeping a subset of these implications suffices. The Boolean encoding also imposes all core degree and pair equalities, the three height budgets, and the at-most-one quota on every triple of contacts. The Boolean encodings allow an arbitrary total number of exterior sites, a relaxation of the required total of 72. The 778 resulting unsatisfiability proofs were independently checked by drat-trim, including 745 from Glucose and 33 from CaDiCaL. The [case archive](thirteen-edge-cases.json.gz) contains the graphs, integer separators and solver choices. The [verifier](three_label_panels.py) reconstructs the catalogue, checks the inequalities, and regenerates and checks the Boolean proofs.

```sh
python three_label_panels.py --edges 13 --genbg /path/to/genbg --drat-trim /path/to/drat-trim
```

Thus **at most nine rooted shapes remain**, the three with eleven internal edges and the six with twelve in the table above. This exclusion holds for a rooted dot-nine overlap at any rank. Only the lower bound of 4,645 distinct occurrences needs the rank-38 two-type hypothesis.

## Only three of the nine shapes are needed at rank 38

Assume $N_{16}=N_{20}=0$. At a fixed positive root $o$ with its four marked negative neighbors $Q$, let $D_t$ be the positive pair labels of a marking $t$. Two distinct markings at this choice have dot product seven or nine and have no sign conflicts, by the [rooted inner-product argument](higher-moments.md#a-forced-overlap-at-rank-38). If $|D_t\cap D_u|\ge3$, their dot product is at least eight, hence nine. The four-label theorem gives $|D_t\cap D_u|=3$.

In the earlier deletion count it suffices to delete one endpoint of each still-present pair **sharing three labels**. All remaining label sets have pairwise intersections of size at most two, precisely the hypothesis for the capacity $C$ used there. Thus the same lower bound $9N_{18}-\sum C$ counts only the three-label pairs. Each oriented pair still has at most one eligible positive root.

At rank 38 in the two-type alternative, **at least 4,645 distinct unordered pairs must therefore belong to just three shapes**, $(15,3,21,22)$, $(15,3,21,26)$ and $(15,3,21,28)$. These are the only rows of the nine survivors on which all three nonroot positives meet two parents. All three have twelve internal edges. Eliminating these three would settle this particular rank-38 alternative even if all six other shapes remained open.

## A triple of pair labels occurs in at most two markings

Keep $N_{16}=N_{20}=0$ and fix $o,Q$. Suppose three markings $t_1,t_2,t_3$ contained the same three pair labels. Each pair is a twelve-edge, three-label overlap as above. Its common positives are exactly $o$ and the three labels. Its common negatives are $Q$ and one extra negative $y_{ij}$. That extra site sees exactly two of the four common positives, since the four parents already supply ten of the twelve internal edges. There are two cases.

If any two of the three $y_{ij}$ coincide, all three coincide. The four disjoint groups are the common nine sites and each marking's nine exclusive sites. Every pair of groups supports a norm-18 marking, either an original marking or a difference. With the same sign convention as before, each group has color sizes four and five, twelve internal edges and eight cross edges between any two five-sides. For pairs on one five-side the common-neighbor budget is $2\binom52=20$. Its own four-side supplies at least 12 incidences, since the four degrees sum to twelve. Each of the other three five-sides supplies at least three, since its five degrees into the chosen side sum to eight. This requires at least 21.

Otherwise the three $y_{ij}$ are distinct. Let $B_i$ be the five positives exclusive to $t_i$ and $A_i$ the three negatives exclusive to $t_i$. Each of $y_{ij},y_{ik}$ sees two sites in $B_i$, and the four parents in $Q$ send six edges to $B_i$, since ten of their sixteen incidences go to the common positives. The remaining ten incidences from $B_i$ into its negative side go to $A_i$. In the support of $t_i-t_j$, the negative side consists of $A_i$, $y_{ik}$, and $B_j$, where $k$ is the third index. There are therefore $20-10-2=8$ edges between $B_i$ and $B_j$. Pairs in $B_i$ now receive at least twelve common-neighbor incidences from the three sites of $A_i$ (ten edges), at least two from $Q$ (six edges), two from $y_{ij},y_{ik}$, and at least three from each of $B_j,B_k$ (eight edges each). These disjoint contributions require 22 incidences against a budget of 20.

A triple of labels belonging to a single parent occurs in at most one marking. Otherwise the shared parent would be a second internal degree-four site on the five-side of a rooted overlap, which the nine-type theorem excludes.

## A population bound before the twelve-edge enumeration

For fixed $o,Q$ shrink each $D_t$ to any four-subset. Distinct subsets stay distinct by the four-label theorem. They are independent in the six-label graph. No star triple can be repeated, and every other triple occurs at most twice by the preceding argument. Let $M$ be their number and let $j,k$ count the label edges joining overlapping and disjoint parent pairs. Over the admissible six-label graphs these rules imply $M+j+k\le6$. The [packing checker](packing.py) enumerates the independent four-subsets and adds each to a family only if the triple multiplicities permit it.

The [rooted transition and prism counts](exclusion.md#counting-windows) give $\sum j=8(99\cdot84-6P)$, $\sum k\ge99\cdot336+6P$, and $P\le851$. Each oriented norm-18 marking contributes at each of its nine positives. Thus
$$9N_{18}\le6\cdot99\cdot560-99\cdot1008+42\cdot851=268590.$$
The count is even by sign reversal, so **$N_{18}\le29,842$ whenever $N_{16}=N_{20}=0$**. At this stage the rank-38 two-type alternative would require a count between 16,684 and 29,842. At rank 42 the earlier bound 12,320 is sharper.

## The three-label exclusion and the rank-38 contradiction

All three twelve-edge shapes in the [forced three-label count](#only-three-of-the-nine-shapes-are-needed-at-rank-38) are impossible. This exclusion on a given pair uses only the Conway parameters. It does not assume the absence of other short vectors.

For each shape choose the root, order its four neighbors, and locate the three designated positives as the second common neighbors of their parent pairs in the one-support graph. Try every negative outside the four parents as the fifth common negative, and check all four row masks. Keep both panels subject to the earlier degree and common-neighbor tests. Permute the exclusive sites with identical contacts to the common panel. Glue two resulting charts on their named common panel and enumerate the two missing cross matrices, as in the thirteen-edge proof.

| Common rows | One-support charts | Gluings with pair quotas | Distinct unrooted cores within this row |
|---|---:|---:|---:|
| $(15,3,21,22)$ | 318 | 406 | 201 |
| $(15,3,21,26)$ | 488 | 12,669 | 5,496 |
| $(15,3,21,28)$ | 370 | 4,951 | 4,288 |

A core can qualify at more than one panel. With panel permutations allowed, the union has **9,106 distinct cores**. On 8,929 the exterior contact equations have an integer separating inequality. On 177 the integer contact counts, triple caps and the exterior-neighbor implications used above have an independently checked DRAT refutation. The [twelve-edge case archive](three-label-twelve-edge-cases.json.gz) and [verifier](three_label_panels.py) reproduce the entire check. From this directory run

```sh
python three_label_panels.py --genbg /path/to/genbg --drat-trim /path/to/drat-trim --jobs 4
```

**Local theorem.** At any rank, if two distinct oriented norm-18 markings have the same positive root, the same four negative neighbors, and at least three common positive pair labels, their dot product is **eight or ten**. The [rooted distance bound](../short-shell-moments.md#bounding-the-norm-18-alternative) bounds the dot product by ten from above. The lower bound of seven for markings at this root and these parents makes the difference a signed unit vector, because its squared norm is at most 22. The common sites now give a lower bound of eight. At dot product nine, four shared labels were excluded earlier and three shared labels have just been excluded. Equivalently such two markings produce an eigenvector of squared norm twenty or sixteen. Of the original 24 rooted dot-nine panel types, only the six with exactly two shared labels listed in the eleven- and twelve-edge rows above can still occur.

**Global theorem.** At any rank with $N_{16}=N_{20}=0$ one has $N_{18}\le16,166$. At a fixed $o,Q$, the sets $D_t$ for distinct markings now have pairwise intersection at most two. The rooted capacity inequality $8C+2j+3k\le24$ therefore applies to the whole family. Summing over the root and parents and using $P\le851$ gives
$$
9N_{18}\le\frac{24\cdot99\cdot560-16\cdot99\cdot84-3\cdot99\cdot336+78\cdot851}{8}
=\frac{582045}{4}.
$$
Rounding to an even number gives the claim. In the rank-38 two-type alternative the independent [shell identity](higher-moments.md#a-quantitative-target-for-the-remaining-pair) requires $N_{18}\ge16,684$. **Rank 38 therefore needs at least three of the twelve selected unit types**, as does rank 36. This excludes one labeling alternative at rank 38. The other rank-38 populations and the existence problem at all four ranks remain open.

## A rank-36 consequence if norm 18 occurs

Suppose rank 36 has exactly three of the twelve selected unit types and one is norm 18. The other two must be the norm-24 and norm-26 eigenvectors. In that case there are at least **8,408**, **252,210** and **1,389,116** oriented eigenvectors of the respective norms. The first lower bound rounds 8,407 up to an even number.

The [rank-36 checker](rank36_three_types.py) takes the [verified harmonic equations](higher_moments.py), retains the 23 short populations together with $(2,34)$, and eliminates the other columns to obtain nine independent exact equations. Retain just the three candidate unit types together with the unrestricted short populations. Use the same root, mark, norm-16 packing and injection bounds as in the [earlier population argument](exclusion.md#consequences-for-short-labelings). In the absence of norms 16 and 20 also impose $2402V_{0,18}\le16166$. The factor 2,402 converts the normalized population to the number of graph markings at rank 36. Across all $\binom{12}3=220$ triples the [integer certificates](rank36-three-type-duals.json) give $M^ty\ge0>b^ty$ on 210. Among the 55 triples containing norm 18, 54 are excluded. For the remaining pair they give $M^ty\le D c$ and $b^ty=D L$, where $c$ selects a graph marking count, $D>0$ is a denominator and $L$ is its lower bound. Run `python rank36_three_types.py` with python-flint.

More generally, whenever the unit type $(3,37)$ is absent, each unit norm-26 marking has thirteen positives and thirteen negatives and its edges within either sign form a matching. Indeed, orient the marking $b$ so that three sites $i,j,k$ with at least two internal edges are negative. The charge-three vector $b+d_i+d_j+d_k$, where $d_i=3e_i-Ae_i$, has squared norm $65-14e$ for $e$ edges on the three sites. For $e=2$ this is 37, and [every labeling of that charge and norm is a unit labeling](../short-shell-moments.md#when-the-nonzero-labels-must-all-be-signed-units), a type absent by hypothesis. For $e=3$ it is 23, below the minimum 33 imposed by the signed sum. This proves the matching assertion. The endpoints of each same-sign edge have their unique common neighbor on the opposite side. For a negative edge take its triangle $T$. The charge-three translate $b+\sum_{i\in T}d_i$ has squared norm $26+39+14\sum_{i\in T}b_i$. A third site of value zero or $-1$ would again give 37 or 23. Hence every same-sign edge closes a triangle within the 26-site support, and the support contains exactly $2m$ triangles when each sign has $m$ matching edges.

The two matchings have the same number $m$ of edges by counting between the signs. On the 73 exterior vertices let $h$ count contacts with either sign. Summing the incidences with the positives gives $\sum h=130-4m$. Pairs of positives need $156-m$ common-neighbor incidences. Their own side supplies none, and the thirteen negatives supply $78+8m$ using their respective cross degrees four and five. Hence $\sum\binom h2=78-9m$ and
$$\sum_{\rm exterior}(h-1)(h-2)/2=21-5m.$$
All summands are nonnegative integers, so each matching has at most four edges. The count of 1,389,116 is a necessary lower bound for markings of this form. Whether this many can coexist on 99 vertices is open.

This requires at least **694,558 distinct 26-site supports**. Two unit signings $t,u$ on precisely the same sites would make $(t+u)/2$ and $(t-u)/2$ integral eigenvectors with squared norms summing to 26. Unless the signings are equal up to reversal, both are nonzero and each has squared norm at least fourteen. Every one of the required induced graphs has only degrees four and six, with exactly $4m\le16$ vertices of degree six.

The [updated rank-36 population table](population-examples.json) has normalized counts 6, 111 and 590 for these norms and satisfies all the checked harmonic equations and count bounds. The obstacle is simultaneous realization of the supports on the graph.

## All rank-36 alternatives with exactly three selected types

Ten triples survive the population screen. Eight require at least **807,072 unit norm-26 eigenvectors**, hence at least 403,536 distinct 26-site supports with the degree and matching restrictions above. The other two require at least **288,984 unit labelings of charge three and squared norm 37**. In particular none of the ten uses norm 16. The table gives the two companions of the indicated type. A pair $(a,t)$ denotes a unit type at charge $a$ and squared norm $t$. The remaining triples are necessary candidates.

| Required type | Possible companion pairs |
|---|---|
| $(0,26)$ | $(0,18)+(0,24)$, $(0,20)+(0,24)$, $(0,24)+(1,21)$, $(0,24)+(1,27)$, $(0,24)+(2,30)$, $(1,25)+(1,27)$, $(1,25)+(2,30)$, $(2,28)+(2,30)$ |
| $(3,37)$ | $(0,24)+(1,21)$, $(0,24)+(1,27)$ |

The same checker verifies a nonnegative rational solution of the projected system with all three chosen counts positive, and a dual lower bound for each of the ten triples. The smallest values before integer rounding are $807072$ and $6068653/21$ in the two rows. A unit $(3,37)$ labeling has two positive and 35 negative sites, and the two positives cannot be adjacent. If its positives $p,q$ were adjacent, subtracting $d_p+d_q$ would give a charge-one vector of squared norm 21 with entries $-1$ at both $p,q$. The [charge-one classification](../short-shell-moments.md#when-the-nonzero-labels-must-all-be-signed-units) says the negative sites of such a vector are independent.

There are $99(98-14)/2=4,158$ nonadjacent pairs. In either of the two charge-three alternatives, some fixed positive pair must therefore occur in at least $\lceil 288984/4158\rceil=70$ distinct labelings. In the alternative with $(1,27)$ the two common neighbors of that pair must both be negative. Moreover each positive has exactly four zero neighbors, and each of those four is paired with a negative in its neighborhood matching.

To see this, the absence of both the unit norm-26 type and $(1,21)$ rules out *all* norm-26 eigenvectors by the [nonunit count](../short-shell-moments.md#when-the-nonzero-labels-must-all-be-signed-units). For three sites $T$ spanning $e$ edges the charge-zero vector $b-\sum_{i\in T}d_i$ has squared norm $82-14(e+\sum_{i\in T}b_i)$. The two positives and a zero common neighbor give $e+\sum b_i=4$. A triangle of one positive and two zeros also gives four. Both would produce the forbidden norm 26. Finally $Ab=-4b-6\mathbf1$ forces a positive to see ten negatives, leaving four zero neighbors because the positives are nonadjacent.

## Forced overlaps for the remaining two-type alternatives

At ranks 40 and 42 the norm-24 count is substantially larger than the norm-18 count. For any oriented norm-24 marking let $e$ be the number of edges among its twelve positives. The number among its twelve negatives is also $e$. Write $d_i$ for each of the 24 internal same-sign degrees. An exterior site sees $h$ of each sign. Its total over the 75 exterior sites is $120-4e$. Positive pairs need $132-e$ common-neighbor incidences. Internal positives contribute $\sum_{P}\binom{d_i}{2}$ and negatives contribute $\sum_N\binom{4+d_i}{2}$. Subtracting and using $\sum_P d_i=\sum_N d_i=2e$ gives
$$
0\le\sum_{\rm exterior}(h-1)(h-2)/2
=15-3e-\tfrac12\sum_{P\cup N}d_i^2.
$$
Thus $e\le3$, and at $e=3$ both sign sides are matchings.

At a positive root with $k$ same-sign neighbors, the $4+k$ negative neighbors span $b$ disjoint edges in the neighborhood matching. The number of independent $m$-subsets is the coefficient of $z^m$ in $(1+2z)^b(1+z)^{4+k-2b}$. For $0\le k\le3$ and $0\le2b\le4+k$, the [coefficient check](packing.py) gives lower bounds $1+4k-3b$ for $m=4$ and $4+6k-3b$ for $m=3$. The sum of $k$ over the positives is $2e$, and the sum of $b$ is at most $e$ because a negative edge has only one common neighbor. Thus an oriented marking occurs in at least $12+5e$ rooted four-neighbor choices and $48+9e$ rooted three-neighbor choices.

* At rank 40 the two-type hypothesis gives $N_{24}\ge11,100$. Across $99\binom74 2^4=55,440$ independent rooted four-neighbor choices there are at least 133,200 incidences. Some choice contains three different norm-24 markings. For a choice containing $M$ markings use $\binom M2\ge2M-3$. At least **100,080** unordered pair occurrences share a positive root and four specified negative neighbors.
* At rank 42 the same hypothesis gives $N_{24}\ge1,776$. Across $99\binom73 2^3=27,720$ rooted three-neighbor choices there are at least 85,248 incidences. Some choice contains four different norm-24 markings. Using $\binom M2\ge3M-6$ gives at least **89,424** unordered pair occurrences sharing a positive root and three specified negative neighbors.

Here the choice of root and neighbors is counted as part of each occurrence. These bounds give concrete targets for a norm-24 overlap analysis at the two ranks where the two-type alternative survives.
