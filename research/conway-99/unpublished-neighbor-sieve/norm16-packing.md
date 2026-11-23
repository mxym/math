# Packing the eight-positive, eight-negative eigenvectors

Let $N_m$ count the oriented integral $-4$ eigenvectors of squared norm $m$. For a graph with the Conway parameters,
$$7N_{14}+8N_{16}\le55,440.$$
In particular $N_{16}\le6,930$ at all four remaining ranks.

## A difference of squared norm fourteen is impossible

Suppose $t,u$ have squared norm sixteen and $f=t-u$ has squared norm fourteen. By the [short-vector classification](../short-support-packing/README.md), each of $t,u$ has eight positive units and eight negative units, with a 4-regular bipartite graph on the two signs. The sides of $f$ have seven sites each. Any two vertices on one side of $f$ have both common neighbors on the other, so any vertex outside its support sees at most one member of each side.

On the support of $f$ the nonzero entries of $t$ agree with the sign of $f$, and each site is used by exactly one of $t,u$. Off this support the two vectors coincide. Their equal squared norms therefore force each to use seven of the fourteen sites. Let $k$ and $7-k$ be the numbers of positive and negative sites of $f$ used by $t$, respectively. Write $E$ for the number of edges of $t$ joining these selected sets. Of the $4k$ incidences from its selected positives, the $8-(7-k)$ negative sites of $t$ outside $f$ can receive at most one each. Thus $E\ge3k-1$. The other sign gives $E\ge3(7-k)-1$.

At least one side has size at least four, giving $E\ge11$. If the smaller side has size at most two, its four neighbors per vertex give $E\le8$. For side sizes three and four, the three vertices have at most six common-neighbor incidences in total over their three pairs. Eleven edges would distribute at least eleven incidences among the four opposite sites, contributing at least $3\binom32+\binom22=10$ pair incidences. This rules out the difference.

## One vector per four neighbors

Fix a positive site $o$ and its four negative neighbors $Q$. The [rooted four-neighbor argument](../short-support-packing/README.md) proves that a norm-fourteen and a norm-sixteen vector cannot share this data. If two distinct norm-sixteen vectors share it, they have no opposite signs and agree at nine or more nonzero sites, hence their difference has squared norm fourteen. The preceding paragraph excludes this. A norm-fourteen vector, when present, is uniquely recovered by taking common neighbors.

The fourteen neighbors of $o$ form seven disjoint edges. Four neighbors in the independent negative side choose four such edges and one endpoint from each, giving $\binom74 2^4=560$ possibilities. Summing over the 99 choices of $o$ and counting each vector at every positive site proves the inequality.

## Consequence for rank 36

The [rank-dependent affine identity](affine-witness.md) implies
$$N_{24}+16N_{16}+2F_1+F_2\ge235396+7N_{14}+2N_{18}.$$
After eliminating $N_{16}$ with the new packing inequality,
$$N_{24}+2F_1+F_2\ge124516+21N_{14}+2N_{18}.$$
In particular there must be at least 62,258 distinct signed labelings among the three indicated types on the fixed vertices of any rank-36 graph.

The same lower bound counts distinct vertex subsets after forgetting the signs. For norm 24 the half-sum and half-difference of two labelings on the same support are integral eigenvectors, and their squared norms add to 24. The minimum fourteen forces the two labelings to agree up to sign. For either affine type, two labelings on the same support differ by twice an integral eigenvector. Its squared norm is twice the number of positives lost by one labeling, hence at most six for the three-positive type and at most fourteen for the seven-positive type. In the latter case equality forces two disjoint positive seven-sets forming the two sides of a Fano eigenvector. Each of the eleven remaining marked sites is negative in both labelings and sees at least two positives in each, contradicting saturation of each Fano side. Thus the three support counts are exactly $N_{24}/2,F_1,F_2$. They are disjoint because the sizes are 24, 25 and 28.

## A bound on the overlap of two norm-sixteen vectors

Let $P_t,N_t$ and $P_u,N_u$ be the positive and negative sets of two norm-sixteen vectors. Put $c=|N_t\cap N_u|$ and $d=|P_t\cap P_u|$. On every vertex $x$ let $h_x$ count its neighbors in the common negative set. Because that set is independent, $\sum_x h_x(h_x-1)=2c(c-1)$. Also $\sum_{P_t}h_x=\sum_{P_u}h_x=4c$. For each integer $k\ge1$, use
$$h(h-1)\ge 2kh-k(k+1)$$
on the $16-2d$ vertices of the positive symmetric difference and use the same inequality with $2k$ on the $d$ common positives. Dropping the nonnegative terms elsewhere gives
$$k^2 d\ge 8k(c-k-1)-c(c-1).$$
This holds with $c,d$ exchanged and also after reversing either vector. In particular $c=4,5,6,7,8$ requires $d\ge4,4,5,6,6$, respectively, by taking $k=1$ or $2$.

Distinct norm-sixteen vectors have dot product at most eight, since their difference has squared norm at least fourteen and the first section excludes fourteen. If their dot product is at least four, their difference has squared norm at most 24. Every integral eigenvector of squared norm at most 24 has entries in $\{0,\pm1\}$, by the [charge-one bound](affine-witness.md). Indeed if a site has magnitude at least two, orient its entry to be negative, then add $d_i$ to obtain charge one and squared norm at most $24+23-28=19$. Thus the original vectors have no opposite signs, and their dot product is $c+d$. If either $c$ or $d$ is at least four, the overlap inequality and $c+d\le8$ force $(c,d)=(4,4)$. In particular **dot product seven is impossible at all ranks**.

## A sharper packing at rank 42

At rank 42, for any two distinct norm-sixteen vectors one has $t\cdot u\le5$. To see this, their classes in the [anisotropic discriminant plane](../maximal-marked-lattice/README.md) have square two for the bilinear form induced by $t\cdot u\bmod7$. Indeed the evaluations of $y\in L^*$ have dot products $7(y,y')$ by tightness, and every integral eigenvector gives such a $y$ as in the [affine dictionary](affine-witness.md). In an orthogonal basis with first vector the class of $t$, the form has diagonal $(2,2)$ after rescaling the second basis vector. This follows since $-1$ is nonsquare in $\mathbb F_7$ and the plane is anisotropic. Writing the second class with coordinates $(a,b)$ gives $a^2+b^2=1$. The possible residues $2a$ of the dot product are $0,\pm2,\pm3$. This excludes six and eight, while seven was excluded above. Furthermore, a dot product of five makes the two classes negatives of each other, since the square of their sum is zero.

Fix a positive root $o$ and three negative neighbors $a,b,c$. Their three pairs have distinct second common neighbors beyond $o$. In any vector using this rooted triple let $z$ count those three second common neighbors that are positive. In the remaining seven positive sites there are nine incidences with the triple. No site can meet all three, since it would share three neighbors with $o$. Thus $z=2$ or $3$, with exactly $z-2$ of the seven positives missing the entire triple. Call the triple good for the vector when $z=3$.

For two vectors $t,u$ using this rooted triple, at least $1+z_t+z_u-3$ positive sites and three negative sites agree. A positive site in one vector that is negative in the other misses all three negatives by independence. There are therefore at most $(z_t-2)+(z_u-2)$ opposite sites. The dot product is at least five, so the preceding argument rules out opposite signs entirely. If either triple is good, there are at least six matching sites, exceeding the rank-42 upper bound five. Otherwise any two distinct vectors have dot product five. Three such vectors cannot use the same triple, as their nonzero classes would have to be pairwise opposite.

A Fano vector excludes all norm-sixteen vectors at its rooted triples at rank 42. Every Fano class has square zero, so vanishes in the anisotropic plane. Its dot product with a norm-sixteen vector is divisible by seven. In fact its absolute dot product with any norm-sixteen vector at any rank is at most six. Orient the Fano vector $f$ to make the dot product nonnegative. The minimum eigenvector norm gives $f\cdot t\le8$. Equality eight would make $g=t-f$ another Fano vector with $g\cdot f=-6$, whereas distinct nonopposite Fano vectors have absolute dot product at most four by three-site closure. Equality seven would make $t-f$ a second norm-sixteen vector with Fano difference. Hence $f\cdot t=0$ at rank 42. If they shared a rooted triple, all six other Fano positives would touch its negatives. Indeed the three pairs give three double incidences, there are nine incidences and only six other positives. At most one of the seven other norm-sixteen positives misses the triple. There are at least six matching sites and at most one opposite sign, contradicting orthogonality. Two Fano vectors sharing a triple coincide by closure.

There are $99\binom73 2^3=27,720$ rooted triples. A Fano vector uses 28 such triples. For norm sixteen count a good triple with weight one and each other triple with weight one half. At each rooted triple the total weight over both types is at most one. At each positive site of a norm-sixteen vector at least two of the four triples are good, because at most one of the six pair labels among its four neighbors is missing. Its eight positive sites therefore use total weight at least 24. Consequently
$$28N_{14}+24N_{16}\le27,720 \quad (r=42).$$
In particular $N_{16}\le1,154$ by evenness. Run `python3 norm16_packing.py` to replay the finite arithmetic checks for both packing arguments.

[The zero-star forest and shore multigraphs](n16-zero-star-forest.md) refine this count by measuring actual double-edge components. The forest/shore theorem holds independently of the Seidel rank.
