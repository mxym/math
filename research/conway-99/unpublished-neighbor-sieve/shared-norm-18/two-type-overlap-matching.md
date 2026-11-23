# Eight pairs of intersecting norm-18 supports in the two-type case

Suppose the only present types among the twelve selected unit types are neutral norms 18 and 24. This is the [remaining two-type case](higher-moments.md) at Seidel ranks 40 and 42. In **each** maximal determinant-49 extension there are eight pairs of norm-18 supports such that all sixteen supports are distinct. Within each pair exactly six or seven graph vertices are common, and the labels can be oriented to agree at every common vertex. The pairs may use some of the same graph vertices. The conclusion holds regardless of graph symmetry.

## At least seventeen vectors in each signed residue class

Fix an extension and its anisotropic discriminant plane over the field of seven elements. On graph labels the plane norm is $q=t-11a^2/9$ modulo seven. For neutral labels the plane pairing is their ordinary integral dot product reduced modulo seven, by tightness of the graph frame. Choose any plane element $g$ of norm $18\equiv4$. For a charge $a$, squared norm $t$, and residue $i$, let $K(a,t,i)$ count all eligible labels whose class pairs with $g$ to $i$. These are actual counts, before any division by eight. For neutral labels $K(0,t,i)=K(0,t,-i)$. Use $W$ for the usual raw folded shell counts in this fixed extension.

There is just one class of norm 4 with pairing 4 against $g$, namely $g$. In coordinates with $g=(1,0)$ the plane has form $4I$: the perpendicular coefficient is a nonzero square by anisotropy and can be scaled to 4. Put $n_g=K(0,18,4)$. On the two-type face the following identity holds:
$$
\begin{aligned}
72 n_g={}&792+4W_{1,23}+20K(0,14,0)+12K(0,22,3)+K(1,29,1)\\
         &+22K(2,22,0)+12K(3,33,0)+12K(3,35,1).
\end{aligned}
$$
The 99 ordinary site marks occur in $W_{1,23}$. Consequently $n_g\ge(792+4\cdot99)/72=16.5$, hence **$n_g\ge17$**. The bound applies to each of the eight classes separately, including before we know which are represented.

Here is the derivation of the rows used in the [exact identity checker](two_type_overlap_matching.py). Start with the [four rank-48 gluings and their shell-two/shell-four quadratic harmonic identity](../short-shell-moments.md#the-second-moment-equations). Retain the class of $g$ while gluing. If a shift has scale $s=1$ or $3$, the auxiliary projection has pairing coordinates $w/s$. Let $B$ be the auxiliary Gram matrix. Fix the image of $g$ under the anti-isometry to be a class with pairing numerator $c$ of norm $-4$. Thus a compatible graph label must have
$$i=-c^t(7B^{-1})w/s\pmod 7.$$
If $m$ plane classes have norm $q$ and this pairing, their contribution per fixed auxiliary numerator is $K(a,t,i)/m$. Indeed in $4I$ coordinates the pairing fixes the first coordinate, and reflection of the second interchanges the two solutions when there are two. The stabilizer of $g$ acts transitively on either a singleton or this pair. The checker enumerates all eight images using $c=(j,0,k,0)$ with $4(j^2+k^2)=-4$ modulo seven. These numerators represent different classes because the first coordinate generator in each binary Gram summand has order seven.

For an auxiliary axis $3h$, a norm-$2l$ vector contributes the harmonic value $48(3w^th/s)^2-2l(9h^tBh)$. The sum for $l=2$ plus 48 times the sum for $l=1$ is zero. Add these rows for the three listed axes, every image and every gluing. Count both signs for positive charge and all numerators for charge zero. The checker also adds the [ordinary folded moment rows](higher_moments.py), undoing their four raw-to-unit substitutions before imposing the two-type assumption. In particular raw $(1,27)$ retains its $9W_{0,18}$ contribution. It verifies the displayed integer identity by appending it to the rational row space with its constant included.

## An affine dimension bound

Take one representative of each antipodal vector pair by selecting one of the two opposite residue classes in each of the four norm-4 directions. There are at least $194$ such vectors: the [two-type identity](higher-moments.md) gives $6W_{0,18}=93+2W_{0,14}+2W_{1,23}+5W_{2,22}\ge291$, and the unfolded number of antipodal pairs is $4W_{0,18}$. Each direction contributes at least 17.

Within one signed class the dot product of distinct vectors is $-3$ or 4. It is 4 modulo seven. Its absolute value is at most 10 by the [norm-18 distance bound](../short-shell-moments.md#bounding-the-norm-18-alternative), including after changing the sign of one vector. Absolute values 10 and 8 would respectively give a difference or sum of norm 16 or 20, both absent.

For $n$ vectors in one class their affine span has dimension at least
$$ d(n)=\left\lceil \frac{24(n-1)}{n+24}\right\rceil .$$
Let $G$ be their Gram matrix, $P=I-J/n$, and $u=\mathbf1^tG\mathbf1/n^2$. Each off-diagonal entry satisfies $g^2=g+12$. Thus $\operatorname{tr}(G^2)=294n+(12+u)n^2$. For the centered Gram matrix $C=PGP$ one has $\operatorname{tr} C=n(18-u)$ and
$$\operatorname{tr}(C^2)\le 294n+(12+u-u^2)n^2.$$
The latter follows by expanding and using $\|G\mathbf1\|^2\ge(\mathbf1^tG\mathbf1)^2/n$. Apply the trace-rank inequality and use
$$
(n+24)(18-u)^2-24(n-1)(12+294/n+u-u^2)=(5un-6n-84)^2/n.
$$

## Why a matching of size eight is necessary

Join two representatives whose dot product has absolute value 6 or 7. If a maximal matching had at most seven edges, deleting its endpoints would remove at most fourteen representatives and leave an edgeless family. All four classes would survive. The residue directions can be taken as $(1,0),(0,1),(2,2),(2,-2)$ in $4I$ coordinates. Between different directions the pairing is $0,1$ or $-1$ modulo seven. The dot bound and the absence of absolute values 6, 7 and 8 now force each cross-class dot to equal that residue's representative in $\{0,1,-1\}$. It is constant on the whole pair of classes.

The four spaces spanned by within-class differences are therefore mutually orthogonal. In the complement of their direct sum, the projections of the four classes still have the same cross-class inner products: each vector is orthogonal to all differences from the other three classes. Two perpendicular directions give nonzero orthogonal projections, since each has nonzero pairing with a third direction. The complement has dimension at least two.

At least $180$ representatives survive. Trim the larger classes to reach $180$, preserving $\sum_j(17-n_j)_+\le14$. This is possible because deleting from a class above 17 leaves the deficit unchanged. Each class still contains at least three vectors. Over the four sorted integer sizes with these bounds, the least $\sum_j d(n_j)$ is 43. The checker tests every such quadruple; $(3,17,17,143)$ attains the arithmetic minimum. Thus the assumed edgeless family would require at least $43+2=45$ dimensions in the 44-dimensional graph eigenspace.

The matching supplies the eight asserted pairs. Orient each to positive dot. Their difference has squared norm 24 or 22 and every entry has absolute value at most one by the [charge-one site switch](rank36-four-types.md#two-fano-supports-on-the-same-square-force-norm-20). The two markings therefore have no opposite signs at a common site and share exactly six or seven vertices. Each support determines its line because its [bipartite support graph is connected](../../short-support-packing/README.md). Run `python3 two_type_overlap_matching.py` with python-flint to verify the residue identity and the dimension minimum. The realizability of these matched configurations remains open.
