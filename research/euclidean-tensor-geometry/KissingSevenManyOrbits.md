# A seven-dimensional kissing bound without point transitivity

**Theorem.** Let $C\subset S^6$ have pairwise scalar products at most $1/2$. Suppose a finite group $G\le O(7)$ preserves $C$ and satisfies **either** condition:

1. its representation on $\mathbb C^7$ is irreducible and primitive; or
2. its representation on $\mathbb R^7$ is irreducible and $9\mid |G|$.

Then $|C|\le126$. Equality holds precisely for an orthogonal copy of the normalized $E_7$ roots among codes in this class. There is **no requirement that the points be one orbit**; in particular they need not have identical neighborhoods or lie in a prescribed lattice. Here primitive refers to the linear representation: there is no nontrivial direct-sum decomposition into blocks permuted by the group.

A hypothetical code with more than 126 points must therefore have reducible symmetry, or have imprimitive irreducible symmetry of order not divisible by nine. This does not determine the unrestricted number. The [point-transitive theorem](KissingSevenVertexTransitive.md) treats a different condition; its [equality proof](KissingSevenTransitiveUniqueness.md) supplies a Sylow lemma used below.

Throughout, [Tomar's rational upper bound](https://www.mefyi.com/papers/kissing-numbers-five-seven/kissing-numbers-five-seven.pdf) gives $|C|\le132$. If $C$ is antipodal the result follows from [Anstreicher, §4, Theorem 7](https://optimization-online.org/wp-content/uploads/2001/01/248.pdf); if $-I\in G$ we may therefore stop. Applications of tables below concern stabilizers of **individual points**, not presumed stabilizers of the whole code.

## The group reduction

An irreducible real representation of odd dimension is absolutely irreducible. An imprimitive seven-dimensional complex representation has seven line blocks. As shown in the [finite-orbit lemma](KissingSevenTransitiveUniqueness.md), the kernel $B$ of permutation of these lines is a 2-group; if it is nonscalar, its weight spaces are seven distinct real orthogonal lines and it acts by sign changes. In case 2 the permutation image contains $A_7$ (prime degree and a 3-cycle). The same lemma excludes a trivial kernel: a representation induced from a linear character of $A_6$ or $S_6$ in $A_7$ or $S_7$ is reducible. A nontrivial scalar kernel contains $-I$.

In the remaining imprimitive case, $B$ contains every even sign change: choose any nonconstant binary sign vector of $B$ and a 3-cycle moving two equal entries and one different entry. Adding its permuted vector over $\mathbb F_2$ produces a weight-two vector. The $A_7$ conjugates generate the even subspace. For a point of support $k\le6$, its orbit has at least $2^k\binom7k$ points (all signs on its support, and all supports occur). Thus $k=1$ or $2$. At $k=2$ unequal magnitudes already give at least 168 points by interchanging the two coordinates, so the orbit must be all 84 normalized $D_7$ roots. At full support the orbit contains at least 64 points for every magnitude pattern. A nonconstant pattern has at least seven coordinate permutations under $A_7$, so all magnitudes equal $1/\sqrt7$. Both parity halves together are impossible (one-sign neighbors have scalar product $5/7$). The 14 axes cannot coexist with the $D_7$ roots, and neither can a parity half since $2/\sqrt{14}>1/2$. The total is at most $\max(84,14+64)=84$ here.

For a primitive group, the determinant twist embeds $G$ in $SO(7)$ when $-I\notin G$. The center of the image is trivial, and its Sylow 7-subgroups are abelian, as proved in the [same lemma](KissingSevenTransitiveUniqueness.md). [Wales, Theorem I](https://msp.org/pjm/1970/34-1/pjm-v34-n1-p21-p.pdf) leaves the normal simple groups
\[
 \mathrm{PSL}_2(13),\quad \mathrm{PSL}_2(8),\quad A_8,\quad
 \mathrm{PSL}_2(7),\quad \mathrm{PSU}_3(3),\quad \mathrm{Sp}_6(2).
\]
The possible extensions are respectively none, by three, by two, by two, by two, and none. We analyze the simple subgroup in the **original** action, not a determinant-twisted orbit. Its complex restriction is irreducible: the number of isotypic components divides both the extension index and seven, and a homogeneous restriction of prime total dimension cannot have multiplicity seven for a faithful simple nonabelian subgroup. Passing to a subgroup can split any number of point orbits, which the following counts allow.

## The groups over fields of order 8 and 13

For $S=\mathrm{PSL}_2(8)$ the [maximal subgroup orders](https://www.math.rwth-aachen.de/~Thomas.Breuer/ctbllib/ctbltoc/data/L2%288%29.html) are 56, 18 and 14: a Borel $2^3:7$ and two dihedral torus normalizers. The normal elementary group in the Borel has all seven nontrivial characters, each once, in a faithful seven-dimensional representation, because a cyclic complement permutes them transitively. Hence involutions have trace $-1$, and nonidentity elements of the split torus $T_7$ have trace zero (they cycle the weight lines).

Both $T_7$ and a nonsplit torus $T_9$ have a one-dimensional fixed space. For $T_7$ this follows by averaging. For $T_9$, there are 63 nonidentity unipotents, 36 split tori, and 28 nonsplit tori. The last two numbers count unordered pairs of distinct rational eigenlines and conjugate pairs of nonrational eigenlines on the projective line; a nonidentity semisimple element has a unique eigenline pair. Character orthogonality gives
\[
 504=49+63+28\sum_{1\ne t\in T_9}|\chi(t)|^2 .
\]
The squared norm of the restricted character on $T_9$ is therefore $(49+14)/9=7$. Its nine character multiplicities sum to seven, so each is zero or one. Nontrivial characters occur in conjugate pairs, giving exactly one fixed dimension. For either torus an inverting involution has trace zero on the nontrivial weight pairs, hence acts by $-1$ on the fixed line. Neither dihedral normalizer fixes a unit vector, and any point fixed by either full torus has its negative in its $S$-orbit.

An orbit of at most 132 points has stabilizer of order at least four. Inside the Borel an order divisible by seven forces the intersection with $2^3$ to be invariant under the irreducible order-seven multiplier, so the candidate orders are $4,7,8,56$. An order-eight or order-56 subgroup here fixes no point. In the two dihedral groups the candidate orders are $4$ or greater divisors of 18 or 14, namely $6,9,18$ or $7,14$; the full normalizers fix no point. Consequently the only possible orbit sizes are $56,72,84,126$, and the first two sizes come from torus-fixed points and are antipodal. The only sum in $127,\ldots,132$ is $56+72=128$, impossible since their union is antipodal. At 126 there is only a single orbit, already classified. This handles the degree-three extension and also $\mathrm{Sp}_6(2)$: the latter contains $\mathrm{SL}_2(8)$ on $\mathbb F_8^2$ preserving the field trace of the determinant.

For $\mathrm{PSL}_2(13)$ the [maxima](https://www.math.rwth-aachen.de/~Thomas.Breuer/ctbllib/ctbltoc/data/L2%2813%29.html) have orders $78,14,12,12$. A point stabilizer in the Borel $13:6$ of index at most 132 in the whole group contains $C_{13}$; otherwise it has order at most six. The order-six multiplier has two free orbits on the nontrivial characters of $C_{13}$, hence the faithful seven-dimensional representation has exactly one trivial weight and one six-element orbit. All points of this kind lie on the 14 Sylow fixed lines and contribute at most 28. Any other point stabilizer must equal a whole maximal subgroup of order 14 or 12 (twice either index exceeds 132). At most one such orbit fits, giving the stronger bound $28+91=119$.

## The unitary and alternating groups

For $\mathrm{PSU}_3(3)$ the [maximal subgroup indices](https://www.math.rwth-aachen.de/~Thomas.Breuer/ctbllib/ctbltoc/data/U3%283%29.html) are $28,36,63,63$. The [degree-28 coset character](https://brauer.maths.qmul.ac.uk/Atlas/v3/permrep/U33G1-p28B0) is $1+27$, while the [degree-36 character](https://brauer.maths.qmul.ac.uk/Atlas/v3/permrep/U33G1-p36B0) has constituents $1,7b,7c,21a$; neither contains the real seven-dimensional representation $7a$. Thus the corresponding maximal subgroups do not fix a point, by Frobenius reciprocity. The index-36 maximal subgroup is simple of order 168, so has no subgroups of index two or three. An orbit of odd size 63 is ruled out by the Sylow lemma. The only sizes still possible below 133 are $56,84,112,126$; none combine to give an order above 126, and at 126 only a single orbit is possible. The extension by two preserves this conclusion.

The real seven-dimensional representation of $A_8$ is the deleted natural permutation representation in $\sum x_i=0$. For completeness, the hook formula gives only the mutually conjugate partitions $(7,1),(2,1^6)$ of degree seven for $S_8$, and no self-conjugate partition of degree 14 that could split into two sevens on restriction. For a repeated-coordinate vector every odd permutation can be corrected with a transposition of equal entries, so the $A_8$ orbit equals its entire coordinate-permutation orbit. All-distinct vectors already have $8!/2$ images. By the multinomial formula the only nonzero unit-vector orbit sizes at most 132 are:

| Size | Coordinate multiplicities | Number of possible orbits when finite |
|---:|---|---:|
| 8 | $7+1$ | 2 (opposite simplices) |
| 28 | $6+2$ | 2 |
| 56 | $5+3$ or $6+1+1$ | two of the first type, continuously many candidate seeds of the second |
| 70 | $4+4$ | 1 (balanced sign vectors divided by $\sqrt8$) |

Within $126,\ldots,132$, only 126 and 128 can be sums respecting these counts. At 128 both simplices occur, so every point satisfies $|x_i|\le\sqrt{7/32}$. A centered normalized two-subset vector (size 28) has an entry $\sqrt{3/8}$ and is excluded. For type $6+1+1$ write its entries as $c$ six times, $a,b$ once each. Then $c=-(a+b)/6$ and its norm squared is at most $(2+4/6)7/32=7/12$, impossible. This leaves the two opposite centered three-subset orbits. For disjoint three-subsets the scalar product of their centered normalized indicators is $-3/5$, so these two orbits cannot coexist.

At 126 the only sums are $70+56$ and $70+28+28$. The 70 balanced sign vectors clash with a two-subset or a three-subset (choose its support among the four plus signs; the scalar products are $1/\sqrt3$ and $3/\sqrt{15}$). For the remaining type $6+1+1$, put $\alpha=a-c,\ \beta=b-c$. Taking the two exceptional signs as desired gives $|\alpha|+|\beta|\le\sqrt2$. Interchanging either exceptional coordinate with an ordinary one (and two equal ordinary coordinates to make the permutation even) gives $|\alpha|,|\beta|\ge1/\sqrt2$. Thus they are opposite, since $a\ne b$, and $c=0$. The 56 points are exactly $(e_i-e_j)/\sqrt2$. These and the balanced 70 give the standard $E_7$ roots in the sum-zero model. The result also applies to $S_8$.

## The projective line on eight points

Let $S=\mathrm{PSL}_2(7)$ act on $\mathbb P^1(\mathbb F_7)$, relabeling infinity as 7. Its only seven-dimensional complex irreducible representation is the sum-zero part of this doubly transitive action; the character degrees are $1,3,3,6,7,8$ ([ATLAS, printed p. 3](https://gaetan.chenevier.perso.math.cnrs.fr/ALG1/ATLAS.pdf)). Work in this real coordinate model. In fact $S$ itself is linearly imprimitive: its index-seven subgroup $S_4$ has a sign character, and the induced degree-seven character is irreducible (it has no trivial summand and cannot otherwise split with those degrees). For the primitive equality case it is therefore enough to handle $\mathrm{PGL}_2(7)$. Any extension of the standard action on the same space differs from the usual one by at most a linear sign, by Schur's lemma. The upper bound below works already for $S$.

The [maximal subgroup orders](https://www.math.rwth-aachen.de/~Thomas.Breuer/ctbllib/ctbltoc/data/L3%282%29.html) are 24, 24, 21. The split torus of order three has two fixed coordinates and two triples; a nontrivial involution has four transpositions. All elements of order four have two 4-cycles. These cycle types follow directly from the projective action. A Sylow 2-subgroup acts regularly on eight coordinates (point stabilizers have odd order 21), so has no fixed sum-zero vector. A subgroup of order 14 cannot occur: it would be contained in the normalizer of its normal Sylow 7-subgroup, which has order 21. Order-seven fixed points have shape $7+1$, with actual stabilizer 21. The remaining stabilizers of order at least two give the following complete list of potential orbits of size at most 132:

| Orbit | Geometry needed here |
|---:|---|
| 8 | the two opposite regular simplices (at most one of each) |
| 14 or 42 | balanced four-subset vectors: an order-four subgroup is cyclic or is a four-group acting freely, in both cases with two 4-orbits |
| 28 | centered normalized two-subset, with either orientation |
| 56 | fixed by an order-three group: entries of multiplicities $1,1,3,3$, allowing equal values |
| 84 | fixed by an involution: entries on four two-element blocks |

For 28 the stabilizer of order six is $S_3$ (there is no element of order six), normalizing the two fixed coordinates of its $C_3$. It interchanges these two coordinates, and is transitive on the other six: a residual 3-orbit for $S_3$ would have fixed points of involutions. For 14 and 42, enumerating the 70 four-subsets under the 168 fractional linear transformations gives three orbits of sizes $42,14,14$, each closed under complement. This enumeration is reproduced in the checker.

Except for the at most two 8-orbits all sizes are divisible by 14. In $127,\ldots,132$ only 128 is arithmetically possible, requiring both simplices (and hence the coordinate bound above). This immediately excludes every 28-orbit. The following three finite cone checks are detailed below, using the complete continuous families of representatives, not a list of sample points:

- No 84-orbit is compatible with both simplices.
- No 56-orbit together with both simplices can coexist with any of the three balanced orbits.
- Two 56-orbits cannot coexist with both simplices.

At most 70 balanced vectors are available, and the required remainder after both simplices is 112. The checks exclude all possibilities for that remainder.

For equality in the primitive extension, both 14-orbits occur together or neither does: the outer projective map $x\mapsto3x$ exchanges them and preserves the 42-orbit, as direct enumeration confirms. A possible additional linear sign does not affect the balanced orbits. At size 126 there is no 8-orbit, and some balanced orbit must occur since 28, 56 and 84 are divisible by 28. No 28-orbit can coexist with one: transitivity on two-subsets provides an aligned pair inside a four-subset. The sum 126 now leaves only $42+84$ or $70+56$ (including both or neither of the 14-orbits). The checker excludes an 84-orbit with the 42-orbit, even without either simplex.

In the $70+56$ case choose the $C_3$-fixed representative with entries $a=p-3t$, $b=-p-3t$, $c=t+s$ three times, $d=t-s$ three times. Use arbitrary nonzero scale, so its squared norm is $Q=2p^2+24t^2+6s^2$. The largest projection onto the balanced signs is at least $2(|p|+3|s|)/\sqrt8$ before normalization (take a singleton and one triple; both complements are available). The kissing constraint thus gives $|p||s|+s^2\le 2t^2$.

In the cone $|p|>4|t|,\ 2|p|>|s|$, compare the vector first at $s=0$ with a permutation fixing the first singleton and moving the second, then with one fixing the second and moving the first. Such permutations exist by double transitivity; they lie outside the exact stabilizer $C_3$. The shorter of the two distances at $s=0$ is $\sqrt2(|p|-4|t|)$. Restoring $s$ changes each vector by at most $\sqrt6|s|$. The required distance is at least $\sqrt Q\ge\sqrt2|p|$, so $t^2\le3s^2/4$. Together these inequalities force $s=t=0$. Outside this cone the last exact single-representative check excludes all candidates. Hence the 56 vectors are again $(e_i-e_j)/\sqrt2$, and the equality configuration is $E_7$.

Finally $E_7$ attains the bound already under the irreducible $A_8$ symmetry just described, and its full Weyl action is primitive (equivalently its index-two rotation group is the primitive seven-dimensional symplectic-group representation; one can also verify this as below). To see primitivity directly, any seven-line block system would give a homomorphism from the nonabelian simple $\mathrm{Sp}_6(2)$ to $S_7$. Its order $1{,}451{,}520$ exceeds $7!$, so the map would be trivial. This contradicts irreducibility, which already follows from the contained $A_8$. We use the classical identification $W(E_7)/\{\pm I\}\cong\mathrm{Sp}_6(2)$, realized by the determinant-one subgroup in this odd dimension.

## Exact verification of the continuous projective-line cases

The [standard-library verifier](verify-kissing-seven-many-orbits.py) generates the 168 transformations $z\mapsto(az+b)/(cz+d)$ over $\mathbb F_7$ with $ad-bc=1$, identifying duplicate permutations. For each stabilizer order $k=2,3$ it takes one cyclic subgroup $H$; all subgroups of that order in $S$ are conjugate. Representatives of different point orbits may independently be chosen fixed by this same $H$. For its four coordinate blocks of sizes $m_0,m_1,m_2,m_3$, put the value $m_3z_i$ on block $i<3$, and $-\sum_{i<3}m_i z_i$ on block 3. This gives an injective matrix $W:\mathbb R^3\to\mathbb R^8$ onto the required sum-zero fixed space. All inequalities are homogeneous, so the six faces $\max_i|z_i|=1$ cover all normalized representatives.

Write $D_g=W^TgW$, $S_0=W^TW$, and $x=Wz$. The candidate's within-orbit constraints are the homogeneous quadratic inequalities
\[
 z^T(D_g+D_g^T-S_0)z\le0\quad(g\notin H).
\]
They are necessary for an orbit whose stabilizer is exactly $H$; points with larger stabilizer were counted separately. For the two simplex constraints add $32x_i^2-7\|x\|^2\le0$. For a balanced sign vector $b/\sqrt8$ in a prescribed balanced orbit, add $(b^Tx)^2-2\|x\|^2\le0$; its negative is in the same orbit, so squaring is valid. For two 56-orbits the inter-orbit inequalities are $2z^TD_gw\le\sqrt{(z^TS_0z)(w^TS_0w)}$ for every $g\in S$. The checker retains the sign of the left side before squaring. Simultaneously negating both representatives is harmless when both simplices are present.

Each face is covered by a closed square and split into four dyadic children. Boxes are excluded only when one necessary inequality fails **strictly everywhere**, or in the last equality test when the entire box lies in the analytically classified cone. The cone test checks the four vertices against its linear halfspaces, with a single sign for $p$ throughout a given box.

Two exact integer enclosures can be selected:

- **Center method:** expand the bilinear form about the two box centers. Bound each nonconstant term in absolute value by its coefficient times the product of the respective half-widths. Quadratic forms are evaluated with both arguments in the same box.
- **Vertex method:** separately interpolate each argument. The minimum of the bilinear form on the product of the two boxes occurs at a pair of vertices, so the smallest of 16 integer evaluations is a valid lower bound. The maximum of either squared norm is attained at a vertex by convexity.

The pair test first discards impossible single boxes at depth three, then bisects the product by subdividing one entire factor at a time. All tests terminate with zero unclassified boxes (the cone handled analytically counts as classified).

| Test | Center nodes | Vertex nodes |
|---|---:|---:|
| 84 with both simplices | 350 | 302 |
| 56 with both simplices and the 42-orbit | 134 | 78 |
| 56 with both simplices and the first 14-orbit | 222 | 198 |
| 56 with both simplices and the second 14-orbit | 222 | 198 |
| 84 with the 42-orbit alone | 158 | 142 |
| 56 with all 70 balanced signs, outside the classified cone | 222 | 158 |
| Pair of 56-orbits with both simplices, after single prefilter | 8,224 | 6,448 |

**Replay:** run `python3 verify-kissing-seven-many-orbits.py` and `python3 verify-kissing-seven-many-orbits.py --vertices`. The finite-group classifications, the earlier Sylow lemma, and the cited unrestricted and antipodal bounds are theoretical inputs; the script does not purport to verify them.
