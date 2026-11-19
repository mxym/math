# Every 1324-maximizing permuton is layered

**Theorem.** Every permuton maximizing the density of the classical pattern 1324 is layered. Consequently the unique layered maximizer of [the preceding Bellman theorem](../packing-density-1324/PROOF.md) is the **unique maximizing permuton without restrictions**. Every sequence of near-optimal permutations whose orders tend to infinity converges to it as a permuton. At finite orders $n\ge4$, every exactly optimal permutation is layered; this last assertion does not specify its layer sizes or imply a unique finite maximizer.

The limiting statement does not follow just from the finite assertion: near-optimal permutations can be nonlayered. We prove it directly. Throughout, write $x<y$ for strict increase in both coordinates of points of the square; $x\parallel y$ means that neither precedes the other. Coordinate ties have probability zero for independent permuton samples. The pattern 1324 is exactly the four-point *diamond* in this order (a unique bottom, a unique top, two incomparable middle points). In particular this uses an induced order, not the undirected four-vertex graph with one missing edge.

## 1. Testing an extremal measure by adding incomparable copies

Let $\mu$ be any maximizing permuton, and $p$ its 1324 density. We have $p>0$, e.g. from positive masses on the three layers of type $[1,2,1]$ in the sense of one bottom layer, one middle layer and one top layer. Define $h(x)$ as the probability of a diamond with a prescribed point $x$ and three independent $\mu$ points; $F(x,y)$ denotes the analogous probability with two prescribed roots and two fresh points. If the prescribed roots are two distinct incomparable *copies* of the same point $x$, write $c(x)$ for this probability. Write $D(x)=\{u:u<x\}$ and $U(x)=\{v:x<v\}$. Because two incomparable roots have to be the middle points of the diamond,
\[
 c(x)=2\mu D(x)\mu U(x),\qquad F(x,y)=2\mu(D(x)\cap D(y))\mu(U(x)\cap U(y))\quad(x\parallel y).
 \tag{1}
\]
These formulas keep the two orders of the fresh points. Ordinary distinct roots are considered only off null sets of coordinate ties.

Here are details for the admissibility of the variation. Let $B$ be measurable with $\mu(B)>0$, $\nu_B=\mu|_B/\mu(B)$, and fix $x$. Replace the sampling law by the unchanged geometric point law of total mass $1-\epsilon$ given by $\mu-\epsilon\nu_B$, together with an extra mass $\epsilon$ at $x$, for $0\le\epsilon\le\mu(B)$. A draw at $x$ is a new copy, with an independent uniform tie key $s$; order such copies by $s$ in the first coordinate and by $1-s$ in the second. All other relative orders are unchanged: both marginals of $\mu-\epsilon\nu_B$ are atomless, so even ties in a single coordinate with $x$ have probability zero. Each finite iid sample, ranked by the resulting two total orders, is a permutation almost surely. Thus its expected fraction of 1324-copies is the 4-sample diamond probability. This is bounded by the unrestricted best density at each sample order $N\ge4$, so also by its limit $p$. The construction does not require that the perturbed geometric law retain uniform marginals in its original coordinates.

Equivalently, use the symmetric four-sample indicator on the disjoint union of the ordinary square and the copy fiber with its uniform tie key. Holding all ordering rules fixed on that union, the density is a polynomial of degree at most four in $\epsilon$ by multilinearity. Taking $B$ to be the whole space, its first derivative at zero is $4(h(x)-p)\le0$. As $\int h\,d\mu=p$, it follows that $h(x)=p$ for $\mu$-almost every $x$. In particular, for any such $x$ and any $B$ of positive mass the first derivative $4(h(x)-\int h\,d\nu_B)$ of the general variation vanishes. Its coefficient of $\epsilon^2$ must then be nonpositive:
\[
 c(x)-2\int F(x,y)\,d\nu_B(y)+F_{BB}\le0,
 \quad F_{AB}=\iint F(x,y)\,d\nu_A(x)d\nu_B(y).
 \tag{2}
\]
(The omitted positive binomial factor is 6.) Integrating in $x$ first over $B$ gives $\int c\,d\nu_B\le F_{BB}$. Integrating (2) over $A$ and substituting that lower bound gives the key inequality
\[
 \int c\,d\nu_A+\int c\,d\nu_B\le2F_{AB}        \tag{3}
\]
for arbitrary positive-measure $A,B$, including $A=B$. No subtraction of a point mass from an atomless permuton is used.

## 2. Equality at incomparable roots

Take two rational open rectangles $A,B$ arranged with every point of one strictly to the left and above every point of the other. If both have positive mass, (1) shows pointwise that $2F(x,y)\le c(x)+c(y)$ on $A\times B$, giving equality almost everywhere by (3). The countably many such pairs, allowing the order reversed and relative-open boundary rectangles, cover all strictly incomparable coordinate pairs. Thus for $\mu^2$-almost every incomparable $x,y$,
\[
 c(x)=c(y)=F(x,y).                                           \tag{4}
\]
Indeed, $F$ is individually at most both $c$'s. If either $c$ is positive, equality of the two products in (1) implies both intersection factors attain each of their corresponding positive maxima. In particular,
\[
 \mu(D(x)\triangle D(y))=\mu(U(x)\triangle U(y))=0.       \tag{5}
\]

It remains to handle the points at which (5) does not follow just by dividing products. Let $M=\{x:c(x)>0\}$. It has positive mass: a sampled diamond exists with positive probability, and a point with zero predecessor or successor mass almost surely cannot fill a middle position. The set with both predecessor and successor mass zero is null, since its points have $h(x)=0$ whereas $h=p>0$ almost everywhere. Up to null sets the remaining points are of two types: $L$ with $\mu D(x)=0$ but $\mu U(x)>0$, and $H$ with $\mu U(x)=0$ but $\mu D(x)>0$.

By (4) almost every cross-pair in $L\times M$ is comparable. It must be ordered $L<M$ almost everywhere, since $\int_L\mu D(x)\,d\mu(x)=0$. Likewise $M<H$ almost everywhere. If both extremes have positive mass, sampling an independent middle point conditionally on $M$ therefore gives $L<H$ almost everywhere by transitivity and Fubini. Within $L$ almost no pair is comparable by absence of predecessors, and similarly within $H$ by absence of successors. Statements about any null type are vacuous.

Now $231$ and $312$ are precisely the unordered three-root posets with one comparable pair $y<z$ and a third point $x$ incomparable to both. If at least one of these three roots lies in $M$, (4) puts all three in $M$ except on a null set. But (5) for $x,y$ implies $\mu(U(y)\setminus U(x))=0$, excluding the witness $z$ by independence. If none lies in $M$, the preceding two-layer order on $L,H$ excludes such a triple. Thus $d(231,\mu)=d(312,\mu)=0$. These two vanishing densities characterize layered permutons (Kabela–Král’–Noel–Pierron, §2 immediately before Lemma 6). This proves the first assertion. The Bellman theorem now gives uniqueness, and compactness plus continuity of pattern densities forces every near-optimal sequence to converge to that same permuton. This convergence is qualitative, not an edit-distance rate.

## 3. Finite counterpart (without a stability inference)

For a permutation $P$ of order $n\ge4$ attaining the maximum count $C>0$, take incomparable elements $u,v$. Make two rival permutations: drop $v$ and inflate $u$ to a decreasing pair; or drop $u$ and inflate $v$ to a decreasing pair. One may do this in both linear orders by placing the new point immediately next to the retained one, in reversed relative order. The single-root contributions to the sum of the two rival counts cancel those to $2C$; the zero-root counts cancel too. The difference is exactly
\[
 |D(u)|\,|U(u)|+|D(v)|\,|U(v)|
 -2|D(u)\cap D(v)|\,|U(u)\cap U(v)|\ge0.                     \tag{6}
\]
Here sets are of original elements, and automatically exclude both incomparable roots. By optimality both rival counts are at most $C$, so equality holds. Each incomparable pair having at least one positive predecessor-successor product therefore has positive products on both sides and exactly the same predecessor and successor sets. There is a nonempty set of positive-product points (the middle of some diamond). Every remaining point must be comparable to *every* such point: it is either below them all (no predecessors) or above them all (no successors). The possibility of being both minimal and maximal is excluded by comparability to the nonempty middle. The two extreme types are antichains with all lower points below all upper points. Just as in §2 there is no one-edge-plus-isolated triple, so $P$ avoids 231 and 312 and is layered. We do not obtain here a formula for its finite layer masses.

The finite cloning method is classical, in particular Stromquist's presentation of Barton's proof of layered replacement and Bóna–Sagan–Vatter's finite poset transformations. Equation (6) is the special exact diamond slack; the distributional extremality test (2)–(4) is needed for the unrestricted limit statement. No priority claim is made.
