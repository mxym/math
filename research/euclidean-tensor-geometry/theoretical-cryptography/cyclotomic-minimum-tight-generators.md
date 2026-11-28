# Minimum integral tight frames for cyclotomic lattices with at most two odd primes

## 1. Definition and theorem

Let \(m=2^a\prod_{i=1}^r p_i^{e_i}\), where \(a\ge0\), the \(p_i\) are distinct odd primes, and \(e_i\ge1\). We allow \(m=1\). Use the real Euclidean space of the full canonical embedding of \(\mathcal O_m=\mathbb Z[\zeta_m]\), with inner product \(\operatorname{Tr}(x\overline y)\) (a complex place contributes twice). Write
\[
 b=2^{\max(0,a-1)}\prod_i p_i^{e_i-1},\quad
 d=\phi(m)=b\prod_i(p_i-1),\qquad
 L=b\prod_i p_i=\begin{cases}m,&a=0,\\m/2,&a\ge1.\end{cases}
\]
For a finite list \(v_1,\ldots,v_M\in\mathcal O_m\), “integral generating tight frame” means both \(\sum_j\mathbb Z v_j=\mathcal O_m\) and \(\sum_j v_jv_j^{\mathsf T}=\alpha I\) on the real canonical space for some \(\alpha>0\). Repetitions, zero, unequal lengths and arbitrary positive frame bound are permitted. Every list entry has the same weight in the frame operator.

**Theorem.** If \(0\le r\le2\), the minimum \(M\) is \(L\). At length \(L\), the list is the standard root-of-unity list up to permutation and independent changes of sign. The reference list is all \(m\)-th roots if \(a=0\), or one representative of each antipodal pair of \(m\)-th roots if \(a\ge1\); its unscaled frame bound is \(L\).

The conclusion does not assume the generators are shortest vectors, are related by the Galois group, have equal norm, or are an orbit of any transformation. It concerns exact covariance for integral linear representations of a known Euclidean lattice. It does not assert any optimality for nontight bases, approximate tightness, weighted frames, general ideals, or conductors with three or more odd prime factors. In particular, exact covariance for arbitrary independent input coordinates is not an equality of their non-Gaussian laws. There is no security or decoding claim.

## 2. The rational Gram model and the scale obstruction

Put \(H_p=I_{p-1}+J_{p-1}\), with \(J\) the all-ones matrix. Normalize the trace form by \(1/L\). For \(p^e\) odd, use the basis
\(\zeta_{p^e}^{u}(\zeta_{p^e}^{p^{e-1}})^v\),
\(0\le u<p^{e-1}\), \(0\le v<p-1\). These are precisely the usual consecutive powers, in a different order. The Ramanujan sum at a difference of exponents is zero when it is not divisible by \(p^{e-1}\), is \(-p^{e-1}\) when divisible by \(p^{e-1}\) but not by \(p^e\), and is \(\phi(p^e)\) at zero. Thus the Gram divided by \(p^e\) is \(p^{e-1}\) copies of \(H_p^{-1}=I-J/p\). The power-of-two basis has Gram \(2^{\max(0,a-1)}I\), including the trivial factor. For coprime conductors the rings of integers tensor: the tensor products of powers generate the ring by Bezout, and the ranks agree. Embeddings and traces factor too. The normalized Gram is therefore \(G=H^{-1}\), where
\[
 H=I_b\otimes\bigotimes_i H_{p_i}.
\]
The empty tensor is the scalar 1.

Let \(C\in\mathbb Z^{d\times M}\) have the frame coordinates as columns in this basis. Tightness is precisely
\[
 CC^{\mathsf T}=cH,\qquad c=\alpha/L>0.
 \tag{1}
\]
Integer generation implies that the reduction of \(C\) has full row rank over every prime field. In the converse direction this prime-rank condition is sufficient for generation by Smith normal form, although the proof below only needs necessity. Since \(H\) has an entry 1, \(c\) is a positive integer. If some prime \(\ell\) divides \(c\), mod \(\ell\) the row space \(U\) of \(C\) satisfies \(U\subseteq U^\perp\). The standard bilinear dot product is nondegenerate even in characteristic 2, so \(M\ge 2d\). When \(r\le2\), \(L<2d\): the largest ratio for two distinct odd primes is \(3\cdot5/(2\cdot4)=15/8\), and the zero- and one-prime cases also have ratio \(<2\). Thus every candidate with \(M\le L\) has \(c=1\).

For comparison, for any number of odd primes, when \(c=1\) mod \(p_i\) the radical of the restricted row-space pairing has dimension \(d/(p_i-1)\). This follows because \(H_{p_i}\) has corank one mod \(p_i\), and every other tensor factor is invertible there. In particular \(M\ge d+d/(p_i-1)\), an elementary local lower bound, not by itself enough for the case of two odd primes.

Write \(D_p=[\,I_{p-1}\mid-\mathbf 1\,]\), so \(D_pD_p^{\mathsf T}=H_p\). The standard coordinate matrix
\[
 C_0=I_b\otimes\bigotimes_i D_{p_i}
 \tag{2}
\]
has \(L\) columns, is surjective over the integers (it includes basis columns), and satisfies (1) at \(c=1\). On each odd power block its columns are the full \(p\)-cycle of roots, using \(\sum_{v=0}^{p-1}\zeta_p^v=0\); for the power of two we keep half the powers. Thus (2) is exactly the stated root list. It remains to prove that any \(C\) satisfying \(CC^{\mathsf T}=H\) with independent rows mod 2 has the nonzero columns of (2), up to signs and order.

## 3. Row support lemmas

Use signed subsets for vectors with nonzero entries in \(\{-1,1\}\). Two signed two-subsets have dot product 1 precisely when they share one coordinate with the same sign. A family of distinct two-subsets that pairwise intersect is a star (all sets share a coordinate), unless it is exactly the three edges of a triangle: from \(\{x,y\},\{x,z\}\) an edge missing \(x\) must be \(\{y,z\}\), and the only edges meeting all three are these three. In particular a pairwise-intersecting **even** family of at least two different two-subsets is a star.

**Four-subset lemma.** If \(h\ge5\) signed four-subsets with pairwise dot product 2 are independent mod 2, every support contains a common pair, and their outside pairs are disjoint. The signs on a shared coordinate are constant.

Indeed two supports must intersect in exactly 2: the overlap must be even and positive, and overlap 4 would give equal mod-2 vectors. Thus both shared signs agree. If a particular pair lies in at least four supports, their outside pairs are disjoint. Any support missing part of that pair would have to use either at least five coordinates (one core coordinate and one per petal), or at least eight (none in the core and two per petal). If it lies in exactly three supports, every other support must contain exactly one core coordinate and one of each petal. All supports then lie in eight positions and, since every dot product is even, their mod-2 span is self-orthogonal of dimension at most four, a contradiction. Thus without a common pair, every pair occurs at most twice. Inside each fixed support its \(h-1\) pairwise intersections must then be distinct edges on four vertices, so \(h\le7\). For \(h=6,7\) each vertex in each such support occurs in at least two of its intersection edges, so each used coordinate has multiplicity at least three. At most \(\lfloor4h/3\rfloor\) positions are used, which contradicts independence of this self-orthogonal system. For \(h=5\) each coordinate occurs at least twice (four edges on four vertices cannot avoid one vertex). Independence forces at least ten positions, so exactly ten are used and each has multiplicity two. This would count \(\sum_x\binom{\operatorname{mult}(x)}2=10\) pair intersections with multiplicity, whereas the five sets intersect twice per pair and give 20. This proves the lemma.

## 4. The tensor block

For two odd primes \(p<q\), put \(n=p-1\), \(h=q-1\). The row vectors \(w_{ij}\) of a single block, \(1\le i\le n\), \(1\le j\le h\), obey
\[
 w_{ij}\mathbin{\cdot}w_{k\ell}
       =(1+\delta_{ik})(1+\delta_{j\ell}).
 \tag{3}
\]
Each has squared norm 4. An integer norm-4 vector of type \(\pm2e_x\) has only even dot products; (3) provides an odd one by differing both labels. Thus every row is a signed four-subset. For fixed \(i\), the \(h\) supports have pairwise overlap exactly two by mod-2 independence. If \(h\ge5\) they have common core \(K_i\) with disjoint petals by the four-subset lemma. The only prime case with \(h<5\) is \((p,q)=(3,5)\); section 5 proves the same conclusion for both families in that case.

Once these family cores exist, fix \(i\ne k\) and a row \(w_{ij}\). Let \(u\) be its dot product with the signed pair \(K_k\), with the signs in family \(k\). Using disjointness of that family's petals, the four-coordinate budget implies
\[
 |u|+|2-u|+(h-1)|1-u|\le4.
\]
Indeed the dot contributions required in the petals are \(2-u\) in label \(j\) and \(1-u\) in every other label. As \(h\ge4\), the only integer \(u\in[-2,2]\) satisfying the inequality is \(1\). Consequently \(w_{ij}\) meets \(K_k\) in exactly one position and matches its sign. The cores \(K_i,K_k\) cannot coincide or the intersection would be two; they cannot be disjoint because all \(h>2\) disjoint petals of family \(i\) would have to meet the two positions of \(K_k\). Therefore all \(K_i\) are distinct pairwise-intersecting pairs. Their family size \(n\) is even, so \(K_i=\{x,u_i\}\) with a common center \(x\), and the sign on \(x\) agrees across the families. Every \(w_{ij}\) uses \(x,u_i\) and no other \(u_k\).

Remove these core coordinates. The remaining petals \(P_{ij}\) are signed two-subsets. Within family \(i\) they are disjoint. Between families the dot product of petals is \(\delta_{j\ell}\), by subtracting the contribution of \(x\) in (3). Thus for \(i\ne k\), the petals \(P_{ij},P_{kj}\) meet in exactly one position with equal sign. If \(j\ne\ell\), the dot product is zero. An overlapping pair with dot zero would have to share both positions and have a sign disagreement; sharing both is impossible since \(P_{ij}\) already meets \(P_{kj}\), disjoint from \(P_{k\ell}\). Therefore the different-\(j\) petals are disjoint. For fixed \(j\) the \(n\) pairwise-intersecting petals form a star \(P_{ij}=\{v_j,z_{ij}\}\), with sign agreement on \(v_j\), by the even-family argument again. All used coordinates are now precisely
\[
       x,\quad (u_i)_i,\quad (v_j)_j,\quad (z_{ij})_{ij},
\]
distinct except for the displayed reuses. Signs agree wherever a coordinate is reused. This is the rectangular tensor pattern, so \(pq\) coordinates are occupied. Choosing separate signs of the coordinates gives the exact prescribed rows \((e_i-e_0)\otimes(e_j-e_0)\) of \(D_p\otimes D_q\) in the order of the original labels.

## 5. The four-petal exception \((p,q)=(3,5)\)

This section uses a paper proof; the companion script checks the cases independently by an exhaustive finite search. Denote the first family's (positive) signed supports by \(A_0,\ldots,A_3\). All their signs can be made positive by coordinate sign choices, since shared coordinates have equal signs. Their fourfold intersection has size \(a_0\in\{0,1,2\}\); let \(t_i\) be the number of coordinates belonging to all three sets other than \(A_i\), but not \(A_i\). If \(\{i,j,k,\ell\}=\{0,1,2,3\}\), the exact pair-only and singleton multiplicities are respectively
\[
 2-a_0-t_k-t_\ell,\qquad 2a_0-2+\sum_{j\ne i}t_j.
 \tag{4}
\]
The first formula uses pair intersection 2; the second subtracts the pair, triple and fourfold contributions from 4.

* If \(a_0=2\), all \(t_i=0\) and we have the desired sunflower.
* If \(a_0=1\), at most one \(t_i=1\), all others zero. With none, all membership patterns have even weight, so independence mod 2 fails. With one, relabel so \(t_0=1\). The membership patterns are the singleton \(\{i\}\) and the pair \(\{0,i\}\) for \(i=1,2,3\), the triple \(\{1,2,3\}\), and all four. Replace both families' index 0 rows by their negatives and each index \(i\ne0\) row by its difference with its own family's old index 0 row. This is the unimodular change of base vertex in the star roots of \(A_4\), so it preserves both the cross Gram and same-family Grams in (3), and mod-2 independence. In the transformed first family, any column whose old pattern contains 0 has its membership complemented on indices \(1,2,3\) and retains index 0; every other column is unchanged. The resulting patterns are all four singletons and all four triples.
* If \(a_0=0\), a value \(t_i\ge2\) violates the inequalities (4) (at \(t_i=2\) all other \(t_j\) would vanish). Thus \(t_i\in\{0,1\}\), with at least three 1s. With exactly three, the xor of the three rows whose indices have \(t_i=1\) vanishes: (4) leaves the singleton of the zero index, the three pairs within the other indices, and the three triples consisting of that zero index and two of the others. With four 1s, the patterns are again all four singletons and all four triples.

It suffices to exclude the latter exceptional pattern, calling its singleton coordinates \(x_i\) and its triple missing \(i\) coordinates \(y_i\). After making shared first-family signs positive (also after the base change), write the entries of the second family's row \(B_j\) at these coordinates as \(X_i,Y_i\). Then
\(X_i-Y_i=1+\delta_{ij}-S\), with \(S=\sum_iY_i\). The budget of four \(\pm1\) entries gives exactly two possible types, each with one additional coordinate outside this first family:
\[
 \begin{array}{ll}
 \mathrm{A}(j,i): & x_j,\ x_i,\ y_i \quad(i\ne j),\text{ all positive},\\
 \mathrm{B}(j,i): & -x_i,\ y_k,\ y_\ell\quad
       (\{j,i,k,\ell\}=\{0,1,2,3\}).
 \end{array}
 \tag{5}
\]
In fact \(S<0\) is impossible at the \(j\) equation and \(S=0\) costs at least five positions; \(S\ge3\) is impossible or costs at least six at the other three equations. For \(S=1\) the three other differences are zero and the \(j\) difference is 1. If \(Y_j=-1\), at least two of the other pairs must be positive, exceeding the budget. Otherwise \(X_j=1,Y_j=0\), and there is exactly one other positive pair. For \(S=2\), the three other differences are \(-1\) and already require three positions; \(X_j=Y_j\) must vanish. The two required positive \(Y\)'s leave one negative \(X\). This proves (5).

Inside the second family, any two supports meet at exactly two positions with equal signs. If an \(\mathrm A(j,i)\) and a \(\mathrm B(k,\ell)\) coexist, then \(\ell\notin\{j,i\}\) to prevent opposite signs, and \(i\ne k\) because otherwise there is no shared \(y\) and even a common extra position cannot create overlap two. Every mixed pair then shares one named \(y\) and its extra coordinate. Thus with both types all extra coordinates are equal. One A with three B is impossible since its target \(i\) is then a B index, and one B with three A is impossible since its negative index \(\ell\) is then an A index. With two of each, the two A rows must target each other's indices, which gives overlap two before adding the common extra coordinate, also impossible.

If all four have type A, associate each row \(j\) with the two-set \(\{j,i_j\}\). Disjoint pairs give no named coordinate overlap, hence are impossible. These edges cover all four labels, so form a star rather than a triangle (duplicate edges are allowed, by first taking distinct edges). Its three leaves target its center \(c\), hence have pairwise two named overlaps and must all have different extra coordinates. Row \(c\) targets one of the leaves; with each of the other two it has exactly one named overlap, forcing its extra coordinate to equal both of theirs, a contradiction. In the all-B case use the edges \(\{j,i_j\}\) again. Disjoint edges give no named coordinate overlap. Two leaves now share their central **negative** coordinate and one \(y\); the center row with either unselected leaf shares exactly one \(y\). This yields precisely the same contradiction. Therefore no exceptional first family can occur. Exchanging the families also gives the result for the second.

## 6. Different blocks cannot reuse coordinates

For \(r=1\), the rows of a block have squared norm 2 and pairwise dot product 1. Their supports are distinct pairwise-intersecting signed two-subsets; the even size \(p-1\) gives a star. After coordinate signs they span the zero-sum hyperplane on their \(p\) occupied coordinates. A row from an orthogonal block restricted to these \(p\) coordinates is therefore constant. It has at most two nonzero entries globally, and \(p\ge3\); hence it cannot overlap.

For \(r=2\), put one classified block in its rectangular form. On its \(p q\) positions the orthogonal complement consists of arrays \(u_i+v_j\), since vanishing against \((e_i-e_0)\otimes(e_j-e_0)\) means that every such mixed difference vanishes. A row from an orthogonal block has at most four nonzero positions. If the \(u_i\) are not all equal, every column of its restriction has at least one nonzero, giving at least \(q\ge5\). If they are all equal, any nonzero restriction is supported on entire columns. This is impossible for \(p\ge5\); for \(p=3\) it forces a full three-position column. But in its own classified block, the row has at most one coordinate private to it, so at least one of those old-column positions is used by another row of the same new block. That other row, being orthogonal to the old block, also uses the entire old column. Two rows of one block would then share at least three positions, whereas their classified supports meet in at most two. This is a contradiction. The support of each block is therefore disjoint from all others. For \(r=0\) the norm-one rows simply occupy distinct positions.

These disjoint blocks give \(L\) nonzero columns in every scale-one representation, and identify every one with (2) up to signs and permutation. Together with the scale obstruction this proves the theorem.

## 7. Primary references and reproducibility

* Chien, Waldron, Flynn, [*Tight frames for cyclotomic fields and other rational vector spaces*](https://doi.org/10.1016/j.laa.2015.02.021), §6, constructs the circular root frame and its canonical rational coordinates; [author PDF](https://www.math.auckland.ac.nz/~waldron/Preprints/Rational-frames/1-s2.0-S0024379515001275-main.pdf). The construction is not the new claim here. The question here allows a different arbitrary integral generating list and proves the minimum length and equality case, with the canonical metric fixed.
* Beck, Hoşten, [*Cyclotomic polytopes and growth series of cyclotomic lattices*](https://arxiv.org/abs/math/0508136), §2, Propositions 5–6 and Theorem 7, uses prime-power copies and tensor products for root-generating polytopes. The Gram calculation here is included explicitly; the primitive metric representation, not the cyclotomic product itself, is the new step.

* The [companion basis-norm theorem](cyclotomic-gaussian-coordinate-optima.md) optimizes the largest singular value for a square integral basis and classifies its minimizers. A square optimum need not be tight: this note minimizes the number of columns of a tight integral generating list, without imposing a square basis or an operator-norm objective.

Run the accompanying Python 3 verifier for independent finite checks of the exponent/Gram identities and the full signed \(3\times5\) block (the only small exception in the proof). The code uses exact integers; the general theorem does not depend on numerical spectral estimates.
