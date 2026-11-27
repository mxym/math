# Euclidean symmetries and cyclotomic ideal markings of the standard trace lattice

Let \(K=\mathbb Q(\zeta_m)\) have reduced conductor \(m\) (so \(m\) is odd or is divisible by four), and put
\[
L_K=(\mathcal O_K,\ \langle x,y\rangle=\operatorname{Tr}_{K/\mathbb Q}(x\bar y)).
\]
Write \(w=|\mu(K)|\), the number of roots of unity in \(K\), \(d=\prod_{p\mid m,\;p\text{ odd}}p\), and \(b=w/(2d)\). Equivalently, \(w=2m\) for odd \(m\) and \(w=m\) otherwise. Empty products have value one, so these conventions include \(K=\mathbb Q\). Write \(n=[K:\mathbb Q]=b\varphi(d)\). For a finite group \(A\), use \(A\wr S_b=A^b\rtimes S_b\), with \(S_b\) permuting the \(b\) factors.

**Theorem.**

1. The full group of additive isometries of \(L_K\) is
\[
\operatorname{Aut}(L_K)\cong\left(C_2\times\prod_{p\mid d}S_p\right)\wr S_b.
\tag{1}
\]
This is also the group of additive symmetries of any centered unwrapped discrete Gaussian with spherical canonical energy on \(\mathcal O_K\).
2. Every element of \(\operatorname{Aut}(L_K)\) with irreducible rational characteristic polynomial is conjugate to multiplication by a root of unity. There is one conjugacy class of such elements of even order, of order \(w\) and characteristic polynomial \(\Phi_w\). If \(b\) is odd, there is in addition exactly one class of odd order, of order \(w/2\) and characteristic polynomial \(\Phi_{w/2}\). If \(b\) is even there is no odd-order class.
3. Let \(F\) be any cyclotomic field, \(I\subset F\) a nonzero fractional ideal, and \(a\) a totally positive archimedean weight, meaning a positive real vector on the real components of the fixed algebra \((F\otimes_\mathbb Q\mathbb R)^{\bar{\ }}\). Give \(I\) the metric \(\operatorname{Tr}_{F\otimes\mathbb R/\mathbb R}(a x\bar y)\). This weighted lattice is similar to \(L_K\) if and only if \(F=K\) as cyclotomic subfields of \(\mathbb C\), and \(I=u\mathcal O_K\) for some \(u\in K^\times\) with \(a\,u\bar u\) a positive scalar on all components. If \(a\) is algebraic, that scalar is in \(\mathbb Q_{>0}\). Every similarity in this situation can be made \(K\)-linear by composing it with a Euclidean lattice isometry of the target, and then it is multiplication by a scalar in \(K^\times\).

Thus a symmetry of the noise law does not have to respect its ring marking, but all full-order cyclotomic ideal markings on this particular metric are conjugate. This does not assert that arbitrary weighted ideal lattices have the same symmetry group, nor that general such lattices determine their fields.

## 1. The complete isometry group from the shortest shell

For nonzero \(x\in\mathcal O_K\), AM–GM over the \(n\) embeddings gives
\[
\langle x,x\rangle=\sum_\sigma|\sigma(x)|^2\ge n\,|N_{K/\mathbb Q}(x)|^{2/n}\ge n.
\]
The squared length equals \(n\) exactly when all conjugates have modulus one, and then \(x\) is a root of unity by Kronecker's theorem. Conversely each root of unity reaches equality. This shortest shell spans the lattice over \(\mathbb Z\), as it contains the powers of a primitive \(m\)-th root. The identity \(|\mu(K)|=w\) also follows directly from \(\mathbb Q(\zeta_m,\zeta_j)=\mathbb Q(\zeta_{\operatorname{lcm}(m,j)})\): for a multiple of \(m\), the totient is strictly larger than \(\varphi(m)\) unless it is \(m\) or \(2m\) with \(m\) odd.

To explicitly write the Gram data of shortest lines (pairs \(\{v,-v\}\)), factor \(m=2^a\prod_{p\mid d}p^{e_p}\), where \(a=0\) or \(a\ge2\). A projective representative can be chosen as the product of
\[
\zeta_{2^a}^{r_2}\quad (0\le r_2<2^{a-1},\text{ omit for }a=0),
\qquad
\zeta_{p^{e_p}}^{r_p}\zeta_p^{x_p}
\quad(0\le r_p<p^{e_p-1},\ x_p\in\mathbb Z/p\mathbb Z),
\]
over the coprime conductor factors. Use \(\zeta_p=\zeta_{p^{e_p}}^{p^{e_p-1}}\). Write \(r\) for the tuple of \(r_i\)'s and \(x\) for the tuple of \(x_p\)'s, and call the representative \(v_{r,x}\). There are \(b\) possibilities for \(r\) and \(d\) for \(x\). The normalized Gram identity is
\[
\frac{\langle v_{r,x},v_{r',y}\rangle}{n}
=\begin{cases}
0,&r\ne r',\\[2pt]
\displaystyle\prod_{p:x_p\ne y_p}\frac{-1}{p-1},&r=r'.
\end{cases}
\tag{2}
\]
Indeed, normalized traces factor over coprime conductor components. In \(\mathbb Q(\zeta_{p^e})\), the trace of \(\zeta_{p^e}^{s}\) vanishes if \(p^{e-1}\nmid s\): sum over a fiber of the reduction of units from modulus \(p^e\) to modulus \(p^{e-1}\) when \(e\ge2\). If \(s\) is a nonzero multiple of \(p^{e-1}\) modulo \(p^e\), the normalized trace equals \(-1/(p-1)\) by reduction to the primitive \(p\)-th roots. The full multiple gives 1. This also gives the dyadic zero between distinct \(r_2\)'s. Within a block every two shortest lines have nonzero inner product. These \(b\) blocks are therefore intrinsic components of the graph joining nonorthogonal shortest lines. Their spans are orthogonal, and their integer spans sum to the whole lattice since the shortest vectors generate it.

Here is why the absolute Gram data in each block determine precisely the independent coordinate permutations, even when different products of the factors \(p-1\) coincide. For \(d>1\) let \(p_0\) be its smallest prime divisor. The largest absolute inner product between distinct unit-normalized shortest lines is \(1/(p_0-1)\), attained exactly when only the \(p_0\)-coordinate differs. This partitions each block into recognizable \(p_0\)-element fibers. Between two different fibers the maximum over representatives is exactly the absolute Gram weight for the remaining coordinates, attained precisely when the \(p_0\)-coordinates agree. The induced permutation of the fibers thus preserves the shorter-product weighted structure. By induction it is a product of the remaining coordinate permutations. After composing with their inverse, the permutation fixes each fiber setwise. The maximizing equality rule across any two fibers requires that their permutations of the \(p_0\)-coordinate coincide. If there is only one fiber there is no extra condition. Starting with the singleton case gives \(\prod_{p\mid d}S_p\).

Every such coordinate permutation preserves the signed Gram matrix (2); it therefore sends the labelled generating roots linearly to their images and extends to an isometry of their real span. To see well-definedness without choosing a basis, any relation among the representatives has squared norm zero under the Gram matrix and so remains a relation. The resulting map preserves the integer span and so is a lattice isometry. Conversely, once the projective permutation is removed, an isometry can only change the signs of the representatives; preservation of the nonzero inner products forces one common sign in each block. All permutations of the blocks and each block's sign are allowed by (2). This proves (1). For a positive spherical precision, the normalized discrete Gaussian assigns mass in exact proportion to \(e^{-t\langle x,x\rangle}\). An additive bijection preserves this law if and only if it preserves all norms, hence if and only if it is one of these isometries.

For comparison, the isometries normalizing the cyclic subgroup \(\{x\mapsto\omega x:\omega\in\mu(K)\}\) are exactly
\[
x\mapsto\eta\,\sigma(x)\qquad (\eta\in\mu(K),\ \sigma\in\operatorname{Gal}(K/\mathbb Q)).
\tag{3}
\]
If an isometry conjugates multiplication by a fixed primitive \(w\)-th root to multiplication by another primitive root, this identity extends from that generator to the full field action. The map sends \(1\) to a shortest vector and therefore to a root of unity, proving necessity; sufficiency is immediate. The group centralizing a primitive multiplication is the subgroup of root multiplications, by the same argument. The two groups in (1) and (3) are equal only for reduced conductors \(1,3,4\): their orders are respectively \((2\prod_{p\mid d}p!)^b b!\) and \(w n=2b^2\prod_{p\mid d}p(p-1)\). For \(b=1\) the ratio is one exactly if no odd prime or only \(3\) occurs; for \(b=2\) only the empty product gives equality; for \(b\ge3\), \(2^b b!>2b^2\) and all remaining factor ratios are at least one. For example, with \(m=5\) a transposition of two of the nonidentity shortest representatives, fixing the other three, preserves the Euclidean Gaussian. An affine permutation of the five coordinate labels cannot have exactly three fixed points, so this transposition is not in (3).

## 2. Irreducible rotations and a unique even-order marking

Let \(T\in\operatorname{Aut}(L_K)\) have irreducible characteristic polynomial over \(\mathbb Q\). Each block span is rational since it is generated by lattice vectors. If the induced permutation of the \(b\) block spans is not a single cycle, the sum over a proper cycle gives a proper rational invariant subspace. Thus the blocks form one \(b\)-cycle. Changing isometric identifications of consecutive blocks turns \(T\) into the cycle with identity transports except on the final edge, with return map \(h=T^b|_{V_1}\) on the first block. For a fixed \(b\)-cycle, a further common change of identifications conjugates \(h\) by any within-block isometry.

The rational block representation in (2) is the tensor product over \(p\mid d\) of the standard rational \(S_p\)-representations \(\{(z_1,\ldots,z_p):\sum z_i=0\}\), and its central sign factor acts by \(\pm 1\). This follows by identifying the block's labelled vectors with products of the \(p\) simplex vertices \(e_j-\mathbf 1/p\), normalized in the real metric; the real normalization is irrelevant for the rational representation since the labelled linear relations are exactly the relations of the rational tensor of those simplex configurations. Write \(h=(\varepsilon,(h_p)_{p\mid d})\) in this representation. If \(h_p\) is not a \(p\)-cycle, it has a nonzero rational fixed vector in the standard representation (a nonconstant vector constant on each cycle and summing to zero). Its line is proper since \(p-1\ge2\). Taking its tensor product with the whole of the other factors gives a proper nonzero rational \(h\)-invariant subspace of \(V_1\). Taking the direct sum of its transported images around the blocks contradicts irreducibility of \(T\).

We are left with \(h_p\) a \(p\)-cycle for each odd prime factor. All these cycles are conjugate in their respective \(S_p\), so the sign \(\varepsilon\) is the only remaining class label. The eigenvalues of the standard representation of a \(p\)-cycle are the nonidentity \(p\)-th roots. Their products as \(p\) varies are all primitive \(d\)-th roots, without repetitions. The eigenvalues of \(T\) are the \(b\)-th roots of these eigenvalues of \(h\), with \(h\)'s additional sign. This is the direct characteristic-polynomial calculation for the cyclic block matrix.

If \(b\) is odd, every prime divisor of \(b\) divides \(d\); taking \(b\)-th roots of the primitive \(d\)-th roots makes exactly the primitive \(bd\)-th roots, and the negative sign makes exactly the primitive \(2bd\)-th roots. If \(b\) is even, write \(b=2^c b_0\) with \(b_0\) odd. With the positive sign, there are roots of varying \(2\)-parts of their orders (from \(1\) up to \(2^c\)), making the characteristic polynomial reducible. The negative sign forces the order's \(2\)-part to be \(2^{c+1}\), and its odd part to be \(b_0d\); all roots are then primitive \(2bd\)-th roots. These order claims can also be checked at each prime using \(\operatorname{ord}(\lambda^b)=\operatorname{ord}(\lambda)/\gcd(b,\operatorname{ord}(\lambda))\). In each irreducible case the count is \(b\varphi(d)\), the degree of the stated cyclotomic polynomial. This proves the asserted classes, since primitive \(w\)-th root multiplication is such an isometry and has irreducible characteristic polynomial. When \(b\) is odd, multiplication by a primitive \(w/2\)-th root also generates the field and realizes the other class. The use of *characteristic*, rather than minimal, polynomial is important: scalar signs on a higher-dimensional space can have irreducible minimal polynomial without satisfying this condition.

In particular, all cyclic subgroups of order \(w\) generated by irreducible isometries are conjugate. There are exactly \(|\operatorname{Aut}(L_K)|/(w n)\) such subgroups, by the normalizer in (3), and exactly \(|\operatorname{Aut}(L_K)|/w\) elements in the corresponding class, by the centralizer.

## 3. Weighted ideal lattices with the same Euclidean shape

Suppose \(f:I\to L_K\) is a Euclidean similarity, so it extends to a \(\mathbb Q\)-linear isomorphism \(F\to K\) and a scaled real isometry of the archimedean spaces. Multiplication by a primitive root of the full root-of-unity group of \(F\) preserves \(I\) and its weighted norm, and has irreducible characteristic polynomial. Conjugating it by \(f\) gives an irreducible isometry of \(L_K\). Its order is even, so the classification forces its order to be \(w\), and hence \(F=\mathbb Q(\zeta_w)=K\) inside \(\mathbb C\). By part 2 compose \(f\) with a target isometry so that it intertwines the same chosen primitive root multiplication on the source and the target. It then intertwines multiplication by all elements of \(K\), hence is \(K\)-linear. It is therefore multiplication by \(u^{-1}\), where \(I=u\mathcal O_K\) since the map is onto.

Let \(c>0\) denote the squared length factor in \(\langle f(x),f(y)\rangle=c\,\operatorname{Tr}(a x\bar y)\). Substituting \(x=u z,y=u v\) gives \(\operatorname{Tr}((a u\bar u-c^{-1})z\bar v)=0\) for all \(z,v\in\mathcal O_K\). Taking \(v=1\) and extending by real linearity, nondegeneracy of the trace on the archimedean algebra gives \(a u\bar u=c^{-1}\mathbf 1\). If this weight is algebraic, a field element whose images under all embeddings are the same belongs to \(\mathbb Q\). Conversely, the stated scalar condition makes \(x\mapsto u^{-1}x\) a similarity onto the standard lattice. No step assumes that the original similarity preserved multiplication.

One can already recover the field alone from the shortest shell and rank: multiplication by a primitive full root of unity on any nonzero vector is free, so the order of the source root group divides the target's kissing number \(w\). Both orders are even and their totients are both the rank, which forces equality. The extra conclusion giving the principal ideal and the cancelling weight comes from conjugacy, not just from this divisibility.

For example, the unweighted ideal \((1-\zeta_5)\mathcal O_{\mathbb Q(\zeta_5)}\) is principal but cannot be similar to the standard trace lattice. Every generator \(u\) of that ideal has absolute norm \(5\). If \(u\bar u=q\) were rational, the norm would be \(q^2\), impossible. With weight \(a=((1-\zeta_5)(1-\bar\zeta_5))^{-1}\), the cancellation in the theorem makes the same ideal isometric to the standard trace lattice.

## Relation to previous work

- [Beck–Hoşten, *Cyclotomic Polytopes and Growth Series of Cyclotomic Lattices*, §2](https://arxiv.org/abs/math/0508136) identifies tensor and direct-sum descriptions of the polytope generated by roots of unity. [van Woerden, *The Closest Vector Problem in Cyclotomic Lattices*, §3](https://math.leidenuniv.nl/scripties/BachVanWoerden.pdf) derives the analogous canonical metric tensor/orthogonal-sum decomposition. The factorization itself is not new. Here the weighted shortest-line graph recovers the coordinate factors intrinsically and gives the full group, after which the classification of irreducible rotations yields the marking statement.
- [Lemire Paquin, *Ideal Lattices in Cyclotomic Fields*, Propositions 4.1.3, 4.2.5 and 4.2.9](https://central.bac-lac.gc.ca/.item?app=Library&id=TC-QMM-123244&oclc_number=911042918&op=pdf) relates cyclotomic ideal realizations in general to irreducible lattice isometries, treats the cyclic permutation of orthogonal factors, and gives the field restriction for the \(\mathbb Z^n\) case. The argument above computes the conjugacy classes for the whole family of standard cyclotomic trace lattices and determines the fractional ideal and the necessary metric cancellation.
- [Lyubashevsky–Peikert–Regev, *On Ideal Lattices and Learning with Errors Over Rings*, §2.3](https://web.eecs.umich.edu/~cpeikert/pubs/ideal-lwe.pdf) specifies the canonical metric and distinguishes error geometry from coefficient coordinates. The statements here concern only unwrapped Euclidean invariance and compatible markings, not modular laws or a security claim for a concrete scheme.

Replay with `node verify-cyclotomic-ideal-marking.js`. The last run passed 657,452 exact checks, including shortest-shell Gram values, exhaustive weighted permutation counts for small conductors and rational cyclotomic eigenvalue orders for generated return maps.
