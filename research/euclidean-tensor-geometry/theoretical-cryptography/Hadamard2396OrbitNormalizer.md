# A global normalizer obstruction at Hadamard order 2396

Let \(p=599\), \(n=4p=2396\), and suppose that \(H\) is a real Hadamard matrix of order \(n\). Its signed automorphism group is
\[
G=\{(R,S): R,S\text{ signed permutation matrices},\ RH S^\mathsf{T}=H\}.
\]
This statement assumes a hypothetical matrix, and does not assert one exists.

**Theorem.** If \(G\) has a subgroup \(P\) of order \(p\), then:

1. Every Sylow \(p\)-subgroup has order \(p\). Its action on both the row and the column labels has four regular orbits.
2. The \(4\times4\) matrix \(D\) of orbit block sums, defined after making the generator pure permutation, satisfies \(DD^\mathsf T=2396 I_4\) and has 50 possible signed row/column equivalence classes. Every such class is a quaternion multiplication matrix or its transpose. The simultaneous signed monomial stabilizer of each \(D\) is \(Q_8\).
3. There is an injection \(N_G(P)/P\hookrightarrow Q_8\times C_2\), with second component the induced action on \(P\), which can only be identity or inversion. In particular no common affine multiplier of order divisible by 13 or 23 is possible in the normalizer, even if the matrix was not built by a Goethals–Seidel ansatz. The normalizer has order dividing \(16p\).
4. The kernel of the signed action on the orbit block sums is either \(P\) or a dihedral group of order \(2p\). In the latter case an inverting element is an involution, and after recentering all sixteen \(p\times p\) circulant blocks are individually symmetric. Its four fixed row and four fixed column positions intersect in a Hadamard matrix of order four.

The current [construction survey](https://arxiv.org/abs/2610.27175v2) lists 2396 as its smallest unresolved order. [Cinna Davis's order-2396 study](https://itsdavis.com/solved-conjectures/results/hadamard-2396/proof/) gives a global exclusion of a different prime (479) and multiplier restrictions on different bordered and two-core constructions. The recent [order-4792 construction](https://charlesponeill.com/maths-releases/hadamard-4792/) concerns twice the order, using four functions on a group of order 1197. Neither these comparisons nor our orbit analysis are constructions at order 2396. The new conclusion here concerns the full signed normalizer whenever a 599-cycle subgroup occurs; it does not show that any such subgroup must occur.

## 1. An order-\(p\) automorphism acts freely on labels

If \((R,S)\) has order \(p\), then \(R H=H S\). Each matrix has order \(p\), since \(H\) is invertible and either component determines the other. The product of signs on each cycle of its underlying permutation is \(+1\), and fixed positions have sign \(+1\), because \(p\) is odd. Conjugate each component by a diagonal sign matrix, changing \(H\) by signed row/column equivalence, and make both components ordinary permutations. Similarity through \(H\) shows that both have the same fixed count \(f\), divisible by \(p\) because \(n=4p\).

Choose any \(p\)-cycle of columns and its normalized indicator \(v\). At each fixed row, all entries of this column cycle agree, so the corresponding coordinates of \(Hv\) have square \(p\). Since \(\|Hv\|^2=n\), we have \(fp\le n\) and \(f\le4\). Therefore \(f=0\). Any \(p\)-subgroup of \(G\) now acts freely on underlying row labels: a nontrivial \(p\)-element fixing a label would have a nontrivial power of order \(p\) fixing it. Hence its order divides \(4p\), proving the Sylow assertion and giving four row and four column orbits.

Use coordinates \((i,x)\) in each orbit, \(x\in\mathbb F_p\), so the generator of \(P\) translates all coordinates by one. The blocks of \(H\) have the form \(H_{ij}(x,y)=f_{ij}(y-x)\). On the \(P\)-fixed subspaces choose the normalized indicators of each orbit as orthonormal bases. In these bases the restriction of \(H\) is
\[
                     D_{ij}=\sum_{x\in\mathbb F_p} f_{ij}(x).
\]
Since \(H\) bijects the fixed subspaces and is \(\sqrt n\) times orthogonal, \(DD^\mathsf T=nI_4\). All entries are odd, hence nonzero, and have absolute value at most \(\sqrt n<p\). In particular no \(f_{ij}\) is constant.

## 2. Exact four-square orbit-sum classification

For \(a,b,c,d\in\mathbb R\), write the matrix of left quaternion multiplication by \(a+bi+cj+dk\) as
\[
 Q(a,b,c,d)=
 \begin{pmatrix}
 a&-b&-c&-d\\
 b&a&-d&c\\
 c&d&a&-b\\
 d&-c&b&a
 \end{pmatrix}.
\]
The [exact verifier](verify_hadamard_2396_orbit_normalizer.py) checks this finite classification. In each row of \(D\), absolute values are positive odd integers and their squares sum to 2396. There are 28 sorted such quadruples. A signed column permutation makes a selected first row positive and nondecreasing, and independent row signs make the first coordinate of every other row positive. The checker builds all 4,800 candidate signed rows with first coordinate positive. For each fixed first row, six are orthogonal to it, and exactly two unordered triples of those six are mutually orthogonal. This gives 56 normalized charts before taking the remaining signed row and column equivalences. Canonicalization chooses every possible first row and every column order compatible with its sorted absolute values, uses the unique column signs making it positive, makes the first coordinate of each remaining row positive, and sorts those rows. The canonical image is exactly the set of images of \(Q(a,b,c,d)\) and \(Q(a,b,c,d)^\mathsf T\) for the 28 quadruples: 50 classes, with transpose merging the two orientations for precisely six quadruples.

For each class the signed column permutations preserving the projective row set (each row considered up to sign) number eight: they have element orders \(1,2,4,4,4,4,4,4\). Such a column permutation determines its signed row partner uniquely, by row distinctness up to sign. This is \(Q_8\); equivalently, for each quaternion matrix right multiplication by the eight signed quaternion units supplies the entire stabilizer. The classification is a finite assertion about \(D\), not about which classes lift to Hadamard matrices \(H\).

## 3. The normalizer and the excluded multipliers

Write \(N=N_G(P)\). Conjugation on \(P\) is an action \(\alpha:N\to\mathbb F_p^\times\). A normalizer element acts in the row orbits by an orbit permutation and affine coordinate functions \(x\mapsto a x+b_i\), and in the column orbits by an orbit permutation and \(y\mapsto a y+c_j\), with the same multiplier \(a=\alpha(g)\). The signs are constant in each orbit: conjugation takes the pure translation to a power of itself, so the signed commutation relation forces each sign to agree at consecutive coordinates. On the fixed subspaces these row and column actions give a homomorphism \(\rho:N\to\operatorname{Aut}(D)\cong Q_8\).

For \(g\in\ker\rho\), the orbit permutations and orbit signs are trivial. Its block conditions are therefore \(f_{ij}(a z+c_j-b_i)=f_{ij}(z)\). If \(a=1\), any nonzero offset \(c_j-b_i\) would force a constant block on the prime field; since there are no such blocks, all row and column offsets coincide. Such \(g\) belongs to \(P\).

If \(\alpha(g)\) for any \(g\in N\) has an odd prime factor \(\ell\) in its order, then \(\ell\in\{13,23\}\). Because \(Q_8\) has exponent four, \(g^4\in\ker\rho\), and its multiplier still has order divisible by \(\ell\). A further power, still in \(\ker\rho\), has multiplier of exact order \(\ell\). Each block is then invariant under an affine map of order \(\ell\) with one fixed point and all other orbits of size \(\ell\): translate the fixed point to zero and the action is multiplication by an element of order \(\ell\). Its row sum as an integer is thus congruent to \(+1\) or \(-1\) modulo \(2\ell\), because \(p-1\) is a multiple of \(2\ell\) and a constant sign is assigned to each \(\ell\)-orbit. The possible positive absolute row sums are \(\{1,25,27\}\) for \(\ell=13\), and \(\{1,45,47\}\) for \(\ell=23\). Neither set provides four squared entries summing to 2396. Thus \(\alpha(N)\subseteq\{1,-1\}\). The kernel of \((\rho,\alpha)\) is exactly \(P\), proving the injection. The simultaneous global sign \((-I,-I)\) maps to the central involution of the quaternion factor. In particular modulo both \(P\) and the global sign, the normalizer embeds in \(C_2^3\).

Finally, any element of \(\ker\rho\) outside \(P\) has multiplier \(-1\), and acts by reflections with positive signs within each row/column orbit. It has order two, conjugates \(P\) to its inverse, and fixes one position per orbit. Recenter the coordinates at these fixed positions. Each \(f_{ij}\) is then even, and its value at zero is \(-1\) if \(D_{ij}\equiv1\bmod4\) and \(+1\) if \(D_{ij}\equiv3\bmod4\): the remaining \(p-1=598\) positions occur in 299 equal-sign pairs. This entrywise sign rule is odd and commutes with row/column signed permutations and transpose. On a quaternion orbit-sum representative it simply replaces the four parameters by signs, giving a quaternion matrix of norm squared four. Hence the fixed \(4\times4\) submatrix is Hadamard.
