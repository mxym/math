# Perpendicular-class balance in the combined norm-\(22/7\) shell

Let \(L\) be the even rank-44 graph lattice on the rank-42 case, \(D=L^*/L\) its anisotropic seven-plane, and \(a_j(\alpha)=\#\{x\in L^*: [x]=\alpha,\ 7(x,x)=2j\}\). On the rank-42 two-selected-type face (norm eighteen and norm twenty-four), the following holds:
\[
a_j(\alpha)=a_j(i\alpha)\quad\text{for every \(j\) and every \(\alpha\),}
\]
where \(i\) is a norm-one quarter-turn of \(D\). This does not assert equality between the two different perpendicular pairs within a norm circle. In particular
\[
N_{22}(\alpha)+G_{3,33}(\alpha)+G_{3,33}(-\alpha)
=
N_{22}(i\alpha)+G_{3,33}(i\alpha)+G_{3,33}(-i\alpha).
\]
Here \(G_{3,33}\) counts actual fields in the positive charge-three sector, not the projected normalization obtained by dividing a total by eight. The total number of oriented neutral norm-22 fields is divisible by four.

## Modular lemma and dimension

Use \(q_7=\exp(2\pi i\tau/7)\). After an isometry write \(D=\mathbb F_7^2\) with finite quadratic form \(q(\alpha)=\frac17\big((a^2+b^2)/2\bmod 7\big)\bmod\mathbb Z\), where division by two inside the parentheses is in \(\mathbb F_7\). Let \(g=2+2i\in\mathbb F_{49}\), \(i^2=-1\); then \(g^2=i\). Torus rotations commute with the Weil \(T,S\), and on the even coefficient space \(i^2=-1\) acts trivially. The projector \((1-i)/2\) on that space is the sum of the order-four character spaces \(g\mapsto\pm\sqrt{-1}\); call this 12-dimensional space \(V\). On each norm circle there are two \(i\)-orbits, each of size four, and a projected coefficient alternates sign around each orbit.

The two six-dimensional summands of \(V\) are irreducible. On each one the \(T\) eigenvalues are distinct, indexed by the six nonzero norms. The \(S\) entry between two circles is a nonzero scalar times
\(\sum_{k=0}^7 (\pm \sqrt{-1})^k\zeta_7^{\langle x,g^k y\rangle}\) for fixed circle representatives. The companion checker verifies directly, for all 36 pairs of norms, that the seven grouped coefficients in \(\mathbb{Z}[\sqrt{-1}]\) are not all equal. Their discrete Fourier sum at \(\zeta_7\) is therefore nonzero by the minimal polynomial \(1+X+\cdots+X^6\) over \(\mathbb Q(\sqrt{-1})\); this also holds for a nonzero scalar multiple in the exponent, a change of sign convention, and the conjugate order-four character. A \(T\)-invariant submodule has a coordinate eigenspace, and applying \(S\) and the \(T\)-projections gives all six. This proves irreducibility.

Any weight-22 modular form with Weil values in \(V\) vanishing at infinity through \(q_7^{11}\) is zero. To see this, the level-seven Weil action factors through \(\mathrm{SL}_2(7)\); here the even coefficient space and the even weight allow descent to \(G=\mathrm{PSL}_2(7)\). Every component is a scalar form on \(\Gamma(7)\), and every translated component has order at least 12 at infinity, so the scalar components vanish to this order at every cusp. The torsion-free modular curve \(X(7)\) has genus 3 and 24 cusps of width seven; the weight-one line has degree 14, as the form \(\Delta\) vanishes with order seven at every cusp and nowhere else. The scalar weight-22 space vanishing to order 12 everywhere has degree \(22\cdot14-12\cdot24=20\), hence dimension 18 by Riemann--Roch. The subspace with order 13 has degree \(-4\) and is zero. The leading cusp coefficients thus embed this 18-dimensional representation into \(\operatorname{Ind}_{\langle T\rangle}^{G}\xi\), where \(\xi\) is the nontrivial cusp parameter character at order 12 (or its inverse).

The usual \(\mathrm{PSL}_2(7)\) character table, for example in [Elkies, *The Klein Quartic in Number Theory*](https://library.slmath.org/books/Book35/files/elkies.pdf), shows that this induced representation is multiplicity-free with dimensions \(3,6,7,8\): the \(6,7,8\) contain each nontrivial seven-cycle character once, and the two 3-dimensional irreducibles split those characters between them. The only possible 6-dimensional complement of the embedded 18-dimensional subspace is the 6-dimensional irreducible. Thus the embedded subspace contains no 6-dimensional constituent, so no components of a \(V\)-valued modular form can lie there nontrivially. Accordingly the initial coefficient map through \(j=11\) on \(M_{22}(V)\) is injective. There are ten nonzero residues among these positive indices and two projected coordinates at each, so \(\dim M_{22}(V)\le20\).

## The two independent coefficient checks

The exact companion `rank42_even_weil_q11.py` constructs genuine \(V\)-valued modular forms from the even rank-four auxiliary lattice with Gram
\[
\begin{pmatrix}2&1\\1&4\end{pmatrix}\oplus
\begin{pmatrix}2&1\\1&4\end{pmatrix}.
\]
Its discriminant form and signature modulo eight agree with those of the graph lattice. In dual pairing coordinates \((w,x,y,z)\in\mathbb Z^4\) the exponent is \(j=2w^2-wx+x^2+2y^2-yz+z^2\), with discriminant coordinates \(5(w+5x),5(y+5z)\) modulo seven, whose squared sum is \(2j\). The search bounds on each pairing coordinate follow from \(|(v,e_\ell)|^2\le(v,v)(e_\ell,e_\ell)\). It projects even harmonic theta coefficients, uses ordinary modular multiplication and the Serre derivative in exact rational arithmetic, and finally divides by \(\Delta\) only after all projected coefficients of exponent \(j<7\) vanish. This last division is holomorphic at every cusp by the same translation argument, and within the upper half-plane because \(\Delta\) has no zeros there. At weight 22 the constructed forms have rank 20, hence span by the upper bound just proved. The subspace cut out by \(j<11\) has dimension two; with the additional condition that both projected coordinates at \(j=12\) vanish it has dimension zero. All these ranks use a finite expansion to \(j=16\), or \(j=23\) before division.

## Application to actual marked fields

For the actual theta of \(L\), the order-four projection has zero constant and zero coefficients through \(j=8\): below the graph minimum there are no vectors, the zero residue is annihilated, and norm 16 is absent. At \(j=9\), the [rank-42 fixed-extension projective-class balance](two-type-residue-balance.md) for \(N_{18}\) makes the projection zero. At \(j=10\) the whole coefficient is zero. At \(j=12\), the same published fixed-extension class balance separately applies to \(N_{24}\) and the projectively counted charge-\(3\), raw-cost-\(35\) fields, so the combined scalar coefficient again has zero projection. When other charge representatives are possible at these lengths, one uses the original integer charge dictionary: for an original theta index \(j\), the only folds are \(a=0\) with raw norm \(2j\) and \(a=\pm3\) with raw cost \(2j+11\); the affine minimums exclude the shorter charge-three terms. The projected theta satisfies the two verified finite conditions, hence vanishes identically.

At index 11, rotation balance and antipodality make the total \(N_{22}+2G_{3,33}\) a multiple of four. The [true-Hoffman scalar relation](norm22-johnson-positive-mass.md) \(G_{3,33}=N_{22}+8(43-n)\) and orientation of \(N_{22}\) make \(G_{3,33}\) even, so \(4\mid N_{22}\). This improves the third Johnson lower bound for \(N_{22}\) from 146 to 148, and its corresponding raw cost-33 floor from 74 to 76. The four surviving population tuples are not excluded.
