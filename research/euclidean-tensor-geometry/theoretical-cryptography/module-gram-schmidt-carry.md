# A rank-independent Gram–Schmidt bound with one-position delay for module bases

For a fixed number field, the ideal class group can prevent an ordinary free basis from following even the first successive independent-vector minimum. Nevertheless it need not cause a growing distortion in the **orthogonalized** lengths: one position of delay suffices, with a constant depending only on the field, not on the module rank. This is a geometric existence result, not a method for finding short vectors or solving a learning problem.

## 1. Statement and normalization

Let \(K\) be a number field of degree \(d\) and \(R=\mathcal O_K\). At a real place use its Euclidean norm, at a complex place its Hermitian norm; summing the squared place norms with weights \(1,2\), respectively, gives the canonical squared norm. Let \(M\subset K^m\) be a finitely generated torsion-free \(R\)-module of rank \(r\). Let \(\ell_i(M)\) be the least canonical radius containing \(i\) vectors of \(M\) independent over \(K\).

For ordered vectors \(b_1,\ldots,b_r\) independent over \(K\), write \(b_i^*\) for the canonical orthogonal projection of \(b_i\) away from the real extension of the \(K\)-span of its predecessors. This is **block, placewise** Gram–Schmidt: all scalar multiples in \(K_{\mathbb R}\) of each predecessor are removed, rather than just its one-dimensional real line.

**Theorem.** For every fixed \(K\) there is a finite \(C_K\) with the following property, simultaneously for all \(r,m,M\). Choose once and for all one integral ideal representing each class, using \(R\) for the trivial class. There is a pseudo-basis
\[
        M=Rb_1\oplus\cdots\oplus Rb_{r-1}\oplus A b_r ,
\]
where \(A\) is the chosen representative of the Steinitz class of \(M\), and
\[
    \|b_i^*\|\le C_K\ell_{\min(i+1,r)}(M)
         \qquad(1\le i\le r).                               \tag{1}
\]
When \(M\) is free, \(A=R\) and this is an ordinary integral basis. For free \(M\), further size reduction gives the same orthogonal components and
\[
 \|b_i\|\le C_K\sqrt{1+(i-1)\kappa_R^2}\,
                         \ell_{\min(i+1,r)}(M),             \tag{2}
\]
where \(\kappa_R\) is the covering radius of \(R\) in \(K_{\mathbb R}\) measured by the maximum absolute value over places. Over any fixed \(K\), the resulting \(O_K(\sqrt r)\) worst-rank scale in the comparison of the longest ordinary basis vector to \(\ell_r\) is necessary. With no delay in (1), a uniform bound over all free modules and all ranks holds if and only if the class group is trivial, even if the constant were allowed to depend on rank.

Evertse's classical almost-basis theorem already supplies the one-position shift for ordinary lengths, with a rank-dependent factor. The new quantitative point here is the rank-independent bound for all block G–S components, and consequently the order-sharp rank factor for maximum ordinary length.

## 2. Normalize short successive quotient generators

For each \(i\) choose \(v_i\in M\) of norm at most \(\ell_i(M)\) independent of \(v_1,\dots,v_{i-1}\). This is possible by the definition of the minimum; the minima are attained since the embedded module is an additive discrete lattice. Let \(V_i=\operatorname{span}_K(v_1,\ldots,v_i)\) and \(M_i=M\cap V_i\), with \(M_0=0\). The quotient \(M_i/M_{i-1}\) is rank one and torsion-free, hence projective over the Dedekind domain \(R\), and is isomorphic to one chosen representative \(I_i\). A splitting yields a vector \(x_i\in V_i\) with
\[
                   M_i=M_{i-1}\oplus I_i x_i .
\]
Here the image of any \(R\)-linear map from a fractional ideal into \(K^m\) is scalar multiplication by a single vector, by extending to \(K\). Write \(p_i\) for the projection of \(x_i\) perpendicular to \((V_{i-1})_{\mathbb R}\). At every place this is a nonzero vector since \(x_i\notin V_{i-1}\) and an embedding preserves the rank of a matrix over \(K\).

The nonzero class of \(v_i\) in the quotient gives \(\pi_i(v_i)=a_i p_i\) for some \(a_i\in I_i\setminus\{0\}\). Every \(I_i\) is integral, so \(|\operatorname{Nm}(a_i)|\ge1\). By the unit log lattice, there is a constant \(\alpha_K\ge1\) such that for each such \(a_i\) one can choose a unit \(u_i\) with \(|u_i|_v\le\alpha_K|a_i|_v\) for every place. Indeed, remove the weighted average \(\log|\operatorname{Nm}(a_i)|/d\) from the log absolute values and approximate the result by the log of a unit within the fixed maximum-norm covering radius of the unit lattice in the zero-sum hyperplane. Replacing \(x_i\) by \(u_i x_i\) leaves the summand \(I_i x_i\) unchanged and makes, placewise,
\[
              \|p_i\|_v\le\alpha_K\|\pi_i(v_i)\|_v,\qquad
              \|p_i\|\le\alpha_K\ell_i(M).                  \tag{3}
\]
No relationship between the components of \(x_i\) *inside* \(V_{i-1}\) is required.

## 3. Carry the class without carrying its accumulated geometric error

The algebra in this step is the usual two-summand Steinitz isomorphism. We choose its coefficients from a finite table and use a geometric adjustment to avoid exponential amplification as the process is repeated.

For each ordered pair \(A,I\) of fixed ideal representatives, let \(A'\) represent the product class. Fix an invertible \(2\times2\) matrix \(P_{A,I}\) over \(K\) with columns \((a,b)^\mathsf T\), \((a',b')^\mathsf T\) satisfying
\[
 A\oplus I=R(a,b)^\mathsf T \oplus A'(a',b')^\mathsf T .     \tag{4}
\]
Existence is Steinitz's theorem and rescaling the last ideal to its fixed representative. Assume \(b\ne0\): if necessary add a nonzero \(A'\)-multiple of the second column to the free first column. This preserves (4), and if \(b=0\), invertibility makes \(b'\ne0\). Across this finite table all absolute values of entries, and all \(|\det P_{A,I}|_v/|b|_v\), are bounded by constants depending only on \(K\) and the fixed choices.

Inductively suppose that
\[
 M_{i-1}=Rb_1\oplus\cdots\oplus Rb_{i-2}\oplus A w,\qquad i\ge2,
\]
where \(A\) is a fixed representative, and \(w\) is the current last vector. Let \(W\) be the \(K\)-span of the displayed \(i-2\) free vectors. In the complement of \(W_{\mathbb R}\), the two relevant projected vectors are \(w_\perp\) and \(\gamma w_\perp+p_i\), with \(\gamma\in K_{\mathbb R}\) and \(p_i\perp w_\perp\). This expression follows from \(V_{i-1}=W\oplus K w\) and the definition of \(p_i\).

Before applying (4), replace \(x_i\) by \(x_i-\beta w\) for a suitable \(\beta\in A I_i^{-1}\). The total module and \(p_i\) stay the same, since \(\beta I_i\subseteq A\). Using the maximum-norm covering radius of the fractional ideal \(A I_i^{-1}\), first make all \(|\gamma_v|\le\kappa\), where \(\kappa\) is bounded over the finite table. Then add to the resulting \(\gamma\) a fixed positive integer from \(A I_i^{-1}\) so large that
\[
                    |a/b+\gamma|_v\ge1                     \tag{5}
\]
at all places. Such an integer exists since a nonzero fractional ideal contains a nonzero integer and its positive multiples. The final \(|\gamma_v|\) is still uniformly bounded by a field-only constant, because there are finitely many \(A,I_i,P_{A,I_i}\). The bounded translation, rather than ordinary nearest size reduction alone, is used to protect the old carry in (5).

Apply (4) to the coordinates \((w,x_i)\), renaming its free vector \(b_{i-1}=a w+b x_i\) and its last vector \(w'=a'w+b'x_i\). In the complement of \(W_{\mathbb R}\), the new free vector has projection
\[
            f=(a+b\gamma)w_\perp+b p_i.
\]
Orthogonality and (5) give \(\|f\|_v\ge |b|_v\|w_\perp\|_v>0\). The two-dimensional exterior area at a place changes by \(|\det P_{A,I_i}|_v\); this uses the Euclidean wedge norm over a real place and the Hermitian wedge norm over a complex place. Its original value is \(\|w_\perp\|_v\|p_i\|_v\), since the added \(\gamma w_\perp\) does not change it. Dividing the new area by \(\|f\|_v\) shows that the new last vector, projected away from \(W+K b_{i-1}\), has norm at most
\[
          \frac{|\det P_{A,I_i}|_v}{|b|_v}\|p_i\|_v.        \tag{6}
\]
In particular the bound for the new last projection depends only on \(p_i\), not on the old carry; it resets at each step. Meanwhile the triangle inequality and the bounded coefficients give \(\|f\|\le C(\|w_\perp\|+\|p_i\|)\) for a fixed field-only \(C\).

Start the induction with \(M_1=I_1x_1\) and \(w=x_1\), whose projection is \(p_1\). By (3) and (6), at the beginning of step \(i\) the old projected last vector has norm \(O_K(\ell_{i-1}(M))\); the new free vector has orthogonal component \(f\) of norm \(O_K(\ell_i(M))\). The final last vector has orthogonal component \(O_K(\ell_r(M))\). The last ideal at every step represents the class of \(M_i\), by (4), so the final one is as asserted. The rank-one case is just (3). This proves (1).

For a free module, ordinary descending size reduction by \(R\)-multiples of earlier \(b_j\)'s leaves all the G–S components unchanged. At step \(i\), reduce each scalar on the \(b_j^*\)-line, in descending \(j<i\), into a representative of maximum absolute value at most \(\kappa_R\) modulo \(R\). Descending order works because \(b_j\) has no component beyond its own index. Then
\[
 \|b_i\|^2\le\|b_i^*\|^2+\kappa_R^2\sum_{j<i}\|b_j^*\|^2,
\]
which with (1) and the ordering of the minima proves (2).

## 4. Both obstructions are genuine

**Zero delay.** If the class group is trivial, all \(I_i\) in Section 2 are \(R\), so the original normalized splitting already gives an ordinary basis with \(\|x_i^*\|\le\alpha_K\ell_i\), with no delay. Conversely suppose \(I\) is a nonprincipal fractional ideal and \(J=I^{-1}\). The rank-two module \(I\oplus J\) is free by Steinitz's theorem. Realize it as the canonical module \((\tau^{-1}I)\oplus(\tau J)\subset K^2\) for positive rational \(\tau\to\infty\), so the short and long axes have the indicated factors. No vector on its first axis belongs to an \(R\)-basis: a free basis vector must be sent to 1 by some \(R\)-linear functional to \(R\), but the restriction of such a functional to \(I\) is multiplication by a scalar in \(I^{-1}\), and this property for a vector in \(I\) would make \(I\) principal. Any first basis vector therefore has norm at least \(\tau\) times the shortest nonzero norm of \(J\). But \(\ell_1(M)\) is at most \(\tau^{-1}\) times the shortest nonzero norm of \(I\). The first orthogonal component equals that first vector, so the no-delay ratio diverges already at rank two. See also the [previous entry-by-entry obstruction](module-minima-free-basis.md) for exact rank-two ordinary lengths and an example in a fixed cyclotomic field.

**The \(\sqrt r\) scale for ordinary lengths.** For each \(r\ge2\) let
\[
 M^{(r)}=R^r+R\,\frac{(1,\ldots,1)}2 .
\]
This is free: the first \(r-1\) standard coordinate vectors and \((1,\ldots,1)/2\) form an \(R\)-basis, since twice the latter minus the others is the last standard coordinate vector. The standard vectors in \(R^r\) show \(\ell_r(M^{(r)})\le\sqrt d\). Put
\[
 \delta_K=\min\{\|x\|: x\in\tfrac12R\setminus R\}>0
\]
using the canonical scalar norm. The set is nonempty and discrete; \(\tfrac12\notin R\). In every vector of \(M^{(r)}\setminus R^r\), all \(r\) coordinates lie in the same nonzero class of \((\tfrac12R)/R\), so the norm is at least \(\delta_K\sqrt r\). Some vector of every \(R\)-basis lies outside \(R^r\), otherwise the whole module it generates lies inside \(R^r\). Thus the max ordinary basis norm divided by \(\ell_r\) is at least \((\delta_K/\sqrt d)\sqrt r\) for this family, for every fixed \(K\).

For clarity, the bounded Gram–Schmidt claim (1) is stronger than the ordinary vector bound in the direction relevant to block projections; the lower bound in the last paragraph is not a lower bound of order \(\sqrt r\) on Gram–Schmidt lengths. In the natural expansion of a pseudo-basis into a \(\mathbb Z\)-basis, choose a fixed integral basis of each coefficient ideal (there are finitely many) and order the expansion by blocks \(I_i b_i\). Orthogonalizing against all earlier blocks removes exactly the prior real-extended \(K\)-span, leaving the corresponding multiples of \(b_i^*\); orthogonalizing further within the block can only decrease the length. Thus the block-compatible ordinary Euclidean G–S lengths inherit (1) up to a field-only factor. This does not assert a new sampling or lattice-reduction algorithm.

## 5. Prior scope and replay

[Evertse, *Reduced Bases of Lattices over Number Fields*, Corollary 2, printed pp. 158–159](https://doi.org/10.1016/0019-3577(92)90003-4) already proves an almost-basis bound with \(\ell_{i+1}\) (in a general product-convex-body setting), with an explicit rank-dependent bound of exponential form. The one-position shift itself is not new. [Fieker–Stehlé, *Short Bases of Lattices over Number Fields*, Theorem 6 and §4.3](https://perso.ens-lyon.fr/damien.stehle/downloads/OKLatRed.pdf) give short pseudo-bases and the algebraic procedure combining two coefficient ideals into a free part and a remaining ideal, also citing the position relation to Evertse. Our two-summand identity (4) is this classical algebra. The additional argument is the local projected-area estimate (6), forcing the new carry to track the *fresh projected component* with no accumulating rank-dependent factor. The ordinary-length bound then follows by size reduction, and is sharp in its maximal rank order as in Section 4. We do not improve the complexity of those primary algorithms, or the quantitative field dependence.

[Langlois–Stehlé, *Worst-Case to Average-Case Reductions for Module Lattices*](https://perso.ens-lyon.fr/damien.stehle/downloads/MSIS.pdf) distinguish a module lattice from its underlying Euclidean lattice. The theorem is about comparing their geometries under a module-compatible basis choice. It is not a claim about modified hardness, secret recovery, or an actual sampler.

Run `python3 verify-module-gram-schmidt-carry.py` to replay exact quadratic-field transition, wedge and lower-bound checks on generated arithmetic. The analytic proof is independent of these examples.
