# Exact independence for centered Gaussian membership in sublattices

For a Euclidean lattice \(L\) of any rank and \(t>0\), give \(x\in L\) probability proportional to \(e^{-t\|x\|^2}\). The events considered here are \(x\in M\) for additive sublattices \(M\subseteq L\), including \(\{0\}\), proper full-rank groups, and \(L\). They are not affine coset events.

**Theorem.** Write the canonical orthogonal decomposition as \(L=\bigoplus_{i=1}^b L_i\) with indecomposable nonzero factors, and put \(S(M)=\{i:L_i\not\subseteq M\}\). For any \(M,N\subseteq L\), centered Gaussian membership in \(M\) and \(N\) is independent if and only if \(S(M)\cap S(N)=\varnothing\). Equivalently, there is an orthogonal lattice splitting \(L=A\oplus B\) with \(A\subseteq M\) and \(B\subseteq N\). If this fails, their covariance is strictly positive at every \(t>0\).

Consequently, pairwise independence of any finite family of centered sublattice memberships implies mutual independence. The pairwise hypotheses may even be checked at different widths, provided the underlying Euclidean inner product is the same. A subgroup may couple factors inside its own support; independence does **not** require each subgroup to be a product over individual indecomposable factors.

**Cyclotomic consequence.** Let \(K=\mathbb Q(\zeta_m)\), let \(L\subset K^r\) be a full \(\mathcal O_K\)-lattice under its real canonical embedding, and use any positive definite inner product for which multiplication by \(\zeta_m\) is isometric. This includes ordinary archimedean place weights and Hermitian positive definite metrics on the copy space within a place. The same characterization holds for \(\mathcal O_K\)-submodules with the real indecomposable factors aggregated into their \(\zeta_m\)-orbits. In fact the maximum size of a pairwise independent family of nontrivial submodule memberships is the number of orbit blocks, at most \(r\); for a nonzero fractional ideal (\(r=1\)), every pair of proper subideals has strictly positive membership covariance, at every centered width and every such metric.

This sharpens the inequality of [Regev–Stephens-Davidowitz, Proposition 4.3 and Theorem 5.1](https://arxiv.org/pdf/1502.04796), which does not state an equality classification. The proof uses the fixed companion [Gaussian shift equality lemma, Theorem part 1 and §§1–4](https://github.com/mxym/math/blob/b07a6b91c604765deaa01446a0e5f442b746e603/research/euclidean-tensor-geometry/theoretical-cryptography/lattice-gaussian-equality-kummer.md), where the parity-class equality is identified via the Kummer map. The [FKG equality theorem of Chan–Pak](https://arxiv.org/abs/2607.06275) concerns increasing functions on distributive lattices and does not supply an equality criterion for the arbitrary Euclidean subgroups or discrete-Gaussian law here. We make no claim of an exhaustive priority search. The scope is statistical structure of abstract centered Gaussian laws, not cryptographic security or an analysis of a deployed system.

## 1. Where equality can enter the coset argument

Write \(\rho(H+z)=\sum_{v\in H}e^{-t\|v+z\|^2}\) and \(f_H(z)=\rho(H+z)/\rho(H)\). For a sublattice \(H\), let \(W=\operatorname{span}_{\mathbb R}H\), let \(H=\bigoplus_j H_j\) be its orthogonal indecomposable decomposition, and use subscripts \(j,\perp\) for the projections onto \(\operatorname{span}H_j\) and \(W^\perp\), respectively. Then
\[
 \frac{f_H(x+y)+f_H(x-y)}2\ \geq\ f_H(x)f_H(y). \tag{1}
\]
There is equality precisely if
\[
 \langle x_\perp,y_\perp\rangle=0,\qquad
 \text{for each }j,\quad x_j\in H_j\ \text{or}\ y_j\in H_j. \tag{2}
\]
Indeed, Eq. (4c) of Regev–Stephens-Davidowitz is AM–GM followed by the square root of their main shift inequality. The perpendicular exponential factors cancel from the main product equality by the parallelogram identity, so the companion shift lemma gives the conditions on the \(j\) components, also when the rank is zero (empty list). Under those conditions, evenness and lattice periodicity yield \(f_{H_j}(x_j+y_j)=f_{H_j}(x_j-y_j)\) for each \(j\). The remaining AM–GM equality then says exactly \(\|x_\perp+y_\perp\|^2=\|x_\perp-y_\perp\|^2\), proving (2).

For \(H\subseteq N\), the coset decomposition and inversion on \(N/H\) give
\[
 f_N(x)-f_H(x)=
 \frac{\sum_{y\in N/H}
   [\,\{f_H(x+y)+f_H(x-y)\}/2-f_H(x)f_H(y)\,]}
      {\sum_{y\in N/H}f_H(y)}. \tag{3}
\]
The summands are independent of representatives. All positive sums before subtraction are finite because they are Gaussian sums over non-repeated cosets of a lattice, even if the quotient is infinite. Each bracket is nonnegative. Hence (3) vanishes if and only if (2) holds for every \(y\in N\). Equivalently \(x_\perp\perp \operatorname{proj}_{W^\perp}N\), and for each \(j\) either \(x_j\in H_j\) or \(\operatorname{proj}_{\operatorname{span}H_j}N\subseteq H_j\).

Now put \(H=M\cap N\). Inject \(M/H\) into \(L/N\), obtaining the proof of the original correlation inequality:
\[
 \frac{\rho(L)}{\rho(N)}
 \ \geq\ \sum_{x\in M/H} f_N(x)
 \ \geq\ \sum_{x\in M/H} f_H(x)
 \ =\ \frac{\rho(M)}{\rho(H)}. \tag{4}
\]
Equality in the first comparison requires and suffices that \(L=M+N\), because every omitted coset contributes positive mass. Equality in the second comparison requires and suffices that (3) vanish for every \(x\in M/H\). Adding an element of \(H\) does not affect the conditions (2), so this gives
\[
 \operatorname{proj}_{W^\perp}M \perp \operatorname{proj}_{W^\perp}N,\qquad
 \text{for each }j,\quad P_j M\subseteq H_j\ \text{or}\ P_j N\subseteq H_j, \tag{5}
\]
where \(P_j\) is projection onto \(\operatorname{span}H_j\). Orthogonality of sets in (5) means every pair of their elements is orthogonal. Statements (4)–(5) are exact at any single \(t>0\).

## 2. From the intersection back to orthogonal blocks of the ambient lattice

Give \(j\) to group \(U\) if \(P_j M\not\subseteq H_j\), to group \(V\) if \(P_j N\not\subseteq H_j\), and to group \(T\) otherwise. The groups are disjoint by (5). Set \(H_U=\bigoplus_{j\in U}H_j\), and similarly \(H_V,H_T\). If one of the projections of a subgroup is contained in \(H_j\), it can be removed integrally because \(H_j\) itself is contained in that subgroup. Thus
\[
 M=M_U\oplus H_V\oplus H_T,\qquad N=H_U\oplus N_V\oplus H_T,
\]
where \(H_U\subseteq M_U\) and \(H_V\subseteq N_V\). Here \(M_U\) is the subgroup of \(M\) with zero \(V,T\) projections, and \(N_V\) is defined by zero \(U,T\) projections in \(N\). The \(M_U\) subgroup lies in the sum of the \(U\)-factor spans and the real span of \(\operatorname{proj}_{W^\perp}M\); \(N_V\) lies in the analogous \(V\) space for \(N\). These spaces and \(\operatorname{span}H_T\) are mutually orthogonal by (5). Since \(L=M+N\), we obtain
\[
 L=M_U\oplus N_V\oplus H_T.
\]
Take \(A=M_U\oplus H_T\subseteq M\) and \(B=N_V\subseteq N\). Conversely, if \(L=A\oplus B\) with these inclusions, then \(M=A\oplus(M\cap B)\), \(N=(N\cap A)\oplus B\). The two membership indicators depend on disjoint independent components of the Gaussian sample.

For completeness the uniqueness of the orthogonal decomposition follows from a short lattice argument of Kneser type. Call a nonzero vector unsplittable if it cannot be written \(v=y+z\) with nonzero lattice \(y,z\) and \(\langle y,z\rangle\geq0\). Each \(y,z\) in such a splitting has smaller norm than \(v\); discreteness in bounded balls gives by induction that unsplittable vectors generate \(L\). Any orthogonal decomposition places each unsplittable vector entirely in a single factor. Connect two unsplittable vectors whenever their inner product is nonzero. Their graph components generate mutually orthogonal subgroups whose direct sum is \(L\). A component cannot split orthogonally, since each generator must lie in one side and no edge can cross. Thus these are intrinsic factors, and any orthogonal splitting is a grouping of them. This proves that \(A\subseteq M, B\subseteq N\) is equivalent to at least one of \(M,N\) containing each \(L_i\). The argument also covers rank zero with an empty decomposition.

For a family \(M_1,\ldots,M_p\), each subgroup has the form
\[
 M_a=\left(M_a\cap\bigoplus_{i\in S(M_a)}L_i\right)
       \oplus\bigoplus_{i\notin S(M_a)}L_i.
\]
Disjoint pairwise supports now give independent blocks for all \(p\) indicators. This remains true if pairwise independence was detected at different positive widths, since the criterion does not contain \(t\). As a simple example on \(\mathbb Z^4\), the conditions \(x_1+x_2\) even, \(x_3=0\bmod 3\), and \(x_4=0\bmod 5\) are mutually independent under the standard centered Gaussian. The first subgroup is not an orthogonal product of the first two one-dimensional lattice factors.

## 3. Cyclotomic modules and conditioning

Multiplication by \(\zeta_m\) is an isometry of \(L\), so it permutes the canonical indecomposable factors. Partition the factors into orbits \(\mathcal O_1,\ldots,\mathcal O_d\). Each orbit sum \(L(\mathcal O_a)\) is stable under \(\mathbb Z[\zeta_m]=\mathcal O_K\). Its rational span is nonzero and is stable under multiplication by the field generated by \(\zeta_m\), so it is a \(K\)-subspace of \(K^r\). The orbit sums form a direct sum on rational spans. Thus \(d\leq r\). A submodule that contains one factor in an orbit contains them all, by repeated multiplication by the root of unity. Every proper submodule has a nonempty support consisting of whole orbits. In any orthogonal splitting into \(\mathcal O_K\)-submodules, every block is a union of real indecomposable factors and is invariant under \(\zeta_m\); hence each block is a union of whole orbits. The orbit sums are therefore also the indecomposable blocks in the category of \(\mathcal O_K\)-modules. Nontrivial independent submodule events have disjoint nonempty orbit supports, so there are at most \(d\) of them. This is attained by \(d\) events, each requiring that its own orbit coordinate lie in \(2L(\mathcal O_a)\), and leaving all other orbit coordinates unrestricted. For \(r=1\) this also gives the strict ideal statement.

The rank-one strict statement continues to hold after conditioning on any finite intersection of nonzero ideal memberships, whenever both tested membership conditions restrict that intersection properly. That intersection of nonzero fractional subideals is a nonzero fractional ideal, and the conditional law is its centered Gaussian, since restriction only changes the partition function. This does not extend the statement to conditioning on unions, complements, or shifted cosets.

## 4. Uniform gap at fixed geometry; exact loci as the metric varies

For a fixed Euclidean lattice and compact precision interval \(0<t_0\leq t\leq t_1<\infty\), there exists \(\delta>0\) such that **all** dependent pairs of sublattice memberships have covariance at least \(\delta\) on this interval, regardless of index or rank. The assertion is vacuous if no dependent pairs exist. Indeed, the space of all subgroups of \(L\) is a closed subset of the compact product \(\{0,1\}^L\): containing zero and closure under subtraction are enforced by closed finite-coordinate conditions. For each \(i\), whether \(L_i\subseteq M\) is a clopen condition on \(M\), since one need only test any fixed finite basis of \(L_i\). Thus the space of dependent pairs is compact by the theorem. Their covariance is continuous jointly in the pair and \(t\), by uniform summability of lattice weights at \(t_0\) and by the denominator being at least one. The positive minimum follows. No dimension-uniform or explicit constant is asserted.

In lattice coordinates \(L=\mathbb Z^n\), let the weight be \(e^{-x^\top Qx}\), where \(Q\) varies over positive definite forms. For fixed \(M,N\), the set of exact independence is the union over integral idempotents \(E\) satisfying \(E L\subseteq M\) and \((I-E)L\subseteq N\) of
\[
 \{Q\succ0: QE=E^\top Q\}.
\]
An integral idempotent gives the lattice direct sum of its image and the image of \(I-E\), and the displayed self-adjointness is exactly mutual \(Q\)-orthogonality of those images. For any compact set of \(Q\)'s, write \(aI\preceq Q\preceq bI\) with \(a>0\); any contributing projection satisfies \(\|E\|_{2\to2}\leq\sqrt{b/a}\) because it is a contraction in the \(Q\)-norm. So only finitely many integral \(E\) participate on that compact set. If \(M,N\) are both proper, every relevant \(E\) has \(0<\operatorname{rank}E<n\), and its orthogonality locus is a proper linear section in the space of symmetric forms (cross-block entries must be zero). Outside a locally finite union of proper linear sections, \(Q\) therefore gives strict covariance for all proper subgroups simultaneously. This metric statement does not imply a gap uniform across metrics approaching one of the independence loci.

## Reproduction

Run `python3 verify-lattice-sublattice-independence.py` using only the Python standard library. It enumerates integral orthogonal projections in small examples, checks the structural criterion against rigorous rational intervals for the terms of the correlation numerator, checks a coupled three-event product, and verifies the rank-one cyclotomic prediction on small rotation-invariant subgroups. These finite checks illustrate, rather than prove, the full theorem or its Kummer input.
