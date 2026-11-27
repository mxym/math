# Sharp Gaussian mass through rank 55 and in even rank 72

**Theorem.** For every positive-definite integral unimodular lattice \(L\) of rank \(n\le55\) and every \(t>0\),
\[
\Theta_L(t)=\sum_{x\in L}e^{-t|x|^2}\le\Theta_{\mathbb Z^n}(t),
\]
with equality only for \(L\cong\mathbb Z^n\). For every even unimodular lattice of positive rank at most 72, the comparison is strict.

[Kominers](https://arxiv.org/abs/2606.01347) proved the comparison through rank 32 and in even rank 40. The [earlier rank 41/64 comparison](unimodular-gaussian-mass-rank-41-64.md) extended those ranges to 41 and 64 using exceptional root-neighbor caps. This continuation proves odd ranks 42–55 and even rank 72. The main new inputs are a comparison via the glue of a \(D_r\) root component, a signed spherical bound on a **single shadow coset**, and an \(A_r\)-projection count when the root component is too large for a dimension-only bound. This does not address nonintegral stable lattices or all ranks.

## 1. A large \(D_r\) component can be removed by gluing

Suppose \(L\) has no norm-one vectors and contains a root component \(R=D_r\) with \(r\ge8\). Assume the Gaussian comparison holds for every integral unimodular lattice of rank \(n-r\) (with the convention 1 in rank zero). Then \(L\) satisfies the strict comparison.

If \(R\) is not primitive, put \(R'=L\cap\operatorname{span}R\). The dual \(D_r^*\) has two integer cosets and two half-coordinate cosets modulo \(D_r\). The nontrivial integer coset cannot occur in \(R'\) because it would contain a norm-one vector. Both half cosets cannot occur simultaneously since their sum or difference would give the integer coset. Thus the extension has index two and is unimodular, and one half-coordinate coset was added. Orthogonal projection of \(L\) to this unimodular \(R'\) lands in \(R'\), so \(L=R'\oplus K'\) with \(K'\) integral unimodular of rank \(n-r\). The theta function of \(R'\) is \((\vartheta_3^r+\vartheta_4^r+\vartheta_2^r)/2\). Jacobi's identity \(\vartheta_4^4+\vartheta_2^4=\vartheta_3^4\) gives this strictly smaller than \(\vartheta_3^r\) for \(r\ge8\).

If \(R\) is primitive, put \(K=L\cap(\operatorname{span}R)^\perp\). The integral dual gives a bijection between \(R^*/R\) and \(K^*/K\) induced by the glue: projection to \(R^*\) is surjective because homomorphisms on the primitive \(R\) extend to \(L\) and \(L=L^*\); projection to \(K^*\) is similarly surjective; and the kernel of either projection modulo the component is \(R\oplus K\). Hence \(K\) has determinant 4. Let \(b\in K^*/K\) be paired with the odd integer coset of \(D_r\). It has order two and integral squared norm modulo one (the glued lattice is integral and \(e_1^2=1\)). Thus \(K'=K\cup(K+b)\) is integral unimodular. Write \(s,c\) for the other two cosets paired with the half-coordinate cosets. Separating the four sums gives
\[
\frac{\Theta_L}{\vartheta_3^r}
=\frac{1+p}{2}\Theta_K+\frac{1-p}{2}\Theta_{K+b}
+\frac{q'}2\bigl(\Theta_{K+s}+\Theta_{K+c}\bigr),
\quad
p=(\vartheta_4/\vartheta_3)^r,\quad q'=(\vartheta_2/\vartheta_3)^r.
\]
Every shifted theta sum here is bounded above by \(\Theta_K\), by the nonnegative Poisson Fourier series. The full normalized comparison is invariant under the Gaussian modular inversion because \(L,\mathbb Z^n\) are self-dual. This inversion interchanges \(\vartheta_2/\vartheta_3\) with \(\vartheta_4/\vartheta_3\), so restrict to \(\alpha=(\vartheta_2/\vartheta_3)^4\le1/2\). Then \(q'=\alpha^{r/4}\le\alpha/2<(1-p)/2\), since \(p=(1-\alpha)^{r/4}\). The displayed formula is strictly less than \(\Theta_K+\Theta_{K+b}=\Theta_{K'}\), which is bounded by \(\vartheta_3^{n-r}\). This proves the claim.

In ranks 42–55 we can therefore remove any \(D_r\) with \(r\ge n-32\) using Kominers's theorem. In the remaining lattices the maximum root Coxeter number \(h\) is at most \(n+1\): the \(A_r\) components have \(h=r+1\); the remaining \(D_r\) have \(h=2(r-1)\le2n-68\); the exceptional types have \(h\le30\). We always have \(N_2\le nh\) for the norm-two count, by summing the ADE component counts. In rank 72 the new rank-through-55 bound lets us remove every \(D_r\) with \(r\ge18\); this sufficient cutoff will be used below.

## 2. Spherical angle and projection bounds

The usual normalized Gegenbauer polynomials \(Q_j^{(n)}\) obey \(Q_0=1,Q_1=x\) and
\((j+n-2)Q_{j+1}=(2j+n-2)xQ_j-jQ_{j-1}\). The addition theorem makes them positive semidefinite kernels (see [Delsarte–Goethals–Seidel, §4](https://doi.org/10.1007/BF03187604)). If \(F=1+\sum_j c_jQ_j\), \(c_j\ge0\), is nonpositive on the allowed off-diagonal angles except one value \(x_0\), with at most \(d_0\) neighbors per vector there, the normalized spherical set has size at most \(F(1)+d_0\max(0,F(x_0))\). Sum the kernel over all ordered pairs to see this. If using one representative per antipodal line, use only even \(Q_j\).

For a shell of squared norm \(a\) with differences in \(L\), the inner product \(a-1\) is a root adjacency: \(x-y\) is a root and \(\langle x,x-y\rangle=1\). Its degree is at most \(ha\); the same applies to an absolute inner product when one can orient \(y\). Indeed in a root component the sum of root outer products is \(2h_i\) times the orthogonal projector (irreducibility and trace), so \(\sum_{\alpha\in R}\langle x,\alpha\rangle^2\le2h|x|^2\), and roots with product 1 have their negatives as well.

**A separate bound in a large \(A_r\) component.** Let an even-norm lattice shell or an odd-lattice shadow shell have squared norm \(a\), and take an \(A_r\) root component. Its standard realization is in the zero-sum space on \(m=r+1\) coordinates. Every shell projection belongs to \(A_r^*\) (shadow vectors pair integrally with the even roots). Express it as \(v-(k/m)\mathbf1\) for integer \(v\) with \(\sum_i v_i=k\) and \(|k|\le m/2\). If \(b=\sum_i v_i^2\), the projection has squared norm \(b-k^2/m\). Since \(b\ge |k|\), this is at least \(|k|/2\); hence \(|k|\le\lfloor2a\rfloor\) and \(b\le\lfloor a+\lfloor2a\rfloor^2/m\rfloor\). The exact multiplicity for \(k,b\) is the coefficient of \(z^k w^b\) in \((\sum_i z^i w^{i^2})^m\), keeping only the stated finite range of \(b\). The verifier uses integer recurrence, doubling the counts for \(k>0\) by symmetry (even if this causes overcount at a boundary).

For a fixed projection, the residual vectors have squared norm \(\gamma=a-b+k^2/m\) in dimension \(d=n-r\). If \(\gamma<1/2\) there is at most one by distance \(\sqrt2\). If \(1/2\le\gamma\le1\), bound the **entire union** of residual vectors by \(2d\) and, when \(\gamma<1\), also by \(\lfloor1/(1-\gamma)\rfloor\). These follow respectively from the nonpositive pair products (Rankin's bound) and the squared norm of their sum. For the former, after normalizing, the sum of squared entries of the Gram matrix is at most twice the size, since negative off-diagonal entries satisfy \(s^2\le-s\) and the sum of all entries is nonnegative. The rank bound on that matrix gives at most \(2d\). For \(d=0\) use the upper bound 1.

If \(\gamma>1\), take each of the two shadow cosets separately, or take the entire shell in the even lattice case. Then differences have even squared norm, and the possible distinct inner products are \(\gamma-j\), \(1\le j\le \lfloor2\gamma\rfloor\). The products of the corresponding linear factors in \(\langle x,v\rangle\), one polynomial per point, separate the points. The dimension of polynomials of degree at most \(j_0=\lfloor2\gamma\rfloor\) on a \(d\)-dimensional ambient sphere is at most
\(\binom{d+j_0}{j_0}-\binom{d+j_0-2}{j_0-2}\), by taking the quotient by multiples of the sphere equation. Double for the two cosets in the shadow case. In the even-lattice case at zero projection, take one representative per antipodal line. For each representative \(x\) the homogeneous polynomial
\[
\langle x,v\rangle\prod_{j=1}^{a-1}\left(\langle x,v\rangle^2-j^2\|v\|^2/a\right)
\]
of degree \(2a-1\) vanishes on every other representative and not at \(x\): here \(\|v\|^2=a\) on the shell and the nontrivial absolute inner products lie in \(0,1,\ldots,a-1\). The linear factor is needed for orthogonal pairs. Thus \(2\binom{d+2a-2}{2a-1}\) additionally bounds the number of vectors. Summing over the projected counts gives the bounds used below. This is a counting argument, not a closest-vector computation.

## 3. Odd ranks 42–55

We may remove norm-one vectors by splitting off their orthogonal \(\mathbb Z\) factors; induction handles the smaller rank. In the no-norm-one case, use the same modular and shadow identities as in the earlier comparison, in the normalization \(u=\Delta_8/\vartheta_3^8\in(0,1/64]\). The ratio \(\Theta_L/\vartheta_3^n=\sum_j a_j u^j\) has
\[
a_0=1,\quad a_1=-2n,\quad a_2=N_2+2n^2-46n,\qquad
\Theta_S=\sum_j (-1)^j16^{-j}a_j\vartheta_2^{n-8j}\vartheta_4(q^2)^{8j},\quad q=e^{-t}.
\]
These are the standard identities as stated in [Kominers, Lemmas 2.1, 3.1 and 3.3](https://arxiv.org/abs/2606.01347). Write \(B_j\) for the shadow population at squared norm \(r_j=(n-8j)/4\). For \(n=48,49\) the possible \(a_6\) is zero: its leading shadow term would require a vector of squared norm 0 or \(1/4\), impossible since zero is not in the shadow and \(2y\in L\) for \(y\in S\). The degree is at most five through 49 and six in 50–55.

### Bounding the shadow populations

The shadow is a single coset modulo \(L\), split into two cosets of the even sublattice \(L_0\). Every \(2y\) for \(y\) in the shadow is characteristic; its parity of squared norm is the parity of \(n\), also seen directly from the displayed shadow exponents. Hence when \(n\) is even each shadow coset modulo \(L_0\) is antipodal. In it the off-diagonal inner products of distinct lines have absolute values drawn from
\[
|a-j|,\qquad 1\le j\le\lfloor 2a-1\rfloor,\qquad a=r_\ell.
\]
This uses the even squared norms of both \(x-y\) and \(x+y\). Bound the two cosets separately, counting two vectors per line. When \(n\) is odd, the two shadow cosets are negatives of each other. Work in just one coset with **signed** angles: \(x-y\in L_0\) is even, \(x+y\in L\setminus L_0\) is odd of squared norm at least 3. The allowed signed products are
\[
a-j,\qquad 1\le j\le\lfloor 2a-3/2\rfloor.
\]
Double the bound for that coset. In both cases the exceptional largest positive product \(a-1\) costs degree at most \(ha\). Using the signed angles in odd rank, rather than forgetting their signs, materially improves the certificates.

The fixed rational Gegenbauer certificates in the [replay](verify-unimodular-gaussian-mass-rank-55-72.js) bound \(B_4\) for all rows, and \(B_5\) in ranks 50–55. They use nonnegative coefficients and exact recurrence checks at every allowed angle. For the smaller shells, a common list of bounds applies at squared norms \(1/2,3/4,1,5/4,3/2,7/4,2,9/4\) in this order:
- Up through \(3/4\), two distinct antipodal lines cannot occur: the squares of \(x-y,x+y\) sum to \(4a<4\). At 1 the lines are orthogonal.
- At \(5/4,7/4,9/4\) in odd rank the separate signed sets have one, two, three distinct pair products, giving \(2\binom{n+j}{j}\) for \(j=1,2,3\) by separating polynomials.
- At \(3/2\) in even rank there is one absolute product within each coset, so the rank-one projectors onto the lines are independent, giving \(2n(n+1)\) vectors over both cosets. Independence follows from the Gram matrix of the projectors, with constant off-diagonal entry strictly smaller than the diagonal.
- At 2 in even rank, adjoining any nonempty shadow coset to \(L_0\) gives an integral lattice since a norm-two representative pairs integrally with \(L_0\) and doubles into \(L_0\). Its root count is at most \(2n(n-1)\); the two cosets give \(4n(n-1)\).

For ranks 54 and 55 we separate large \(A_r\) components to tighten \(N_2\) and, when necessary, \(B_4\):
- Rank 54 without \(A_r\) for \(r\ge48\) has \(h\le48\). For \(r=48\) use \(h=49\), \(N_2\le r(r+1)+d\max(30,d+1,2(d-1))\) where \(d=n-r\), and the spherical \(B_4\) bound. For \(r\ge49\) keep that root count and use the \(A_r\)-projection bound of §2 for \(B_4\).
- Rank 55 without \(A_r\) for \(r\ge52\) has \(h\le52\). For \(r=52,53,54\), the complementary rank is at most three so its root count is at most \(d(d+1)\). Thus \(N_2\le r(r+1)+d(d+1)\); use the spherical \(B_4\) bound at \(r=52,53\) and the projection bound at \(r=54\). A full-rank \(A_{55}\) would have determinant 56, not an integer square, so cannot sit in a unimodular lattice. In both ranks the \(B_5,B_6\) bounds are kept uniform across the cases.

### Positivity over the whole width range

For transparent normalization set \(s_j=(-1)^j 2^{n-12j}a_j\) and \(x=4096u\in(0,64]\). After the leading exponent in a shadow summand, its coefficients in powers of \(q^2\) are those of \(P_j(v)=(1+v+v^3+\cdots)^{n-8j}(1-2v+2v^4+\cdots)^{8j}\). Write \(p_{j,k}=[v^k]P_j\). The first two are \(p_{j,1}=n-24j\) and \(p_{j,2}=((n-24j)^2-(n+24j))/2\); the cubic \(p_{6,3}\) follows by multiplying the written factors through cubic degree.

Reading the successive shadow coefficients gives
\[
s_6=B_6,\quad s_5=B_5+(144-n)B_6,\quad
s_4=B_4+(120-n)s_5-p_{6,2}B_6,\quad
s_3=B_3-(n-96)s_4-p_{5,2}s_5-p_{6,3}B_6 .
\]
Use \(B_6=0\) and omit its terms when the degree is at most five. The contribution in \((\Theta_L/\vartheta_3^n-1)/u\) from \(j\ge3\) is \(2^{12-n}(-s_3 x^2+s_4x^3-s_5x^4+s_6x^5)\). Dropping \(-B_3x^2\) inside this factor gives the upper bound
\[
2^{12-n} x^2\big[(x+n-96)B_4+T_5(x)B_5+T_6(x)B_6\big],
\]
where
\[
\begin{aligned}
T_5(x)&=p_{5,2}+(120-n)(x+n-96)-x^2,\\
T_6(x)&=R(x+n-96)+(p_{5,2}-x^2)(144-n)+p_{6,3}+x^3,\quad
R=(120-n)(144-n)-p_{6,2}.
\end{aligned}
\]
Use \(U_5=\max(0,p_{5,2}+(120-n)(n-96)+(120-n)^2/4)\) as an upper bound on \(T_5\), and the largest nonnegative Bernstein coefficient of \(T_6\) on \([0,64]\) as \(U_6\). If \(N_2^{\max}\) and \(B_j^{\max}\) denote the appropriate bounds, the resulting certificate for all widths is positivity of
\[
2n-\frac{N_2^{\max}+2n^2-46n}{64}
-2^{24-n}\big[(n-32)B_4^{\max}+U_5 B_5^{\max}+U_6 B_6^{\max}\big].
\tag{1}
\]
In this bound \(x^2\le4096\), and all terms are replaced by nonnegative upper bounds before multiplication. The exact replay computes (1) for each case; the smallest margin over the odd cases is strictly greater than \(0.12\), in the \(h\le48\) rank-54 row. The smallest margin at rank 55 is greater than \(0.55\). These rounded margins are descriptive; the sign checks use integers and rational arithmetic.

## 4. Even rank 72

Write \(e=E_4/\vartheta_3^8=1-16u\in[3/4,1)\), as in the earlier note, and denote the squared-norm \(2,4,6\) shell counts by \(N_2,N_4,N_6\). The level-one modular form basis in weight 36 gives the ratio
\[
e^9+c_1e^6u^2+c_2e^3u^4+c_3u^6,
\]
where, by extracting the first three shell coefficients,
\[
c_1=N_2-2160,\qquad c_2=N_4-2093040-1416c_1,\qquad
c_3=N_6-1198601280-842652c_1-672c_2 .
\]
For example these come from \(E_4=1+240q^2+2160q^4+6720q^6+\cdots\) and \(\Delta=q^2-24q^4+252q^6+\cdots\). The coefficients on \(N_2,N_4,N_6\) in the ratio are all nonnegative on the interval: for \(N_2\) the first two terms give \(e^3u^2(e^3-1416u^2)>0\), and the remaining coefficient is \(108900u^6>0\); for \(N_4\) use \(u^4(e^3-672u^2)>0\). Thus we may substitute separate upper bounds on these counts.

After handling \(D_r\) for \(r\ge18\) by §1, either \(h\le50\), with \(N_2\le3600\), or \(h=r+1\) for an \(A_r\) component of rank \(50\le r\le72\). In the latter case use \(N_2\le r(r+1)+d\max(30,d+1,2(d-1))\). For \(N_4\), use an even spherical certificate in degrees \(2,6,10\), solving \(F(0)=F(1/4)=F(1/2)=0\), with the exceptional angle \(3/4\) costing degree at most \(4h\). For \(N_6\), use degrees \(2,4,10,18\), solving \(F(0)=F(1/6)=F(1/3)=F(2/3)=0\), and verify \(F(1/2)<0\); the last angle \(5/6\) has degree at most \(6h\). The replay solves these small systems exactly and tests positivity of every \(c_j\) of the spherical certificates. For each \(A_r\) row also compute the \(A_r\)-projection bounds on \(N_4,N_6\) and keep the smaller bound separately for each shell. In the critical \(A_{62}\) row the upper counts are \(4206,32938522,30541061464\).

Let \(U(e)\) be the substituted theta-ratio upper bound. To prove it is below one use the degree-eight polynomial
\[
\frac{1-U(e)}{1-e}
=\sum_{j=0}^8 e^j
-\frac{c_1}{256}e^6(1-e)
-\frac{c_2}{65536}e^3(1-e)^3
-\frac{c_3}{16777216}(1-e)^5.
\]
On \([3/4,1]\) set \(e=(3+x)/4\). All nine Bernstein coefficients on \(x\in[0,1]\) are strictly positive for every row, as the replay checks. The smallest coefficient across all rows is greater than \(0.0185\), in the \(A_{62}\) row. This proves the strict comparison for every \(t>0\), without requiring positivity of the individual substituted cusp coefficients.

## Scope and replay

Use the earlier 41/64 result for the lower ranks, and the norm-one splitting for integral lattices. Even unimodular ranks are multiples of eight, so there are no even cases between 64 and 72. [Shi–Dai–Solé](https://arxiv.org/abs/2611.19749) independently prove strict comparisons for extremal even and odd unimodular lattices and other code-related classes; the present rank statements make no extremality assumption. The strongest rank bounds here come from exact symbolic shell and Bernstein estimates, not a lattice enumeration or a grid of Gaussian widths. No beyond-55 odd or beyond-72 even claim is made. No cryptographic target, scheme, solver, or key recovery is part of the result.

Replay: node verify-unimodular-gaussian-mass-rank-55-72.js (Node.js 18+, standalone). It prints the fixed upper counts and the certified signs' margins; the displayed decimal approximations are not inputs.
