# Exact nonreal sectors and the outer support of the permanent–determinant pencil

Fix \(n\ge4\) and set \(\rho=n!/n^{n/2}\), \(c_0=\rho-1\). Rows of each complex matrix \(A\) are normalized to have Euclidean length one. Write \(p=\operatorname{per}A,\ d=\det A\), and
\[
 C_n(\lambda)=\max_A|p+\lambda d|.
\]
The maximum exists because the set of normalized matrices is compact. We use the sharp absolute-value tradeoff and its equality cases from the [all-order note](https://github.com/mxym/math/blob/4f312d46aab51f90425336f06000a95b48df6f59/research/euclidean-tensor-geometry/theoretical-cryptography/FactorPermanentDeterminantAllOrders.md) for \(n\ge5\) and [Part Q of the previous manuscript](https://github.com/mxym/math/blob/main/manuscripts/complex-permanent-pencil/paper.md) for \(n=4\). The absolute-value theorem and its equality cases are dependencies, not new claims here.

**Theorem 1.** For each \(n\ge4\) there exists \(\varepsilon_n>0\) such that
\[
 C_n(\lambda)=\max\{\rho,\ |1+\lambda|,\ |1-\lambda|\}
 \qquad\text{if}\qquad |\operatorname{Im}\lambda|\le
                 \varepsilon_n|\operatorname{Re}\lambda|. \tag{1}
\]
In particular the sectors contain nonreal coefficients of arbitrarily large modulus. The proof does not give an explicit or dimension-independent angle.

The flat set \(\mathcal L_n=\{\lambda:C_n(\lambda)=\rho\}\) is compact and convex, contains the closed disk \(|\lambda|\le c_0\), and contains every nonreal point of the boundary of that disk **in its interior**. Near \(+c_0\) its local boundary is exactly \(|1+\lambda|=\rho\); near \(-c_0\) it is exactly \(|1-\lambda|=\rho\). These are local assertions, not a formula for the entire flat set.

**Theorem 2.** For fixed \(n\ge4\), uniformly in real \(\theta\), as \(R\to\infty\),
\[
 C_n(Re^{i\theta})=R+h_n(\theta)+O_n(R^{-1}),\quad
 h_n(\theta)=\max_{U\in U(n)}
   \operatorname{Re}\!\left(e^{-i\theta}\frac{\operatorname{per}U}{\det U}\right). \tag{2}
\]
This is a reduction of the first asymptotic correction to the unitary support function; it does not determine \(h_n\) in all directions. The even and odd permutation matrices and the normalized three-dimensional Fourier matrix embedded with an identity block give the unconditional lower bound \(h_n(\theta)\ge\max\{|\cos\theta|,|\sin\theta|/\sqrt3\}\).

## 1. Two neighborhoods

The absolute-value theorem gives
\[
 |p|+c_0|d|\le\rho,\qquad |p|\le1+c_0(1-|d|), \tag{3}
\]
with equality in the first inequality only at the equimodular rank-one and monomial matrices. The all-order note also supplies, for every \(n\ge4\), the two bounds used here; its proofs of these two estimates apply unchanged at \(n=4\). With \(r^2=\sum_{i\ne j}|(AA^*)_{ij}|^2/(n(n-1))\), set
\[
 B_n=1-\left(\frac{n}{2(n-1)}\right)^{\lfloor n/2\rfloor/2}>0.
\]
Then
\[
 |p|\le\rho[1-B_n(1-r^2)],\qquad
 |d|\le(1-r)^{(n-1)/2}\sqrt{1+(n-1)r}. \tag{4}
\]
The permanent estimate uses [Roos's phase-sensitive block bound](https://arxiv.org/pdf/1906.06176), and the determinant estimate is the [mean–variance product bound of Rodin](https://arxiv.org/abs/1409.0162), as derived in the cited note.

For any fixed finite bound on \(|\lambda|\), there is a uniform neighborhood \(r\ge1-\delta\) in which \(|p+\lambda d|\le\rho\). Indeed the permanent deficit in (4) is at least \(\rho B_n(1-r)\), whereas \(|\lambda d|\le|\lambda|\sqrt n(1-r)^{(n-1)/2}\); the latter power exceeds one. At \(r=1\), \(d=0\).

At an even monomial matrix, apply an even column permutation and phases so the limit matrix is \(I\), then change row phases to make each diagonal entry of a nearby matrix nonnegative. All these operations leave \(|p+\lambda d|\) and \(p\overline d\) unchanged. Let \(Q=\sum_{i\ne j}|a_{ij}|^2\) and \(Z=\sum_{i<j}a_{ij}a_{ji}\), so \(|Z|\le Q/2\). The diagonal product is \(1-Q/2+O_n(Q^2)\) by row normalization. A transposition contributes \(Z\) to second order, while all nonidentity non-transposition permutations move at least three indices. Thus, as \(Q\to0\),
\[
 p=1-Q/2+Z+O_n(Q^{3/2}),\qquad
 d=1-Q/2-Z+O_n(Q^{3/2}). \tag{5}
\]
These bounds are uniform over the off-diagonal variables in a fixed dimension. In particular:
- In any compact coefficient neighborhood of a positive real \(t\), \(|1+\lambda|-|1-\lambda|\) is bounded below by a positive number if the neighborhood is taken small enough. From (5),
\[
 |p+\lambda d|
 \le |1+\lambda|-\tfrac12\big(|1+\lambda|-|1-\lambda|\big)Q
             +O_n((1+|\lambda|)Q^{3/2}).
\]
It is at most \(|1+\lambda|\) in a uniform small matrix neighborhood.
- If \(W=p\overline d\), then
\[
 W=1-Q+2i\operatorname{Im}Z+O_n(Q^{3/2}),
\]
so for sufficiently small \(Q\), \(1-\operatorname{Re}W\ge Q/2\) and \(|\operatorname{Im}W|\le2Q\). This estimate does not involve \(\lambda\).

## 2. Bounded and unbounded coefficients

Conjugation and an odd column permutation show \(C_n(\bar\lambda)=C_n(\lambda)=C_n(-\lambda)\), so only \(\lambda=x+iy\), \(x\ge0\), is needed. In this half-plane \(|1+\lambda|\ge|1-\lambda|\). Flat matrices and the identity give the lower bound in (1). If no \(\varepsilon_n\) exists, there is a sequence of violations \(\lambda_j=x_j+iy_j\) with \(x_j>0,\ |y_j|\le x_j/j\), and normalized \(A_j\) satisfying
\[
 |\operatorname{per}A_j+\lambda_j\det A_j|>
 \max\{\rho,|1+\lambda_j|\}.
\]
Pass to a subsequence so \(A_j\to A_\infty\) and \(x_j\) converges in \([0,+\infty]\).

If \(x_j\to t<\infty\), then \(\lambda_j\to t\). For \(t<c_0\) a violation is impossible eventually by (3), which proves the entire flat disk. For \(t\ge c_0>0\), continuity and the sharp real norm force \(A_\infty\) to be an equality matrix for the real pencil. By the absolute-value equality cases and the strict odd-parity monomial deficit \(|1-t|<1+t\), it is either equimodular rank one or an even monomial. The respective uniform neighborhoods above exclude the violation.

If \(x_j\to\infty\), the squared gap from the even monomial branch is exactly
\[
 \begin{split}
 |1+\lambda_j|^2-|p_j+\lambda_j d_j|^2
 ={}&|\lambda_j|^2(1-|d_j|^2)+1-|p_j|^2\\
    &+2x_j(1-\operatorname{Re}W_j)-2y_j\operatorname{Im}W_j,
 \qquad W_j=p_j\overline{d_j}. \tag{6}
 \end{split}
\]
It is negative by assumption. Boundedness of \(p_j,d_j,W_j\) and \(|\lambda_j|\to\infty\) first force \(|d_j|\to1\). Divide by \(2x_j\), drop the nonnegative determinant deficit, and use \(y_j/x_j\to0\); it follows that \(\operatorname{Re}W_\infty\ge1\). By (3), \(|p_\infty|\le1\), hence \(W_\infty=1\). This is an even monomial by equality in (3). The estimates in (5) now apply eventually. The first line on the right in (6) is nonnegative for \(|\lambda_j|^2\ge\rho^2-1\), since (3) gives
\[
 |p_j|^2-1\le(2c_0+c_0^2)(1-|d_j|)
             \le(\rho^2-1)(1-|d_j|^2).
\]
The second line is then at least \((x_j-4|y_j|)Q\ge0\). This again contradicts the violation and proves (1).

For the remaining claims about \(\mathcal L_n\), \(C_n\) is a convex continuous function of \((\operatorname{Re}\lambda,\operatorname{Im}\lambda)\); for example its Lipschitz constant is at most one because \(|d|\le1\). It is always at least \(\rho\); the monomial branches bound \(\mathcal L_n\) by \(|1\pm\lambda|\le\rho\). At a nonreal point of the circle \(|\lambda|=c_0\), equality can only be equimodular rank one: the monomial triangle inequalities are strict. A uniform \(r\)-near-one neighborhood works at all nearby coefficients by (4); away from that neighborhood the matrix set is compact and has a strict gap at the chosen coefficient. Continuity gives an open coefficient neighborhood with \(C_n=\rho\). Finally (1) gives the asserted local arcs at the real contact points.

## 3. Outer support and the error term

For unitary \(U\), multiplication by \(\overline{\det U}\) preserves the objective modulus. Since \(|z|\ge\operatorname{Re}z\), the unitary tests alone give \(C_n(Re^{i\theta})\ge R+h_n(\theta)\). For the Fourier lower witness, the normalized \(3\times3\) Fourier matrix has ratio \(\pm i/\sqrt3\) between its permanent and determinant (use the conjugate for the other sign). Adjoining identity rows keeps that ratio. This yields the stated lower bound alongside the even and odd monomial witnesses.

For the upper bound, let \(A\) maximize the objective, \(D=|d|\), and take \(R\ge4\rho\). The two monomial tests give \(C_n(Re^{i\theta})\ge R\), so \(D\ge1-\rho/R\ge3/4\) by \(|p|\le\rho\). Write \(A=G^{1/2}U\) with \(G=AA^*\) and \(U\) unitary. The determinant phases of \(A,U\) agree because \(G^{1/2}\) is positive definite. The determinant-quotient monotonicity in the all-order note, valid for \(n\ge4\) by its derivative proof, gives \((1-d_n(r))/r^2\ge1-d_n(1)=1\) for \(0<r\le1\), where \(d_n\) denotes the envelope in (4). Therefore \(r^2\le1-D\), including \(r=0\). Diagonalizing \(G\), and using \(|\sqrt{s}-1|\le|s-1|\) for \(s\ge0\), gives
\[
 \|A-U\|_{\mathrm F}=\|G^{1/2}-I\|_{\mathrm F}
 \le\|G-I\|_{\mathrm F}\le\sqrt{n(n-1)}\,\sqrt{1-D}.
\]
The [permanent bound of Carlen–Lieb–Loss](https://arxiv.org/abs/math/0508096) applied after telescoping one row at a time gives
\[
 |p-\operatorname{per}U|\le \rho\sqrt n\,\|A-U\|_{\mathrm F}
 \le K\sqrt{1-D},\qquad K=\rho n\sqrt{n-1}.
\]
Indeed all non-difference rows remain unit vectors.

Multiply the pencil value by \(\overline{\det U}e^{-i\theta}\), and put \(z=e^{-i\theta}p\,\overline{\det U}\). Its modulus is \(|RD+z|\). We have \(\operatorname{Re}z\le h_n(\theta)+K\sqrt{1-D}\). Also \(RD+\operatorname{Re}z\ge RD-\rho\ge R/2\). Consequently
\[
 |RD+z|\le RD+\operatorname{Re}z+\rho^2/R;
\]
subtract the real part and rationalize the difference using \(|RD+z|\ge RD+\operatorname{Re}z>0\). Finally
\[
 RD+K\sqrt{1-D}\le R+\frac{K^2}{4R}.
\]
This proves (2), with explicit error bounded between \(0\) and \((K^2/4+\rho^2)/R\) for \(R\ge4\rho\).

## Scope

The previously known complete complex pencil formula in order three is not repeated. For \(n\ge4\), the sectors, local flat boundary and unitary asymptotic reduction do not give the exact norm throughout the remaining angular region, or an all-direction characterization of the unitary support. All arguments in this note are analytic and require no numerical certificates beyond the already cited absolute-value tradeoff.
