# A global quadratic-defect bound for orthogonal symmetric tensors of every order

mxym repository account; prepared with AI assistance, 7 October 2026.

## Statement and provenance

The cubic argument extends to **every symmetric tensor order**. We prove an unconditional estimate including arbitrary real weights, zero weights and all degeneracies. It uses neither an entropy theorem nor an upstream OpenAI result. Orthogonally decomposable tensors and their algebraic equations are established subjects, notably Boralevi–Draisma–Horobeț–Robeva, [arXiv:1512.08031](https://arxiv.org/abs/1512.08031). We do not claim their zero-set characterization as new. The present result is a quantitative estimate directly from the complete contraction-commutator defect, with an elementary proof and explicit dimension/order constants. Its novelty relative to all existing error-bound and tensor-decomposition literature has not been established.

Fix integers $m\ge1$ and $p\ge3$. For a fully symmetric real order-$p$ tensor $T$, use the Frobenius norm over all ordered indices. For an ordered multi-index $\alpha\in\{1,\ldots,m\}^{p-2}$, define

$$
(X_\alpha)_{ij}=T_{\alpha_1,\ldots,\alpha_{p-2},i,j},
\quad
R_p(T)=\left(\sum_{\alpha,\beta}
|[X_\alpha,X_\beta]|_F^2\right)^{1/2}.
\tag{1}
$$

All ordered multi-indices are included, even though symmetry creates duplicates. This convention is essential for the rotation invariance and for the constants stated here. Let

$$
\mathcal D_{m,p}=\left\{\sum_{i=1}^m\lambda_i u_i^{\otimes p}:
(u_i)\text{ orthonormal},\ \lambda_i\in\mathbb R\right\}.
$$

Put $K_{1,p}=0$ and, for $m\ge2$, define the explicit constant

$$
K_{m,p}=\frac{p^p}{p!}\sqrt{2p}\,m^{p/2}.
\tag{2}
$$

**Theorem.** Every fully symmetric real tensor of order $p$ satisfies

$$
\operatorname{dist}(T,\mathcal D_{m,p})
\le K_{m,p}\sqrt{R_p(T)}.
\tag{3}
$$

For each fixed $m\ge2,p\ge3$, no larger uniform power of $R_p$ is possible, even on tensors of norm at most one. In particular, the zero-defect statement is exact. There is no small-defect assumption or lower-weight hypothesis. For each fixed order, (2) grows polynomially in dimension; it is not asserted optimal.

## Complete proof

### Rotation invariance

An orthogonal coordinate change acts on the contraction multi-index by $U^{\otimes(p-2)}$, an orthogonal matrix, and on the last two indices by conjugation. Because the commutator is bilinear, its two multi-indices transform by the tensor product of two such orthogonal matrices. Summing all squared entries in (1) therefore leaves $R_p$ unchanged. The tensor and distance norms are invariant as well.

### Maximizing direction and a spectral gap relative to it

Set $f(x)=T(x,\ldots,x)$ and $\lambda=\max_{|x|=1}|f(x)|$. If $\lambda=0$, polarization gives $T=0$. If the maximizing value is negative, replace $T$ by $-T$; the defect and the distance are unchanged because the decomposition class permits negative weights. Thus take a maximizing vector $v$ with $f(v)=\lambda>0$.

Let $X_v=T(v^{p-2},\,\cdot,\,\cdot)$. Lagrange multipliers give $X_vv=\lambda v$. For a unit vector $w\perp v$, the second derivative of $f(v\cos t+w\sin t)$ is

$$
p(p-1)T(v^{p-2},w,w)-p\lambda\le0.
$$

Rotate so $v=e_1$ and diagonalize $X_v$ on its complement:

$$
X_v=\operatorname{diag}(\lambda,\mu_2,\ldots,\mu_m),
\quad
\mu_j\le\lambda/(p-1).
\tag{4}
$$

The positive gap used below is **between the maximizing eigenvalue and the other eigenvalues of this particular contraction**, derived from the maximum. No gap assumption on the unknown orthogonal weights is made.

### Bound every mixed tensor entry

In these coordinates $X_v=X_{(1,\ldots,1)}$ is one of the contraction matrices in (1). For any multi-index $\alpha$ and $j>1$,

$$
([X_v,X_\alpha])_{j1}
=(\mu_j-\lambda)T_{\alpha,j,1}.
$$

Since $p\ge3$, (4) gives
$\lambda-\mu_j\ge\lambda(p-2)/(p-1)\ge\lambda/2$. Thus

$$
R_p(T)^2\ge2\sum_\alpha|[X_v,X_\alpha]|_F^2
\ge\lambda^2\sum_{\alpha,j>1}|T_{\alpha,j,1}|^2.
\tag{5}
$$

The first factor two counts the row and column of the complete commutator array indexed by $X_v$. Their sole overlap is its zero self-commutator. The second inequality also uses the two skew-symmetric entries for each pair $(1,j)$.

Let $T'$ be the restriction to $e_1^\perp$ and $M=T-\lambda e_1^{\otimes p}-T'$. Its only entries are mixed. Among the ordered permutations of a fixed symmetric coefficient containing $k$ copies of index one, $1\le k\le p-1$, the fraction with last index one and penultimate index different from one is $k(p-k)/(p(p-1))\ge1/p$. This is also valid when the other indices repeat: average the indicator over all permutations of positions. Therefore

$$
|M|^2\le p\sum_{\alpha,j>1}|T_{\alpha,j,1}|^2
\le pR_p(T)^2/\lambda^2.
\tag{6}
$$

This aggregated estimate avoids a dimension factor from bounding each entry separately. It is why the theorem needs the complete family of contractions, rather than a few selected or sampled matrices.

### Defect of the complementary tensor

For multi-indices $\alpha$ lying entirely in the complement, write

$$
X_\alpha=\begin{pmatrix}a_\alpha&b_\alpha^T\\
b_\alpha&Z_\alpha\end{pmatrix}.
$$

The $Z_\alpha$ are precisely the contractions of $T'$. The lower-right commutator block is

$$
[Z_\alpha,Z_\beta]+b_\alpha b_\beta^T-b_\beta b_\alpha^T.
$$

Minkowski's inequality for the direct sum of matrix spaces gives

$$
R_p(T')\le R_p(T)+\sqrt2\sum_\alpha|b_\alpha|^2
\le R_p(T)+2|M|^2.
\tag{7}
$$

For the first inequality, sum
$|bc^T-cb^T|_F^2=2(|b|^2|c|^2-\langle b,c\rangle^2)$ over all ordered pairs. For the second, entries $(b_\alpha)_j=T_{\alpha,1,j}$ are a subset of the ordered mixed tensor entries. These comparisons do not assume any sign of $a_\alpha$ or $b_\alpha$.

### Induction

The real polarization identity is

$$
T(x_1,\ldots,x_p)=\frac1{2^p p!}
\sum_{\epsilon\in\{-1,1\}^p}
\left(\prod_i\epsilon_i\right)
f\left(\sum_i\epsilon_i x_i\right).
$$

For unit vectors $x_i$, this has magnitude at most $P_p\lambda$, where $P_p=p^p/p!$. Fix the first $p-1$ arguments to basis vectors and optimize over the final unit vector. The Euclidean norm of the corresponding coefficient vector is at most $P_p\lambda$. Summing over the $m^{p-1}$ fixed ordered tuples gives

$$
|T|\le P_p m^{(p-1)/2}\lambda.
\tag{8}
$$

Proceed by induction on $m$, with the one-dimensional case exact. Write $R=R_p(T)$. If $\lambda\le\sqrt{2pmR}$, choosing the zero tensor and using (8) proves (3). If $\lambda>\sqrt{2pmR}$, (6)–(7) give

$$
|M|\le\frac{\sqrt R}{\sqrt{2m}},\qquad
R_p(T')\le(1+1/m)R.
$$

Choose an optimal decomposition $S'$ of $T'$ in the complement. Existence follows by optimizing on the compact orthogonal group after choosing the optimal projection weights in each fixed basis. By induction,

$$
|T'-S'|\le K_{m-1,p}\sqrt{(1+1/m)R}.
$$

Extend this decomposition by the term $\lambda e_1^{\otimes p}$. Its error is at most

$$
\left[\frac1{\sqrt{2m}}+K_{m-1,p}\sqrt{1+1/m}\right]\sqrt R
\le K_{m,p}\sqrt R.
$$

For completeness, the last inequality follows without hiding a recursive constant. Set $A=P_p\sqrt{2p}$ and $s=p/2\ge3/2$. For $m\ge2$, $\sqrt{1+1/m}\le1+1/m\le m/(m-1)$. Also

$$
m^{s-1}-(m-1)^{s-1}
=\int_{m-1}^m(s-1)x^{s-2}\,dx
\ge\int_{m-1}^m\frac1{2\sqrt x}\,dx
\ge\frac1{2\sqrt m}.
$$

Thus $Am^s-A(m-1)^s\sqrt{1+1/m}\ge A\sqrt m/2\ge1/\sqrt{2m}$. For $m=2$ using the actual $K_{1,p}=0$ only improves this estimate. This includes $R=0$: every mixed coefficient is then zero and induction gives an exact decomposition. Reversing the initial sign change, if any, gives the original tensor. $\square$

## Sharpness for every fixed order and dimension

For $m\ge2$, take the tensor whose entries are one exactly on permutations of $(1,\ldots,1,2)$ and zero elsewhere. The contractions with multi-indices $(1,\ldots,1)$ and $(1,\ldots,1,2)$ of lengths $p-2$ have, on the first two coordinates, matrices

$$
\begin{pmatrix}0&1\\1&0\end{pmatrix},
\qquad
\begin{pmatrix}1&0\\0&0\end{pmatrix},
$$

which do not commute. Therefore this tensor is not orthogonally decomposable: contractions of an orthogonally decomposable tensor are all diagonal in its defining basis.

The decomposition class is closed. Indeed, in any approximating sequence with bounded tensor norms the weights have bounded sum of squares, because its rank-one terms are orthonormal; then compactness of the bases and bounded weights gives a convergent decomposition. Thus this tensor has positive distance $d_0$ from the class and positive finite residual $r_0$.

For its multiple $tT$, distance is $td_0$ and defect is $t^2r_0$. If $\alpha>1/2$, their ratio $td_0/(t^2r_0)^\alpha$ diverges as $t\downarrow0$. Taking $t$ sufficiently small keeps the tensor norm at most one. This proves the sharp exponent for each fixed $m,p$.

## Dimension dependence cannot be removed

**Proposition.** For each fixed $p\ge3$, any constants $L_{m,p}$ satisfying (3) in dimension $m$ obey

$$
L_{2k,p}\ge\sqrt{1-2^{2-p}}\,k^{1/4},\qquad k\ge1.
\tag{9}
$$

In particular, a dimension-free estimate with this Frobenius residual is impossible.

**Proof.** On $\mathbb R^2$, let $H_p(x,y)=\operatorname{Re}(x+iy)^p$. Its symmetric tensor has entry $\cos(\ell\pi/2)$ on indices containing $\ell$ copies of index two. Its squared Frobenius norm is $2^{p-1}$. Its absolute diagonal maximum on the unit circle is one.

For the contraction multi-indices, an even number of index-two entries gives, up to sign, $E=\operatorname{diag}(1,-1)$; an odd number gives, up to sign, $F=\begin{pmatrix}0&1\\1&0\end{pmatrix}$. Each parity occurs $2^{p-3}$ times. Same-parity matrices commute; a cross-parity commutator has squared Frobenius norm eight. Counting both orders gives $R_p(H_p)^2=2^{2p-2}$.

Take $T_k$ to be the orthogonal direct sum of $k$ copies in dimension $2k$. Every nonzero contraction is supported in a single block; different blocks commute. Hence

$$
|T_k|^2=k2^{p-1},\qquad R_p(T_k)=2^{p-1}\sqrt k.
$$

For a unit vector with block radii $r_b$, $|T_k(u^{\otimes p})|\le\sum_b r_b^p\le\sum_b r_b^2=1$. In every orthonormal basis the total squared projection onto the $2k$ orthonormal rank-one tensors is thus at most $2k$. Optimizing the weights in that basis and then the basis itself yields

$$
\operatorname{dist}(T_k,\mathcal D_{2k,p})^2
\ge k(2^{p-1}-2).
$$

Divide its square root by $\sqrt{R_p(T_k)}$ to obtain (9). These lower and upper dimension powers do not match; determining the optimal dimension growth remains open within this note. No claim about whether that question was previously studied is made. $\square$

## What is and is not verified

This manuscript proves every order and dimension analytically. The cubic companion adds a substantially better dimension-dependent constant and the exact best constant $\sqrt3/2$ in dimension two. Finite rational tests verify the compression identity, all-contraction indexing and the sharpness contractions for selected higher orders; they do not replace the induction.

The separate Lean files verify the normalized cubic first-order kernel and binary polynomial identities. They do not yet formalize this all-orders maximizing-vector argument. No algorithmic complexity, dimension-free constant, or mathematical priority claim is made.
