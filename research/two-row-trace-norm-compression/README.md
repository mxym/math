# Trace-norm compression: two block rows and an entrywise-positive obstruction

**Research draft · 18 November 2026.** The lower trace-norm inequality holds for every matrix with two block rows. It can fail for a real, symmetric, strictly entrywise-positive $6\times6$ matrix on a $3\times3$ grid of $2\times2$ blocks. On growing grids there is no dimension-independent positive lower factor, even with those inner block sizes fixed. Here “positive entries” does **not** mean a positive semidefinite operator.

**中文摘要。** 本文证明 Audenaert 两行块矩阵压缩猜想的 $p=1$ 端点，并把 Li–Zhao 的带符号例子提升为逐项严格正的核范数反例。一般 Schatten 指数的问题不在本文结论内。

The research and a separate internal proof check were AI-assisted. The governing norm, sign, input theorem, singular cases, and the seed's provenance were checked against the primary sources below. This is not external peer review or formal verification, and no worldwide priority is claimed.

## 1. The trace endpoint for any two block rows

Let a real or complex matrix $T$ have two block rows and $N\ge1$ block columns with arbitrary compatible finite dimensions. Let $C=C_1(T)=[\|T_{ij}\|_*]$, with $\|\cdot\|_*$ the nuclear norm (sum of singular values). Then
$$
                     \|C\|_*\le\|T\|_* .                                    \tag{1}
$$
This is the $p=1$ case of Audenaert's Conjecture 1 (2007 preprint, 2008 publication), not the conjecture at all exponents. It imposes no block commutativity, positivity or rank restriction. The bound is attained for every prescribed nonnegative scalar compression $C$: take $T_{ij}=C_{ij}u_iv_j^*$ using a unit vector in each prescribed row and column space. Then $T$ is $UCV^*$ for isometries $U,V$.

**Input (Drury, 2014, Corollary 1.3; Li–Zhang, preprint Theorem 1).** For three compatible block rows $Z_a$ with the same number of columns, the real symmetric matrix with entries $\|Z_aZ_b^*\|_*$ is positive semidefinite. This is a published input, not our result. Rectangular blocks and singular cases are allowed.

**Proof.** The zero case is immediate. Take a reduced singular-value decomposition $T=U\Sigma V^*$; set $X=U\sqrt\Sigma$, $Y=V\sqrt\Sigma$. Then $T=XY^*$ and $\|X\|_F^2=\|Y\|_F^2=\|T\|_*$. Write $X_i,Y_j$ for the block rows; define
$$
 G_{i\ell}=\|X_iX_\ell^*\|_*,\qquad b_j=\|Y_j\|_F^2,\qquad
 c_j=(\|X_iY_j^*\|_*)_{i=1}^2=C_{:j}.
$$
Each $P_j=\begin{pmatrix}G&c_j\\ c_j^t&b_j\end{pmatrix}$ is PSD by Drury. Each therefore is the Gram matrix of three real vectors. Realize the first pair as the same vectors $u_1,u_2$ for every $j$: two pairs with identical Gram matrix have a norm-preserving identification of their spans, including dependent pairs. Map the projection of the third vector onto this span by that identification, and its perpendicular component to an extra orthogonal direction with the same length. The resulting $v_j$ satisfies $u_i\cdot v_j=C_{ij}$ and $\|v_j\|^2=b_j$. No cross-inner-product of two $v_j$'s is prescribed. Thus $C=AB^t$ for the corresponding matrices of vector rows, with
$$
 \|A\|_F^2=\operatorname{tr}G=\sum_i\|X_i\|_F^2=\|T\|_*,
 \qquad \|B\|_F^2=\sum_j b_j=\|T\|_*.
$$
Schatten Hölder gives $\|AB^t\|_*\le\|A\|_F\|B\|_F$, proving (1). No global positivity of the matrix of all pairwise trace norms is assumed.

**Remainder and equality.** Let $D=(CC^t)^{1/2}$, let $G^\dagger$ be the Moore–Penrose inverse and set $G^{\dagger/2}=(G^\dagger)^{1/2}$. There is a nonnegative identity
$$
2(\|T\|_*-\|C\|_*)=\sum_j(b_j-c_j^tG^\dagger c_j)
     +\big\|G^{\dagger/2}(G-D)\big\|_F^2.                                 \tag{2}
$$
Indeed $P_j\ge0$ implies $c_j\in\operatorname{ran}G$: apply its quadratic form to $(z,t)$ for $z\in\ker G$ and both small signs of $t$. Substituting $(-G^\dagger c_j,1)$ gives $b_j-c_j^tG^\dagger c_j\ge0$. The range of $D$ lies in that of $G$. Expanding the square and cycling the trace gives $\operatorname{tr}G-2\operatorname{tr}D+\operatorname{tr}(G^\dagger CC^t)$; summing the other terms gives (2). Equality holds exactly when $G=D$: necessity follows from the second summand and range inclusion; sufficiency follows by taking traces. Intrinsically, $G$ is the entrywise block nuclear-norm compression of $(TT^*)^{1/2}=XX^*$; $\|T\|_*$ equals its trace. No invertibility assumption is needed.

## 2. Failure on strictly positive matrices, even with fixed two-by-two inner blocks

Li and Zhao (2020), immediately after Example 3.4, expect equation (7) to hold for tensors with nonnegative entries. Their order-two, Euclidean-factor case (vector parameter $(2,2)$) is the usual Schatten **one** norm. Their Example 3.4 is signed and so is not itself a counterexample to this expectation. We *use their signed example*, not an original signed seed:
$$
 M=\begin{pmatrix}-1&1&0\\1&0&1\\0&1&1\end{pmatrix},\qquad
 H=|M|_{\rm entrywise}.
$$
The characteristic polynomials of $M,H$ are $x(x^2-3)$ and $(x-2)(x-1)(x+1)$; $H{\bf1}=2{\bf1}$. For $k\ge1$ let $n=3^k$, $S=M^{\otimes k}$, $A=H^{\otimes k}=|S|_{\rm entrywise}$, and $J$ the $n\times n$ all-ones matrix. Define $T$ by an $n\times n$ grid of fixed $2\times2$ blocks
$$
 T_{ij}=\begin{pmatrix}2+S_{ij}&2-S_{ij}\\2-S_{ij}&2+S_{ij}\end{pmatrix}.
$$
The entries belong to $\{1,2,3\}$; $T=T^t$ and each row or column sums to $4n$. Hence $T/(4n)$ is strictly positive and doubly stochastic. This does *not* assert positive semidefiniteness.

Changing inner coordinates to the normalized sum and difference vectors, and grouping these two sets of coordinates, gives
$$
 T\simeq4J\oplus2S,\qquad C_1(T)=4J+2A.
$$
Thus $\|T\|_*=4n+2(2\sqrt3)^k$. Because $A{\bf1}=2^k{\bf1}$, $4J$ shifts just this nonnegative eigenvalue upwards by $4n$ and vanishes on the orthogonal complement. It follows that
$$
 \|C_1(T)\|_*=4n+2\|H\|_*^k=4n+2\cdot4^k,\qquad
 \frac{\|T\|_*}{\|C_1(T)\|_*}
  =\frac{2\cdot3^k+(2\sqrt3)^k}{2\cdot3^k+4^k}\ \longrightarrow 0.
$$
For $k=1$, the $6\times6$ matrix $T$ has eigenvalues $12,2\sqrt3,-2\sqrt3,0,0,0$, while its $3\times3$ compression has eigenvalues $16,2,-2$. Thus their nuclear norms are $12+4\sqrt3<20$. No positive dimension-independent lower factor exists even for strictly positive matrices with only these three integer values before rescaling and *fixed* $2\times2$ inner blocks. The grid grows; no impossibility at fixed grid dimensions is asserted.

**Threshold in grid dimensions.** For a given $m\times n$ grid and arbitrary compatible inner dimensions, the universal constant-one trace inequality holds iff $\min(m,n)\le2$. Sufficiency follows by (1), taking the adjoint or padding the one-row case. For necessity pad the $k=1$ counterexample with zero block rows/columns; change only entries of the extra blocks to a sufficiently small positive number if strict entrywise positivity is desired. The strict violation persists by continuity. This is a statement with quantification over inner dimensions: compression on a positive grid of scalar blocks is of course equality.

## Reproduction

Run `python3 -B -O verify.py` in this directory (requires NumPy and SymPy). The script computes spectra and the orthogonal block decompositions in exact arithmetic for $k=1,2,3$; the general $k$ conclusion follows from the displayed tensor-product identities. It also makes 289 numerical checks of (1) and (2), including complex rectangular and singular cases. These tests are regression checks, not a proof of the endpoint theorem.

## Sources and scope

1. K.M.R. Audenaert, [On a norm compression inequality for 2 × N partitioned block matrices, Conjecture 1](https://arxiv.org/html/math/0702186), Linear Algebra Appl. 428 (2008), 781–795. See also K.M.R. Audenaert and F. Kittaneh, [Problems and conjectures in matrix and operator inequalities, Conjecture 3, (22)–(23)](https://arxiv.org/abs/1201.5232). Audenaert's §2 proves lower-to-upper duality, not the converse; §4 includes $p\ge4$ and structured cases. In §5, at $p=1$ its diagonal-block function $g_1$ is just the ordinary trace norm and hence convex; shorthand about failure over the extended interval below one should not be taken as a counterexample *at* $p=1$.
2. T. Zhang, [Clarkson–McCarthy type inequalities, part I, v4 (28 March 2026), Conjecture 1.14, Theorem 1.15](https://arxiv.org/html/2410.21961v4). Restates the all-exponent two-row conjecture and proves a weaker rank-factor bound. The present note does not resolve the interior $1<p<2$ or $2<p<4$.
3. S.W. Drury, [Positive semidefiniteness of a 3 × 3 matrix related to partitioning](https://doi.org/10.1016/j.laa.2013.12.037), Linear Algebra Appl. 446 (2014), 369–376, Corollary 1.3. C.-K. Li and F. Zhang, [Positivity of partitioned Hermitian matrices with unitarily invariant norms](https://arxiv.org/abs/1407.0331), Positivity 19 (2015), 439–444. Three-block positivity is prior art. M. Lin and P. van den Driessche noted a gap in an earlier fidelity proof on [p. 835](https://journals.uwyo.edu/index.php/ela/article/download/1429/1429/1429); we use Drury and Li–Zhang, not that earlier proof.
4. [Vuong–Osaka, Theorem 1.2 / Corollary 3.1](https://arxiv.org/html/2610.11021) and [Sra](https://arxiv.org/abs/2610.15889), October 2026, report PSD of the three-by-three matrix of the $p$-th powers of block $p$-norms for $1\le p\le2$. That is a distinct conjecture (Lin–van den Driessche), not a two-row norm comparison. Only the published $p=1$ theorem is used here.
5. Z. Li and Y.-B. Zhao, [On norm compression inequalities for partitioned block tensors, eq. (7), Example 3.4 and following paragraph](https://doi.org/10.1007/s10092-020-0356-x), Calcolo 57, 11 (2020). See also the authors' [open manuscript, p. 11](https://pure.port.ac.uk/ws/portalfiles/portal/19117904/On_norm_compression_inequalities.pdf). Their signed seed already violates the three-row extension with no sign restrictions. Section 2 turns that seed into a strictly positive example and amplifies the failure while preserving fixed inner block size. The matrix tensor nuclear norm at parameter $(2,2)$ is the ordinary nuclear norm by Definition 2.2, not the Schatten 2-norm.
6. The Omega project's [reduction to three block columns](https://www.trureturing.org/knowledge/node/ae3dc404d8dc70ec2d9580ea946dfa146c5463f3fe60c351605543c0ae6d07ee/) concerns the *upper* side $p\ge2$, not (1). Bounded searches for author names, trace/nuclear norm, compression, block rows, Drury, and nonnegative tensors did not locate a prior explicit proof of (1) in this generality or a previous refutation of Li–Zhao's nonnegative expectation. This is not an exhaustive priority search.
