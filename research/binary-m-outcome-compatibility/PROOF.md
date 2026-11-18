# A sharp compatibility threshold for binary and m-outcome POVMs

Let $d\ge2$ and $m\ge2$ be integers. A POVM is a family of positive semidefinite matrices summing to $I_d$; zero effects are allowed. For an $n$-outcome POVM $E$ define its uniform-noise version $E_i(s)=sE_i+(1-s)I_d/n$. Compatibility means that the two noisy POVMs are the marginals of one joint POVM.

**Theorem.** The minimum, over all binary/$m$-outcome pairs on $\mathbb C^d$, of the largest common compatible visibility is
$$
s_* = \frac12\left(1+\frac{1}{1+\sqrt m}\right).
$$
This is the setting of [Bluhm et al., Definitions 2.13, 2.15, 2.16 and Conjecture 6.6](https://arxiv.org/pdf/2512.17706v1). Their real-qubit theorem and sharp example are antecedents; see [sources](SOURCES.md).

## 1. An exact test for compatibility with every binary measurement

Write the first POVM as $(I\pm A)/2$ for a Hermitian contraction $A$. For the second POVM $B_1,\dots,B_m$, write
$$
e=(1-s)/m,\qquad C_j=eI+sB_j .
$$
A family $G_{\pm,j}$ with second marginal $C_j$ must have the form $(C_j\pm D_j)/2$. These effects are positive precisely when $-C_j\le D_j\le C_j$; their first marginal is $(I\pm sA)/2$ precisely when $\sum_j D_j=sA$. Thus every noisy binary measurement is compatible with this fixed noisy second measurement if and only if
$$
s[-I,I]\;\subseteq\;\sum_j[-C_j,C_j],
$$
where the right side is a Minkowski sum of order intervals.

Both sides are compact convex subsets of the real vector space of Hermitian matrices, with pairing $\operatorname{Tr}(TD)$. Inclusion is equivalent to domination of the support functions in every Hermitian direction $T$. The interval $[-C,C]$ consists of $C^{1/2}H C^{1/2}$ for Hermitian contractions $H$. For singular $C$, the positive matrices $C\pm D$ must each annihilate $\ker C$, since their nonnegative quadratic forms on each kernel vector sum to zero. One can then conjugate by the inverse square root on the support. Maximizing over $H$ gives the trace norm, so the exact condition is
$$
\sum_j \lVert C_j^{1/2}T C_j^{1/2}\rVert_1\;\ge\;s\lVert T\rVert_1
\qquad\text{for every Hermitian }T. \tag{1}
$$

## 2. Two positive matrices with a common lower bound

Use unsquared fidelity $F(P,Q)=\operatorname{Tr}\sqrt{P^{1/2}QP^{1/2}}$.

**Lemma.** Suppose $R>0$, $0\le X,Y\le R$, $e>0$ and $s\ge0$. Set $b=\sqrt{e(e+s)}-e$. Then
$$
 F(eR+sX,eR+sY)\ \ge\ e\operatorname{Tr}R+b(\operatorname{Tr}X+\operatorname{Tr}Y). \tag{2}
$$

**Proof.** Recall the standard variational expression for $P,Q>0$:
$$
 F(P,Q)=\tfrac12\inf_{H>0}\operatorname{Tr}(PH+QH^{-1}). \tag{3}
$$
Indeed, setting $L=P^{1/2}HP^{1/2}$ and $M=P^{1/2}QP^{1/2}$ changes the expression inside the trace to $\operatorname{Tr}(L+ML^{-1})$. Its excess over $2\operatorname{Tr}\sqrt M$ equals $\lVert L^{1/2}-L^{-1/2}M^{1/2}\rVert_{\mathrm{HS}}^2$, zero for $L=M^{1/2}$.

In an orthonormal eigenbasis of any $H>0$, take a unit vector $u$ with eigenvalue $h$. Put $r=\langle u,Ru\rangle$, $x=\langle u,Xu\rangle/r$ and $y=\langle u,Yu\rangle/r$. Here $r>0$ and $x,y\in[0,1]$. The contribution to half the trace in (3) is
$$
 \tfrac r2\big[(e+sx)h+(e+sy)/h\big]\ \ge\ r\sqrt{e+sx}\sqrt{e+sy}.
$$
On $[0,1]$, the square root lies above its chord:
$$
 \sqrt{e+sx}\ \ge\ \sqrt e+(\sqrt{e+s}-\sqrt e)x.
$$
Multiply the two nonnegative scalar bounds at $x,y$ and discard the nonnegative term in $xy$. The contribution is at least $r(e+b(x+y))$. Summing and taking the infimum gives (2). There is no assumption that $R,X,Y$ commute. ∎

## 3. The dimension-independent lower bound

Fix $T=T^*\ne0$. Let $K=\operatorname{supp}|T|$, let $J:K\to\mathbb C^d$ be inclusion, and put $R=J^*|T|J$ and $S=\operatorname{sgn}(T)|_K$. Then $R>0$, $S$ is a self-adjoint unitary commuting with $R$, and $T=JRSJ^*$. For $B=B_j$, define
$$
 X=R^{1/2}J^*BJR^{1/2},\qquad Y=SXS.
$$
Both are in $[0,R]$ and have the same trace. With $C=eI+sB$, define rectangular maps $M=C^{1/2}JR^{1/2}$ and $N=MS$. When $s<1$ we have $e>0$, so these maps are injective. Now $M^*M=eR+sX$, $N^*N=eR+sY$, and $MN^*=C^{1/2}TC^{1/2}$. Polar decomposition on either side shows that the nonzero singular values of $MN^*$ are those of $(M^*M)^{1/2}(N^*N)^{1/2}$. Hence (2) gives
$$
 \lVert C^{1/2}T C^{1/2}\rVert_1
   =F(eR+sX,eR+sY)
   \ \ge\ e\operatorname{Tr}R+2b\operatorname{Tr}X . \tag{4}
$$
This takes account of the compression $J^*BJ$ without assuming $B$ preserves $K$. The [alternative proof](TWO-PROJECTION-PROOF.md) establishes (4) without fidelity.

Since $\sum_j B_j=I$, the corresponding $X_j$ sum to $R$. Thus
$$
\sum_j\lVert C_j^{1/2}T C_j^{1/2}\rVert_1
\ \ge\ f_m(s)\lVert T\rVert_1,\qquad
 f_m(s)=(m-2)e+2\sqrt{e(e+s)}. \tag{5}
$$
The inequality is immediate for $T=0$ and extends by continuity to $s=1$. From (1), $s\le f_m(s)$ is sufficient for every pair.

## 4. Sharpness

Use the source paper's example on a qubit: $A=\sigma_x$ and $B=(|0\rangle\langle0|,|1\rangle\langle1|,0,\dots,0)$. Let $T=\sigma_x/2$; then $\lVert T\rVert_1=\operatorname{Tr}(TA)=1$. The first two $C_j$ have diagonal entries $e+s,e$ in opposite order and each contributes $\sqrt{e(e+s)}$ to (5). Each of the other $m-2$ terms contributes $e$. Thus the right-hand support function in direction $T$ is exactly $f_m(s)$, whereas the point $sA$ pairs with $T$ to give $s$. For $s>f_m(s)$ this concrete pair is therefore incompatible. In higher dimension, form a direct sum with any pair of the appropriate outcome counts on the complement; compressing a putative joint measurement to the qubit summand would give a forbidden one there.

Finally, $f_m(s)=1-(\sqrt{e+s}-\sqrt e)^2$ decreases strictly from $1$ to $0$ as $s$ increases from $0$ to $1$. Put $r=\sqrt m$ and $s=(r+2)/(2(r+1))$. Then
$$
 e=\frac{1}{2r(r+1)},\qquad e+s=\frac{r+1}{2r},\qquad
 \sqrt{e(e+s)}=\frac1{2r}.
$$
Substitution gives $f_m(s)=s$, the unique crossing. Together the universal lower bound and the sharp obstruction prove the theorem. ∎
