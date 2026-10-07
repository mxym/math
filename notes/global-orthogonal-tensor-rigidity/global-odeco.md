# Global orthogonal approximation of approximately associative cubic tensors

mxym repository account; proof developed with AI assistance, 7 October 2026.

## Scope

This is an independent, unconditional result for **all** real symmetric cubic tensors, including zero weights and repeated weights. It uses no entropy inequality and no OpenAI theorem. The exact connection between associative metrized algebras and orthogonally decomposable tensors is prior work; a principal reference is Boralevi–Draisma–Horobeț–Robeva, *Orthogonal and unitary tensor decomposition from an algebraic perspective*, [arXiv:1512.08031](https://arxiv.org/abs/1512.08031). We give a complete elementary quantitative proof, explicit (large) dimension constants, an optimal homogeneous exponent, and an exact two-dimensional distance formula with its best constant. Whether these quantitative statements overlap existing tensor-perturbation literature remains to be established. No first-result or major-open-problem claim is made.

## 1. Main theorem

Let $T=(T_{ijk})$ be a fully symmetric real cubic tensor on $\mathbb R^m$, $m\ge1$. Its norm is

$$
|T|^2=\sum_{i,j,k=1}^m T_{ijk}^2.
$$

Define symmetric matrices $(X_r)_{ij}=T_{rij}$, and write $A(x)=\sum_r x_rX_r$. Set

$$
\mathcal R(T)=\left(\sum_{r,s=1}^m|[X_r,X_s]|_F^2\right)^{1/2}.
\tag{1}
$$

This quantity is independent of the choice of orthonormal coordinates, since rotations act orthogonally on the coefficient indices and by conjugation on the matrix indices. It is homogeneous of degree two. In terms of the commutative product $x*y=A(x)y$, full tensor symmetry gives $\langle x*y,z\rangle=\langle x,y*z\rangle$. Commuting multiplication operators express associativity: $(x*y)*z=x*(y*z)$. In one direction this follows from associativity directly; in the other, use commutativity and $A(z)A(x)y=A(x)A(z)y$.

Let

$$
\mathcal D_m=\left\{\sum_{i=1}^m\lambda_i u_i^{\otimes3}:
(u_i)\text{ an orthonormal basis},\ \lambda_i\in\mathbb R\right\}.
$$

Zero weights are allowed. Define $C_1=0$ and, for $m\ge2$,

$$
C_m=5m^{3/2}.
\tag{2}
$$

**Theorem 1.** For every fully symmetric real cubic tensor,

$$
\operatorname{dist}(T,\mathcal D_m)\le C_m\sqrt{\mathcal R(T)}.
\tag{3}
$$

In particular, no lower bound on a nonzero weight, no spectral gap, and no norm bound on $T$ is needed. The exponent $1/2$ on $\mathcal R$ cannot be increased in a uniform estimate, even on a norm-bounded set and even in dimension two. The constants (2) are not asserted to be best.

### 1.1 A maximizing vector splits a tensor

Let $p(x)=T(x,x,x)$ and $\lambda=\max_{|x|=1}p(x)$. As $p$ is odd, $\lambda=\max|p(x)|\ge0$. If $\lambda=0$, then $T=0$ by polarization. Otherwise select a maximizing unit vector $v$.

The stationarity equation is $A(v)v=\lambda v$. For a unit $w\perp v$, differentiate $p(v\cos t+w\sin t)$ twice at zero. Its second derivative is

$$
6T(v,w,w)-3\lambda\le0.
$$

Choose coordinates with $v=e_1$ and diagonalize $A(v)$ on its orthogonal complement. This preserves $v$. In these coordinates

$$
X_1=\operatorname{diag}(\lambda,\mu_2,\ldots,\mu_m),
\qquad \mu_i\le\lambda/2.
\tag{4}
$$

Tensor symmetry gives $X_ie_1=\mu_i e_i$ for $i>1$. Therefore

$$
[X_1,X_i]e_1=\mu_i(\mu_i-\lambda)e_i.
$$

The two ordered commutators for each pair $(1,i)$, and the two skew-symmetric entries within each, give

$$
\mathcal R(T)^2\ge4\sum_{i>1}\mu_i^2(\mu_i-\lambda)^2
\ge\lambda^2\sum_{i>1}\mu_i^2.
\tag{5}
$$

This aggregate bound does not presume that $\mu_i$ is nonnegative and avoids estimating each term separately.

Let $T'$ be the restriction of $T$ to $e_1^\perp$. The only nonzero mixed coefficients with index one are $T_{1ii}=\mu_i$ and their permutations. Thus

$$
|T-\lambda e_1^{\otimes3}-T'|^2=3\sum_{i>1}\mu_i^2.
\tag{6}
$$

For $i>1$ let $Z_i$ be the lower-right block of $X_i$. Then

$$
X_i=
\begin{pmatrix}0&\mu_i e_i^T\\\mu_i e_i&Z_i\end{pmatrix},
$$

where $e_i$ now denotes the corresponding complement basis vector. The lower-right block of $[X_i,X_j]$ is

$$
[Z_i,Z_j]+\mu_i\mu_j(e_ie_j^T-e_je_i^T).
$$

Minkowski's inequality on the direct sum of all matrix entries implies

$$
\mathcal R(T')\le\mathcal R(T)+\sqrt2\sum_{i>1}\mu_i^2.
\tag{7}
$$

Indeed the squared norm of the added blocks is
$2\sum_{i\ne j}\mu_i^2\mu_j^2\le2(\sum_i\mu_i^2)^2$.

### 1.2 Proof of Theorem 1

The dimension-one statement is exact: every cubic tensor there already lies in $\mathcal D_1$. Assume the theorem in dimension $m-1$ and abbreviate $R=\mathcal R(T)$.

Polarization gives a bound used in the small-maximum case:

$$
T(x,y,z)=\frac1{48}\sum_{\epsilon\in\{-1,1\}^3}
\epsilon_1\epsilon_2\epsilon_3
p(\epsilon_1x+\epsilon_2y+\epsilon_3z).
$$

For unit vectors $x,y,z$, each argument has norm at most three, hence $|T(x,y,z)|\le(9/2)\lambda$. Fix $x,y$ to basis vectors and optimize over $z$; the coefficient vector in $z$ has Euclidean norm at most $(9/2)\lambda$. Sum over the $m^2$ fixed pairs:

$$
|T|\le(9/2)m\lambda.
\tag{8}
$$

If $\lambda\le\sqrt{mR}$, choose the zero tensor in $\mathcal D_m$. Equation (8) proves (3). This includes $T=0$.

If $\lambda>\sqrt{mR}$, equations (5)–(7) give

$$
|T-\lambda e_1^{\otimes3}-T'|
\le\sqrt{3/m}\sqrt R,
$$

$$
\mathcal R(T')\le(1+\sqrt2/m)R.
$$

By induction choose $S'\in\mathcal D_{m-1}$ with

$$
|T'-S'|\le C_{m-1}\sqrt{(1+\sqrt2/m)R}.
$$

Such a nearest tensor exists: for fixed orthonormal basis, the minimizing weights are the orthogonal projections $T(u_i,u_i,u_i)$; then optimize a continuous function on the compact group $O(m)$. Extend $S'$ by zero in direction $e_1$ and set $S=\lambda e_1^{\otimes3}+S'\in\mathcal D_m$. The triangle inequality yields

$$
|T-S|\le\left[\sqrt{3/m}
+C_{m-1}\sqrt{1+\sqrt2/m}\right]\sqrt R
\le C_m\sqrt R.
$$

To verify the last inequality, for $m\ge2$ use $\sqrt{1+\sqrt2/m}\le1+1/m\le m/(m-1)$. Then

$$
5m^{3/2}-5(m-1)^{3/2}\sqrt{1+\sqrt2/m}
\ge5m(\sqrt m-\sqrt{m-1})
\ge\frac52\sqrt m\ge\sqrt{3/m}.
$$

The actual value $C_1=0$ improves the case $m=2$. This covers $R=0$ as well: a nonzero maximum is then in the second case, every mixed $\mu_i$ is zero, and the induction gives an exact decomposition. All steps involve actual tensor norms, not a sampled numerical maximizer. $\square$

## 2. Exact distance and best constant in dimension two

Every binary cubic has a unique decomposition

$$
p(\cos\theta,\sin\theta)
=a\cos3\theta+b\sin3\theta+c\cos\theta+d\sin\theta.
\tag{9}
$$

In tensor coefficients this says

$$
T_{111}=a+c,\quad T_{112}=b+d/3,\quad
T_{122}=-a+c/3,\quad T_{222}=-b+d.
\tag{10}
$$

Set $A=\sqrt{a^2+b^2}$ and $B=\sqrt{c^2+d^2}$. These letters in this section denote scalars, not multiplication matrices.

**Theorem 2.** In dimension two,

$$
\operatorname{dist}(T,\mathcal D_2)=\sqrt3\,|A-B/3|,
\qquad \mathcal R(T)=4|A^2-B^2/9|.
\tag{11}
$$

Consequently the exact best universal constant is

$$
\operatorname{dist}(T,\mathcal D_2)
\le\frac{\sqrt3}{2}\sqrt{\mathcal R(T)}.
\tag{12}
$$

For nonzero residual, equality holds exactly when $A=0$ or $B=0$. Both zero also gives equality. More generally $A=B/3$ gives zero distance and zero residual.

**Proof.** Equation (10) gives $|T|^2=4A^2+(4/3)B^2$. For any orthonormal pair $u,v$, $u^{\otimes3},v^{\otimes3}$ are orthonormal in tensor space, so the optimal weights are $p(u),p(v)$. Reflections or signs do not change their squared values; all bases are therefore handled by taking $u=(\cos\theta,\sin\theta)$ and $v=(-\sin\theta,\cos\theta)$. A direct trigonometric expansion gives

$$
p(u)^2+p(v)^2
=A^2+B^2+2(ac-bd)\cos4\theta+2(ad+bc)\sin4\theta.
$$

Because $(ac-bd)^2+(ad+bc)^2=A^2B^2$, its maximum is $(A+B)^2$, including $A=0$ or $B=0$. Subtract this from $|T|^2$:

$$
\operatorname{dist}(T,\mathcal D_2)^2
=3A^2+B^2/3-2AB=3(A-B/3)^2.
$$

The off-diagonal entry of $[X_1,X_2]$ is

$$
k=T_{111}T_{122}+T_{112}T_{222}-T_{112}^2-T_{122}^2
=2(B^2/9-A^2).
$$

The two ordered nonzero commutators have squared Frobenius norm $2k^2$ each. Thus $\mathcal R(T)=2|k|$, proving (11). Finally
$(A-B/3)^2\le|A^2-B^2/9|$, since both $A,B$ are nonnegative. For unequal values equality holds exactly when the smaller is zero. This proves (12) and its stated equality cases. $\square$

### Sharpness of the homogeneous exponent

Take the harmonic cubic $p(x,y)=x^3-3xy^2$, with $a=1,b=c=d=0$. Equations (11) give distance $\sqrt3$ and residual four. For $t>0$, the tensor $tT$ has distance $t\sqrt3$ and residual $4t^2$. Hence every estimate with residual power $\alpha>1/2$ fails as $t\downarrow0$, even if one restricts to tensors of norm at most one. This proves the exponent assertion in Theorem 1. Padding by zero coordinates is not needed for this conclusion.

## 3. Relation to other statements and verification boundary

The result is an algebraic error bound for the complete symmetric cubic class. It is distinct from perturbing a **given** orthogonal decomposition by a small tensor and recovering its factors under nonzero-weight or gap assumptions: the data here are measured associativity defects, and the weights can vanish. This distinction does not by itself prove novelty; the full tensor-approximation literature must be compared.

No algorithmic polynomial-time guarantee is asserted. The maximizing-vector induction is a proof of existence, not permission to treat a floating-point critical point as the global maximum. For dimension two the distance is exact without an optimization oracle.

The exact checker tests the binary identities through polynomial coefficient comparison, the tensor block-compression identity in arbitrary rational examples, and homogeneity and negative controls. Those tests are finite evidence; Sections 1–2 contain the all-dimensional proofs. The general maximizing-vector/Hessian argument and induction are not yet Lean-formalized. The separate Lean kernel file belongs to the companion compatibility note and must not be cited as a formalization of this theorem.
