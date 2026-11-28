# Thirty-point conditional positivity for a spherical quartic, and a 58-point counterexample

Let $f(t)=t^4-t^2/4$, and $F_{ij}=f(x_i\cdot x_j)$ for unit vectors in a real Euclidean space.

* If there are at most 30 vectors, $b^\mathsf T F b\ge0$ whenever $\sum b_i=0$. No separation condition is needed.
* Consequently for $4\le n\le30$ the maximum, over all $n$-point $60^\circ$ spherical codes in all dimensions, of $\min_{w\ge0,\ \sum w_i=1}w^\mathsf T Fw$ is already attained in dimension $n-2$.
* Conditional positivity does **not** extend to every $60^\circ$ code: an explicit 58-point example below has $b^\mathsf T F b<0$ at total mass zero.

The positive result concerns the **number of points**, not positivity for arbitrary numbers of points on the 29-sphere. No sharp cutoff between 30 and 58, value of the maximized energy, or unrestricted kissing number is asserted. Failure of this mass-convexity proof does not disprove the rank conclusion at larger cardinalities. The starting point is the [twenty-point bipartite-stress theorem](https://github.com/mxym/math/blob/0b3313277b91fb18a6500fa789818b7993d7ae73/research/euclidean-tensor-geometry/KissingMixedEnergyBipartiteStress.md). For the different, classical question of positive-definiteness for *all* code sizes in a fixed sphere dimension, see [DeCorte–Pikhurko, §4](https://academic.oup.com/imrn/article/2016/20/6095/2452923).

## A choice of flattening

Embed the span in $\mathbb R^d$ with $d=30$. Work on the real symmetric matrices with the Frobenius inner product. Write $X_i=x_i x_i^\mathsf T$, and let $T=\sum b_i\,|X_i\rangle\langle X_i|$ act on this matrix space; put $S_0=\sum b_i X_i$. Then $T$ has rank at most 30, **operator trace zero** and $\|T\|_F^2=\sum_{ij} b_i b_j(x_i\cdot x_j)^4$. Also $S_0$ is traceless and $\|S_0\|_F^2=\sum_{ij} b_i b_j(x_i\cdot x_j)^2$. We prove
$$
 \|S_0\|_F^2\le \frac{99}{25}\|T\|_F^2.
$$

Test with any traceless symmetric $S$ of Frobenius norm one and diagonalize it, with eigenvalue vector $\lambda$ of sum zero and norm one. Let $L$ have the following blocks on the symmetric-matrix space:
$$
 A=\frac{\lambda{\bf1}^\mathsf T+{\bf1}\lambda^\mathsf T}{10}
       +\frac45\operatorname{diag}\lambda
 \quad\text{on diagonal coordinates},\qquad
 \frac25(\lambda_i+\lambda_j)\quad\text{on }(E_{ij}+E_{ji})/\sqrt2,\ i<j .
$$
For $X=xx^\mathsf T$, multiplication gives $\langle X,LX\rangle=(x^\mathsf TSx)\|x\|^2$: the coefficient of $x_i^4$ is $\lambda_i$ and of $x_i^2x_j^2$ is $\lambda_i+\lambda_j$. Thus $\operatorname{tr}(LT)=\langle S,S_0\rangle$. There is freedom to distribute the latter coefficient between the two blocks; the displayed coefficients need not agree with the fully symmetrized trace adjoint. Directly $\operatorname{tr}A=0$ and $\|A\|_F^2=1+(d/2-1)/25=39/25$.

Normalize $\|T\|_F=1$ (the zero case follows from the pairing identity). By eigenvalue rearrangement for self-adjoint matrices, it suffices to bound pairings of the signed eigenvalues of $T$ with distinct eigenvalue slots of $L$: in eigenbases the squared overlaps form a doubly stochastic matrix, a convex combination of permutations. At most 30 slots matter, and the assigned coefficients have zero sum and squared sum one. Let $k$ selected slots lie in $A$, with coefficients of squared norm $a^2$, and $m$ in the other block, with coefficient vector $z$ and squared norm $b^2=1-a^2$. Put $s=\sum z$.

## A signed graph incidence bound

Let $B$ have the $m$ distinct rows $e_i+e_j$ of the selected pairs, and $P=I-{\bf1}{\bf1}^\mathsf T/d$. The diagonal of $BB^\mathsf T$ is two and its other entries are zero or one. If $p$ and $q$ are the sums of the positive and the absolute negative entries of $z$, discard the negative cross terms and include all same-sign terms. This gives
$$
 \|PB^\mathsf T z\|^2\le b^2+p^2+q^2-4s^2/d
 \le(1+m/2)b^2+(1/2-4/d)s^2,
$$
since $p-q=s$ and $(p+q)^2\le m b^2$. The off-diagonal block pairing is at most $(2/5)\|PB^\mathsf T z\|$ in absolute value.

When $k\ge2$, $m\le28$, and $1/2-4/d=11/30\le15/d$. Hence this norm is at most $\sqrt{15}\sqrt{b^2+s^2/d}$. In the diagonal block pad the $k$ coefficients with zeros to length $d$. Their sum is $-s$, so subtracting their mean and using $\operatorname{tr}A=0$ bounds that pairing by $\sqrt{39/25}\sqrt{a^2-s^2/d}$. Its sum with the off-diagonal bound has square at most
$$
 39/25+(4/25)15=99/25
$$
by Cauchy–Schwarz. If $k=0$ then $s=0$ and the squared bound is only $(4/25)16$.

For $k=1$ use the sharper $\|A\|_{\rm op}\le6/5$. Indeed in the direction $\mathbf1/\sqrt d$ the scalar block is zero, the coupling to its orthogonal complement has squared norm $(d+8)^2/(100d)=361/750$, and the remaining block has norm at most $(4/5)\max|\lambda_i|\le(4/5)\sqrt{29/30}<79/100$. Since $361/750<(6/5)(6/5-79/100)$, the two-by-two comparison of quadratic forms proves the claim for both signs. Here $s^2=a^2$ and $m\le29$. With $J=31/2$, $h=11/30$, the pairing is bounded by
$$
 (6/5)a+(2/5)\sqrt{J-(J-h)a^2}.
$$
A last Cauchy–Schwarz gives its square at most $(36/25)J/(J-h)+(4/25)J=22444/5675<99/25$. Taking the supremum over $S$ proves the stated tensor inequality. In particular $b^\mathsf TFb\ge\|T\|_F^2/100$.

This is precisely the conditional convexity used in the previously linked theorem. Its remaining stress, bipartition and compactness arguments are independent of the cutoff and therefore give the second assertion.

## An explicit separated obstruction

Take unit poles $u,v$ with $u\cdot v=\kappa=-7/16$. In an orthogonal space take the 28 vertices $z_1,\dots,z_{28}$ of a unit regular simplex, so $z_i\cdot z_j=-1/27$ for $i\ne j$. Put $p=29/56$ and form the code
$$
 u,\quad v,\quad x_i=-\sqrt p\,u+\sqrt{1-p}\,z_i,\quad
 y_i=-\sqrt p\,v-\sqrt{1-p}\,z_i\quad (1\le i\le28).
$$
Within each satellite layer distinct pairs have inner product $1/2$. A pole meets its own layer at $-\sqrt p$, the other at $-\kappa\sqrt p<1/2$. The two cross-layer products, according as the indices agree or differ, are
$$
 c=p\kappa-(1-p)=-635/896,\qquad e=p\kappa+(1-p)/27=-187/896 .
$$
Thus the code has separation at least $60^\circ$. Use signed masses $q,-q,-1/28,+1/28$ on $u,v,$ each $x_i,$ each $y_i$, respectively, with $q=1/5$. Write $H(t)=t(t-1/4)$, so $f(s)=H(s^2)$. Direct summation gives
$$
 \frac12 b^\mathsf TFb =
 q^2(3/4-f(\kappa))
 +\frac{3/4+27f(1/2)-f(c)-27f(e)}{28}
 -2q\{H(p)-H(p\kappa^2)\}
 =-\frac{1394362953}{16112838246400}<0 .
$$
This is a zero-sum direction, so the mass quadratic genuinely fails to be convex on the probability simplex (perturb strictly positive uniform mass by a small multiple). The construction lives in dimension $2+27=29$.

The accompanying [standard-library fraction checker](verify-kissing-thirty-point-flattening.py) verifies the scalar bounds, the flattening coefficient identities on a rational spanning test family, and the negative energy both by the formula and by summing the full signed 58-by-58 kernel matrix.
