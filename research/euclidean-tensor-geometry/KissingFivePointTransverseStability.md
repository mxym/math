# Transverse stability of five-point planar kissing configurations for a mixed frame energy

Let $f(t)=t^4-t^2/4$. For an ordered tuple $X=(x_1,\dots,x_n)$ of unit vectors, set
$
 E(w,X)=\sum_{i,j} w_iw_j f(x_i\cdot x_j),\qquad
 C(X)=\min_{w_i\ge0,\ \sum_iw_i=1}E(w,X).
$
All sums count ordered pairs and include the diagonal. The five-point capacity bound in the plane is $1/4$. Here we show that every generic planar five-point kissing configuration is a **strict local maximizer modulo planar configurations**, in every ambient dimension. The proof gives a quantitative defect and the exact normal quadratic form. It does not give a global five-point upper bound in dimension three or higher.

## 1. Statement

Let $Y=(y_1,\ldots,y_5)$ lie on the unit circle in a two-plane $P$, with angles $\theta_i$. Assume the five axes are distinct, and that the solution of
$
 \sum_i w_i^0=1,\qquad \sum_i w_i^0e^{2i\theta_i}
 =\sum_i w_i^0e^{4i\theta_i}=0                                      \tag{1}
$
is strictly positive. These assumptions hold for every planar five-point code with angular separation strictly greater than $60^\circ$: the projective nodes are distinct (an antipodal pair leaves no room for three further points at strictly greater separation), and positivity follows from [sharp spacing circle quadrature, statement for doubled angles](https://github.com/mxym/math/blob/e50e33215d387d70ba4d59e325b223dcd8e46075/research/euclidean-tensor-geometry/SharpSpacingCircleQuadrature.md). The criterion (1) also includes weakly separated boundary configurations with distinct axes and positive weights.

**Theorem.** In a neighborhood of $Y$, for every unit five-tuple $X$, not necessarily a kissing configuration, let $\lambda_1\ge\cdots\ge\lambda_5\ge0$ be the eigenvalues of its $5\times5$ Gram matrix. Then
$
 C(X)\ \le\ \frac14-\frac{\min_i w_i^0}{16}
                 (\lambda_3+\lambda_4+\lambda_5).                    \tag{2}
$
Equality $C(X)=1/4$ holds in this neighborhood exactly when the points lie in a two-dimensional linear subspace. The neighborhood size may depend on the base configuration; it can be taken independent of the ambient dimension. Distinctness and strict positivity are needed by our local argument: we claim no such neighborhood theorem here for the remaining planar boundary points.

## 2. Exact normal quadratic form (any number of nodes)

In fact start with any weighted planar tuple $(w,Y)$ satisfying (1), allowing zero weights. Write $z_i\in P^\perp$, $h_i=\|z_i\|$, $V=\sum_iw_i h_i^2$, and consider
$
 x_i(t)=\sqrt{1-t^2h_i^2}\,y_i+t z_i.
$
With the usual Hermitian norm on the complexified normal space put $M_k=\sum_iw_i e^{ik\theta_i}z_i$, $\mu_6=\sum_iw_i e^{6i\theta_i}$, and $V_* = V-2\|M_1\|^2$. Project the vector-valued node function $z$ orthogonally, in the weighted real $L^2$ space (modulo zero weights), off the two node functions $\cos\theta,\sin\theta$, coordinate by coordinate. By (1) these functions are orthogonal, each of squared norm $1/2$, so $V_*$ is the squared norm of the residual.

**Proposition.** The coefficient $Q$ of $t^2$ in $E(w,X(t))$ satisfies
$
 Q=\|M_3\|^2-\tfrac54 V_*
 \ \le\ -\big(\tfrac34-\tfrac12|\mu_6|\big)V_*
 \ \le\ -\tfrac14 V_*.                                               \tag{3}
$
The first bound is sharp for each base with at least one available ambient normal direction. The zero directions on the positive-mass nodes are exactly the infinitesimal tilts $z_i=A y_i$ of the plane.

Indeed $f(\cos u)=1/4+(3\cos2u+\cos4u)/8$; hence the energy at the base is $1/4$. Put $c_{ij}=y_i\cdot y_j$. The quadratic change of $x_i(t)\cdot x_j(t)$ is $z_i\cdot z_j-c_{ij}(h_i^2+h_j^2)/2$. Since $f'(\cos u)=\tfrac52\cos u+\cos3u$, the first term contributes $\tfrac52\|M_1\|^2+\|M_3\|^2$. The second contributes $-\tfrac54 V$, using $\sum_j w_jc_{ij}^2=1/2$ and $\sum_j w_jc_{ij}^4=3/8$ for every $i$. This proves the identity. By (1) both third-harmonic functions are orthogonal to both first-harmonic functions. The Gram matrix of $(\cos3\theta,\sin3\theta)$ on the residual space is $\tfrac12\bigl(\begin{smallmatrix}1+\Re\mu_6&\Im\mu_6\\\Im\mu_6&1-\Re\mu_6\end{smallmatrix}\bigr)$; its largest eigenvalue is $(1+|\mu_6|)/2$. This bounds $\|M_3\|^2$ and gives (3), with equality in the first bound by taking one normal coordinate proportional to the corresponding linear combination of third harmonics.

## 3. Uniform finite remainder

For $\delta=\max_i h_i\le1/16$, at $t=1$ one has
$
 |E(w,X(1))-1/4-Q|\le25\,\delta^2 V.                               \tag{4}
$
To see this set $r_i=\sqrt{1-h_i^2}$, $s=h_i^2+h_j^2$, $c=c_{ij}$, $d=z_i\cdot z_j-sc/2$, and $\Delta=x_i(1)\cdot x_j(1)-c$. Then
$
 |d|\le s,\qquad \Delta=d-\tfrac12(r_i-r_j)^2c,\qquad
 |\Delta-d|\le g\delta^2 s,\quad g=[8(1-\delta^2)]^{-1}.
$
The last bound uses $(h_i^2-h_j^2)^2\le\delta^2s$ and $(r_i+r_j)^2\ge4(1-\delta^2)$. On $[-1,1]$, $|f'|\le7/2,\ |f''|\le23/2$. Under the product weights, $\mathbb E s=2V$ and $\mathbb E s^2\le4\delta^2V$. Taylor's inequality now gives (4), since $7g+23(1+g\delta^2)^2<25$. In particular, whenever $M_1=0$ one has
$
 E(w,X(1))\le1/4-(1/4-25/256)V\le1/4-V/8.                         \tag{5}
$

## 4. Finding the plane and the positive weights simultaneously

On five distinct projective nodes, the real system (1) is invertible: a nonzero trigonometric polynomial of degree at most two in the doubled angle has at most four distinct zeros. Thus $w(y)$ depends smoothly on nearby normalized planar directions, remains positive, and can be arranged to have $\min_iw_i(y)\ge\min_iw_i^0/2$.

In fixed orthonormal coordinates $P\oplus P^\perp$, let $R_A$ be the exponential of the skew matrix with off-diagonal blocks $(-A^\mathsf T,A)$, $A:P\to P^\perp$. Decompose $R_A^{-1}x_i=(p_i,z_i)$, $y_i=p_i/\|p_i\|$, and impose
$
 \Psi(A;X)=\sum_i w_i(y)\,z_i y_i^\mathsf T=0 .
$
At $A=0,X=Y$, the normals vanish. The derivative in $A$ is
$-\dot A\sum_iw_i^0 y_i y_i^\mathsf T=-\dot A/2$ by (1); the derivatives of the other factors are multiplied by $z_i=0$. The implicit function theorem supplies $A(X)$ for all nearby configurations. In its rotated coordinates we have exactly $M_1=0$, and by continuity $\delta\le1/16$. Apply (5) to these feasible weights. If $P'=R_{A(X)}P$, then
$
 V\ge(\min_i w_i^0/2)\sum_i\|\operatorname{proj}_{(P')^\perp}x_i\|^2
 \ge(\min_i w_i^0/2)(\lambda_3+\lambda_4+\lambda_5),
$
where the last inequality is the variational characterization of the sum of the eigenvalues outside the first two. This proves (2). Every coplanar configuration has energy at least $1/4$ for every weight by the Fourier identity above, so (2) proves the equality statement as well. For ambient uniformity apply the argument in $\mathbb R^7$: the span of the base plane and the five perturbed vectors has dimension at most seven and embeds isometrically there fixing the base. Both sides of (2) are Gram invariants.

## 5. Sharpness of the normal coefficient

For the six signed ends of three regular axes, take $w_i=1/6,\ \theta_i=i\pi/3,\ z_i=(-1)^i h v$ with fixed unit normal $v$. Then $\mu_6=1,\ M_1=0,\ Q=-V/4$. The perturbed antipodes remain antipodes; all cross-axis products have absolute value $|1/2-3h^2/2|$. Thus $E-1/4=(2/3)f(1/2-3h^2/2)=-h^2/4+O(h^4)$.

The same universal coefficient cannot be improved even as a uniform asymptotic estimate for generic five-point bases and their *optimized* weights. Take five consecutive vertices of a regular hexagon and approach them by strict five-point codes, for instance by interpolating their successive gaps with those of a regular pentagon. Then $e^{6i\theta_i}\to1$ after fixing the first angle, so $|\mu_6|\to1$. At each strict base choose scalar normal data in the top third-harmonic direction of (3); it has $M_1=0$. Optimizing the weights does not alter the quadratic coefficient: the base matrix $F_{ij}=f(y_i\cdot y_j)$ is positive definite by the Fourier expansion and the five-node Vandermonde argument. At sufficiently small $t$, $F(t)$ remains positive definite; the optimum is the positive vector $F(t)^{-1}\mathbf1/(\mathbf1^\mathsf TF(t)^{-1}\mathbf1)=w^0+O(t^2)$. The fixed-weight excess over the optimum is its $F(t)$-squared distance to that optimum, hence $O(t^4)$. Take the small-$t$ limit at each base first. This sharpness concerns (3), not the coarser neighborhood constant in (2).

**Context and replay.** The mixed kernel and optimization over weights differ from the global fixed-measure comparisons for pure powers in [Ehler–Okoudjou, *Minimization of the probabilistic $p$-frame potential*](https://arxiv.org/abs/1101.0140). The local result uses no dimension-specific estimate and is not a solution of either general kissing-number problem. Run `python3 verify-kissing-five-point-transverse.py` for exact rational checks of the quadratic formula, finite error and six-end sharpness; the neighborhood and sharpness arguments are analytic proofs, not deductions from samples.
