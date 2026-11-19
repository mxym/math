# Acute random triangles under a common ellipsoidal deformation

Let $d\ge2$ and let $H$ be a fixed real symmetric $d\times d$ matrix. Put $A_t=\exp(tH/2)$ for $t\ge0$. With the same random vectors $X_1,X_2,X_3$ in every comparison, let $p(t)$ denote the probability that the Euclidean triangle with vertices $A_tX_1,A_tX_2,A_tX_3$ is acute.

**Theorem.** In either of the following settings, $p(t)$ is strictly decreasing on $[0,\infty)$ if $H$ is not scalar, and is constant otherwise.

1. $d\ge3$ and $X_i=r_iU_i$, where $r_i>0$ are any prescribed (not necessarily equal) lengths and $U_i$ are independent uniform unit vectors.
2. $d=2$ and the $X_i$ are iid from a rotationally invariant absolutely continuous law with a radially nonincreasing density.

In (1) one may also mix the positive radii, even jointly, provided the directions remain independent uniform vectors conditional on the radii. In particular in every $d\ge2$, among all uniform **solid ellipsoids** the ball uniquely maximizes the probability, up to translations and scale. More precisely, the probability strictly decreases along every nonscalar logarithmic stretch of a ball. By polar decomposition, every invertible affine image is covered at the individual endpoint of such a ray. Common translations and orthogonal factors do not affect angles. Uniform surface area on a general ellipsoid is not the affine image of uniform spherical surface area; we do not identify those sampling models.

**1. The one-vertex comparison.** Designate the vertex $X$, one other endpoint $Y$, and the third $Z$. Write $e=X/|X|$, $u=(X-Y)/|X-Y|$ and condition on $|X|=r>0, |Y|=s>0$. In (1), also fix the third radius $R$. In (2) leave the third point independent and unconditioned. Let
$$
 F(z)=\Pr(n\cdot Z\le z)-\tfrac12
$$
for any unit $n$; the definition does not depend on its direction. Its density $f=F'$ is even and nonincreasing on $[0,\infty)$, and $F$ is odd and nondecreasing. In (1) the density is proportional to $(1-z^2/R^2)^{(d-3)/2}$ on $(-R,R)$ and zero off that interval; the proportionality constant is positive. This follows by the usual unit-sphere projection density (or normalizing a vector of independent standard Gaussians). In (2), if the planar density is $h(|x|)$, the projection density is $\int_{\mathbb R}h(\sqrt{z^2+y^2})\,dy$, directly giving the assertion. No integrability of a derivative of $f$ is required.

The vertex angle at $A_tX$ is nonobtuse exactly when $n_t\cdot Z\le n_t\cdot X$, where
$$
 n_t=\frac{e^{tH}u}{|e^{tH}u|},\qquad \alpha_t=u\cdot n_t>0 .
$$
This follows by taking the scalar product of $A_t(X-Y)$ and $A_t(X-Z)$. Right angles are null: condition on $X,Y$ and use the continuous projection law of the independent $Z$. All points are distinct and noncollinear almost surely (a fixed line meets a positive-radius sphere in at most two points, also null in the absolutely continuous case).

By joint rotational invariance $u$ is uniform, and the conditional law of $c=e\cdot u$ is independent of $u$. Given $u,c$, the transverse direction of $e$ is uniform on the unit sphere of $u^\perp$; this includes the two-point sphere when $d=2$. Hence
$$
 \mathbb E[F(n_t\cdot X)\mid u,c]
 = G_{\alpha_t}(c):=\mathbb E F\!\left(r\alpha_t c+
 r\sqrt{(1-c^2)(1-\alpha_t^2)}\,V\right),
$$
where $V$ is the first coordinate of that transverse direction. Only its symmetry and $|V|\le1$ will be used; the formula also applies at $\alpha_t=1$.

For $a,b\ge0$, $J(a,b)=(F(a+b)+F(a-b))/2$ increases weakly in $a$ and decreases weakly in $b$. The first is monotonicity of $F$. For the second, its a.e. derivative in $b$ is $(f(a+b)-f(a-b))/2\le0$ because $a+b\ge |a-b|$, and the functions on bounded $b$-intervals are absolutely continuous. Thus, by pairing $V$ with $-V$, for $c>0$ the function $G_\alpha(c)$ increases weakly in $\alpha\in[0,1]$: its location increases and its noise amplitude decreases. It also satisfies $G_\alpha(-c)=-G_\alpha(c)$.

**2. Signed latitude of a random edge.** Let $\mu$ be the conditional law of $c$ just described. Its measure on $(0,1]$ dominates the reflection of its measure on $[-1,0)$. If $s\le r$, then $c=(r-e\cdot Y)/|X-Y|>0$ almost surely, so the claim is immediate, including equal radii. If $s>r$, fix $e$ first. In the direction $-u$ the ray from $X=re$ meets the sphere of radius $s$ at the unique positive distance
$$
 \ell=rc+L(c),\qquad L(c)=\sqrt{s^2-r^2+r^2c^2}.
$$
The angular density of $u$ relative to uniform solid angle is proportional to $\ell^{d-1}/L(c)$. Indeed, the area of a surface patch projects radially to solid angle by the factor $|u\cdot Y/s|/\ell^{d-1}=L(c)/(s\ell^{d-1})$; equivalently this is the Jacobian of a radial graph. Under uniform $u$ the latitude factor is even in $c$, proportional to $(1-c^2)^{(d-3)/2}$. For $0<c<1$, $L(c)+rc>L(c)-rc>0$, so the density strictly dominates its reflection there. The scalar law obtained with fixed $e$ is the unconditional one by rotation; as $u$ is uniform even conditional on $c$, it is also the required law at every $u$ up to null sets. No singular Jacobian is needed at $s=r$.

Integrate the odd function $G_\alpha$ against $\mu$: only the nonnegative measure $\mu(dc)-\mu(-dc)$ on positive latitudes contributes. Therefore the conditional probability of a nonobtuse angle at $A_tX$ given $u,r,s$, namely $1/2+\int G_{\alpha_t}(c)\,d\mu(c)$, increases weakly in $\alpha_t$.

**3. Monotonicity and strictness.** For fixed unit $u$ write $m(t)=u^T e^{tH}u=\sum_j w_j e^{t\lambda_j}$ in an eigenbasis, $w_j\ge0$ and $\sum w_j=1$. Then $\alpha_t=m(t)/\sqrt{m(2t)}$, and the logarithmic derivative is $(\log m)'(t)-(\log m)'(2t)\le0$, since $(\log m)''$ is the variance under the exponentially tilted weights. It is negative for $t>0$ whenever $u$ has components in at least two distinct eigenspaces. A uniform $u$ has this property almost surely if $H$ is nonscalar. This proves that each nonobtuse-vertex probability is nonincreasing. Since a nondegenerate triangle has at most one obtuse angle and right angles have probability zero, $p(t)$ is the sum of the three nonobtuse-vertex probabilities minus two.

In (1) choose $X$ with the smallest radius, so $r\le s,R$. The positive latitude imbalance has nonzero mass on $(0,1)$, by §2 (when $s=r$ all the mass is there). The function $F$ is strictly increasing throughout $[-r,r]$. For $0\le\alpha_1<\alpha_2\le1$, $0<c<1$, put $a_i=r\alpha_i c$, $b_i=r\sqrt{(1-c^2)(1-\alpha_i^2)}$. Then $a_2>a_1$, $b_2\le b_1$, and for $|v|\le1$ both $a_i\pm b_2 |v|$ belong to $[-r,r]$: the upper bounds follow from $a_i+b_2\le a_2+b_2\le r$ by Cauchy–Schwarz and the lower bounds from $0\le b_2\le r$. Consequently $J(a_2,b_2|v|)>J(a_1,b_2|v|)\ge J(a_1,b_1|v|)$, giving strict improvement on the positive imbalance. For any $0\le t_1<t_2$ this vertex's probability strictly drops, and the other two cannot increase.

In (2), choose any $h_0>0$ small enough that the radial density is positive on the open ball of radius $2h_0$ (a nontrivial nonincreasing radial probability density has this property). Then $F$ is strictly increasing on $[-h_0,h_0]$. There is positive probability that $0<r<h_0$ and $s>r$, by independence and positivity of density on the ball. On this event the same strictness argument applies, while elsewhere nonstrict comparison holds. This finishes both cases.

**Scope.** This treats arbitrary eccentricity inside the ellipsoid class of Hall's conjecture, not arbitrary convex bodies. In dimension two no claim is made for arbitrary unequal fixed shells. In dimensions three and above, conditioning on the radii compares entire radial laws with their affine images, not different radial distributions. One may combine the theorem with separately established radial extremizers, but those radial comparisons are not part of this proof. No formal verification or external peer review is claimed.
