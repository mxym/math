# A support-function criterion involving the width alone

Use the notation of PARALLEL.md, with $n\ge3$, $m=n-1$, and $s_m=|S^m|$. Let $K$ be a full-dimensional compact convex body. Its central symmetral is $M=(K+(-K))/2$. Define $h=h_M>0$, i.e. half the directional width. Assume $h\in C^2(S^m)$ and $Q_h=\nabla_S^2h+hI$ is positive definite. Set
\[
 X(u)=h(u)u+\nabla_S h(u),\qquad \phi(u)=h(u)/|X(u)|^n .
\]

**Criterion.** If $\phi$ is a support function, then $\sigma_K(K)\le2^{-m}$. If $\phi-\epsilon$ is also a support function for some $\epsilon>0$, equality holds only if $K$ is a closed ball. Neither hypothesis restricts the odd part of $h_K$ beyond the requirement that $K$ exists. For an arbitrary compact $E$ whose convex hull $K$ satisfies these hypotheses, $d_K=d_E$ and $\sigma_E(E)\le\sigma_K(K)$, as already noted by Kawohl, Nitsch and Sweers. If $K$ is a ball, its farthest-point measure has strictly positive density on its interior away from the center, so no proper compact subset with that same convex hull has equality.

**Proof.** For every $u$, the exposed face $F_M(u)=(F_K(u)-F_K(-u))/2$ consists of the unique point $X(u)$: this is the support-function derivative formula. Each summand face must therefore itself be a singleton. Write $p_\pm$ for the two support points of $K$ for $\pm u$; by construction $p_+-p_-=2X(u)$. For boundary-area-almost every $x\in\partial K$ with outer normal $u$, $x=p_+$. For any farthest $z\in K$ from $x$ we have
\[
 d_K(x)\ge |x-p_-|=2|X(u)|,\qquad (x-z)\cdot u\le (x-p_-)\cdot u=2h(u).
\]
Thus the flux upper bound of Kawohl–Nitsch–Sweers (Proposition 2.2 and Lemma 2.4 in their 2014 preprint) implies
\[
 s_m\,\sigma_K(K)\le 2^{1-n}\int_{S^m}\phi\,dS_K ,
\]
where $S_K$ is the ordinary surface area measure. This is the higher-dimensional use of their opposite supporting chord comparison, not a new potential-theoretic formula.

Let $H$ have support function $\phi$. It is origin-symmetric since $\phi$ is even. The mixed-volume identity $\int \phi\,dS_L=nV(L[m],H)$ applies. The Alexandrov–Fenchel inequality implies concavity of $V(L[m],H)^{1/m}$ under Minkowski addition with convex coefficients. Apply this to $(K+(-K))/2=M$ and note $V(K[m],H)=V((-K)[m],H)$ by reflection. Hence $\int\phi\,dS_K\le\int\phi\,dS_M$. The right side is exactly $s_m$: at $x=X(u)$ on $\partial M$, the Jacobian of radial projection $x\mapsto x/|x|$ is $(x\cdot u)/|x|^n=\phi(u)$. This projection bijects the boundary with $S^m$ since $M$ contains the origin in its interior. This proves the criterion.

For rigidity, apply the same mixed-volume concavity to $H_0$ with support $\phi-\epsilon$ and to the Euclidean ball separately. Each symmetrization difference is nonnegative and the latter has coefficient $\epsilon>0$, so equality forces $|\partial M|=|\partial K|$. For $n\ge3$, equality in the ordinary surface-area Brunn–Minkowski inequality for full-dimensional summands implies $K$ and $-K$ homothetic. Their volumes agree, so $K$ is centrally symmetric up to translation. The equality assertion of Kawohl–Nitsch–Sweers's central-symmetry theorem now implies it is a ball. The ball attains equality.

**Explicit open class.** By homogeneity, normalize half-width by any $R>0$. For $f=h/R$, suppose $|f-1|$, $|\nabla f|$, and the operator norms of its covariant derivatives of orders two and three on $S^m$ are all at most $\delta=1/[8(n+1)]$, pointwise. Then $Q_f\succ0$. To check the strict support condition, put $q=f^2+|\nabla f|^2$ and $\psi=fq^{-n/2}$. Along any unit-speed great circle, parallel covariant differentiation gives $q\ge (1-\delta)^2$ and
\[
 |q''|\le2[\delta^2+(1+\delta)\delta+\delta^2+\delta^2]\le4\delta
\]
since $\delta\le1/4$. The final two terms bound the squared derivative and second derivative term of the vector field $\nabla f$ along the geodesic. For $L=\log\psi$, this gives
\[
 L''\ge-\frac{\delta}{1-\delta}-\frac{\delta^2}{(1-\delta)^2}
          -\frac{2n\delta}{(1-\delta)^2}
 \ge-\frac{16+32n}{9}\delta>-\tfrac12.
\]
Consequently $\psi''+\psi=\psi(1+L''+(L')^2)\ge\psi/2>0$ in every unit tangent direction. The homogeneous-extension support-function criterion $Q_\psi\succeq0$ now applies also to $\psi-\epsilon$ for any sufficiently small positive $\epsilon$. Rescaling to $\phi=R^{1-n}\psi$ preserves the condition. This explicit neighborhood of constant width includes noncentral bodies of genuinely variable width (e.g. a non-centrally-symmetric constant-width body plus a sufficiently small nonround ellipsoid). It should not be confused with a neighborhood in the Hausdorff distance or a result for all convex bodies. ∎
