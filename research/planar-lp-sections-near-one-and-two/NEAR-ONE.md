# The two-sided neighborhood of one

**Claim.** For each fixed $n\ge4$ there is $\eta_n>0$ such that the [regular plane](README.md) is, up to signed coordinate permutations, the unique global minimizer whenever $|p-1|<\eta_n$. The endpoint result at $p=1$ is prior work. We retain a quadratic lower bound from its proof, then perturb.

Use the frame parameters and local chart $(u,y)$ in [the near-two proof, Sections 1 and 3](PROOF.md); its second-order expansion at two is not needed here. At one, near the regular frame, all $n$ projective row directions are distinct. The section is a symmetric polygon. Its $2n$ vertex rays are perpendicular to the rows, since the gauge $\sum_j\sqrt{w_j}|\cos(\theta-\alpha_j)|$ changes its defining linear form precisely at those rays. Consecutive rays bound triangles of areas $A_a$ with half-apertures $\beta_a$; they sum in angle to $\sum_a\beta_a=\pi$. The sequence of $\beta_a$ consists of two copies of the cyclic list $(\phi_{j+1}-\phi_j)/4$ with the wrap measured positively. For each arc let $I_a$ be the integral of the reciprocal radial function over that arc.

Set $\psi(x)=\sin x/(\cos x)^{1/3}$. The bound for an individual triangle from [Chasapis–Nayar–Tkocz, Lemmas 6–7 and proof of Theorem 1](https://arxiv.org/abs/2109.05645v2), whose polygonal proof they credit to Fedor Nazarov, gives $A_a I_a^2\ge4\psi(\beta_a)^3$. By Hölder,

$$
\Big(\sum_a A_a\Big)\Big(\sum_a I_a\Big)^2
   \ge4\Big(\sum_a\psi(\beta_a)\Big)^3 .
$$

Here $\sum_a I_a=\int_0^{2\pi}\sum_j\sqrt{w_j}|\cos(\theta-\alpha_j)|\,d\theta=4\sum_j\sqrt{w_j}$. Consequently,

$$
\operatorname{area}_1\ge
\frac{(\sum_a\psi(\beta_a))^3}{4(\sum_j\sqrt{w_j})^2},
$$

with equality at the regular frame. The cited theorem independently gives its **global** uniqueness even for competing planes with fewer distinct nonzero rows.

Let $\beta_0=\pi/(2n)$ and $w_*=2/n$. Since

$$
\psi'(x)=\tfrac23\cos^{2/3}x+\tfrac13\cos^{-4/3}x,\qquad
\psi''(x)=\tfrac49\sin x(\cos^{-7/3}x-\cos^{-1/3}x)>0
\quad(0<x<\pi/2),
$$

a Taylor lower bound around $\beta_0$ gives $\sum_a\psi(\beta_a)\ge 2n\psi(\beta_0)+c\sum_a(\beta_a-\beta_0)^2$; the linear terms cancel. Similarly, strict concavity of the square root and $\sum w_j=2$ give $\sum_j\sqrt{w_j}\le n\sqrt{w_*}-c'\sum_j(w_j-w_*)^2$ in a neighborhood. The right side of the area bound increases in its positive numerator sum and decreases in its positive denominator sum, with both partial derivatives bounded away from zero in magnitude near regular. Hence the area excess bounds the sum of both squared deviations from below, times a positive constant. For mean-zero angular increments $\eta_j$,

$$
\sum_a(\beta_a-\beta_0)^2
    =\tfrac18\sum_j(\eta_{j+1}-\eta_j)^2
    \ge c_n\sum_j|\eta_j|^2
$$

by the finite cyclic Poincaré inequality. Since $y$ is the orthogonal projection of $\eta$ to the residual angular subspace, this gives quadratic growth in $|u|^2+|y|^2$.

The integrated area has a continuous frame Hessian jointly in $p$ and the frame near $(1,\mathrm{regular})$. The [moving-cutoff argument, Section 4](PROOF.md) applies unchanged: in each angular patch the sole vanishing factor is $|\sin s|^p$ in a translated integration variable. It is never differentiated in $s$; this is important for $p\le1$. Quadratic growth at one therefore gives a positive definite Hessian there, which remains positive on a fixed convex chart ball for all $p$ sufficiently close to one on either side. Cyclic symmetry makes the regular point stationary for every such exponent, hence the unique minimizer in that ball.

Finally, area is jointly continuous in the frame and $p$ globally on every compact exponent interval inside $(0,\infty)$. Indeed the angular denominator is positive on the compact parameter space by the frame identity $\sum s_j=1$. If minimizers for $p\to1$ stayed outside a neighborhood of the regular orbit, a convergent subsequence would give a different global minimizer at one, contrary to the cited uniqueness. Local uniqueness therefore gives global uniqueness. No step presumes convexity of $B_p^n$ when $p<1$. ∎
