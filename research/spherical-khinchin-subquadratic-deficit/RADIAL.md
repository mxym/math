# A quartic deficit below the second moment: the spherical-mean argument

Let $\xi_j$ be independent uniform vectors on $S^{d-1}$, let $G$ have law $N(0,I_d/d)$, and let $\sum_{j=1}^n a_j^2=1$. For each fixed $0<p<2$ there is $c_p>0$ such that
$$
 \mathbb E\Big|\sum_{j=1}^n a_j\xi_j\Big|^p-\mathbb E|G|^p
 \ \ge\ \frac{c_p}{d}\sum_{j=1}^n a_j^4
 \qquad (d\ge3).
 \tag{1}
$$
This addresses the higher-dimensional, positive low-moment question in §3 of Jakimiuk–Tang–Tkocz, *Khinchin inequalities for uniforms on spheres with a deficit*. It does not treat their real-sign problem or their fixed-number-of-summands problem. Here we prove (1) for $d+p>4$. The accompanying proof treats $d=3,\ 0<p\le1$, which completes (1). We draw on the classical spherical-mean/bisubharmonic method and on JTT's Gaussian-radius replacement. The motivation for handling the endpoint separately is that the bi-Laplacian formula changes at $d+p=4$.

## Squared radii

For a smooth function $f$ let $M_f(x,u)$ be the mean of $f(x+\sqrt u\,\xi)$, with $\xi$ uniform on the unit sphere in dimension $d$. For $u>0$, differentiation and the divergence theorem give
$$
 \partial_u M_f(x,u)=\frac1{2d}\mathbb E\Delta f(x+\sqrt u\,U),
$$
where $U$ is uniform in the unit ball of dimension $d$. A uniform point in that ball has the same law as the first $d$ coordinates of a uniform vector on $S^{d+1}$ (e.g. the squared projection length is $\operatorname{Beta}(d/2,1)$ by normalized independent Gaussians). Apply the same differentiation in dimension $d+2$ to the function constant in the two new coordinates. This gives
$$
 \partial_u^2 M_f(x,u)=\frac1{4d(d+2)}\mathbb E\Delta^2 f(x+\sqrt u\,V),
 \tag{2}
$$
where $V$ is the projection to the first $d$ coordinates of a uniform point in the unit ball in dimension $d+2$. In particular $V$ is centered, $|V|\le1$, and is chosen independently of other shifts.

Let $f(x)=|x|^p$ and set $A=p(2-p)(d+p-2)(d+p-4)>0$. For $d+p>4$ the identity
$$\Delta^2f(x)=-A|x|^{p-4}$$
holds distributionally on all of $\mathbb R^d$. Indeed, apply the radial Laplacian twice away from zero. In passing across a sphere of radius $r$ the two worst boundary errors for the first and second Laplacian are $O(r^{d+p-2})$ and $O(r^{d+p-4})$, respectively, hence vanish. Both resulting densities are locally integrable. Smooth by convolution with a nonnegative, centered, radial smooth probability bump of radius $h\le1$, writing $f_h$ for the result and $W_h$ for an independent vector of that law. Then $\Delta^2 f_h(x)=-A\,\mathbb E|x+W_h|^{p-4}$.

## A quantitative replacement

Replace the summands one at a time by independent copies of $a_jG$. At a given step write $a=|a_j|>0$ (zero coefficients can be ignored) and $Y$ for the sum of the other terms, already Gaussianized or not. It is centered, independent of this replacement, with $\mathbb E|Y|^2=1-a^2$. Define $g(s)=\mathbb E f_h(Y+a\sqrt{s}\,\xi)$. Formula (2) yields
$$
 -g''(s)=\frac{Aa^4}{4d(d+2)}
              \mathbb E|Y+a\sqrt{s}\,V+W_h|^{p-4}\qquad (s>0).
 \tag{3}
$$
Differentiation through the $Y$ average is legitimate on compact $s$-intervals in $(0,\infty)$: mollified derivatives on bounded sets are bounded, have at most polynomial growth outside, and $Y$ has moments of every order. Thus $g$ is concave on $[0,\infty)$ by continuity at zero. Since $z^{(p-4)/2}$ is convex and decreasing for $z>0$, the expectation in (3) is bounded below by
$$
 (1-a^2 + a^2s\,\mathbb E|V|^2 + \mathbb E|W_h|^2)^{(p-4)/2}.
 \tag{4}
$$
In particular it is at least $6^{(p-4)/2}$ whenever $0\le s\le5$.

Use $G=\sqrt T\,\xi$ in law, independently of $Y$, where $T\sim\chi_d^2/d$, $\mathbb E T=1$, $\mathbb E(T-1)^2=2/d$, and $\mathbb E(T-1)^4=12/d^2+48/d^3\le28/d^2$ for $d\ge3$. Thus
$$
 \mathbb E\big[(T-1)^2;\ T\le5\big]\ge 2/d-28/(16d^2)\ge 1/d .
$$
Subtract $g(T)$ from its tangent line at 1. By global concavity the gap is nonnegative everywhere. For $T\le5$, integrating the bound (3)–(4) twice along the segment between 1 and $T$ shows that it is at least $Aa^4\,6^{(p-4)/2}(T-1)^2/[8d(d+2)]$. On taking expectations, the tangent's linear term vanishes. Sum the resulting lower bounds over replacements and send $h\downarrow0$ by dominated convergence (the smoothed functions are bounded by $(1+|x|)^p$). The all-Gaussian sum has law $G$. We obtain the explicit coefficient
$$
 \frac{6^{(p-4)/2}p(2-p)}{8d}\,
 \frac{(d+p-2)(d+p-4)}{d(d+2)} .
 \tag{5}
$$
For $d\ge4$ the last ratio is at least $p/12$, since $(d+p-2)/d\ge1/2$ and $(d+p-4)/(d+2)\ge p/6$. For $d=3,\ p>1$ the ratio is also strictly positive for each such $p$. Together with the separate low-dimensional proof this gives a constant as stated in (1). ∎
