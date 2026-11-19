# The low-moment seam on the two-sphere

We prove (1) of RADIAL.md for $d=3$ and $0<p\le1$. Constants in this section may depend on $p$, never on the number of coefficients. Let $m_p=\mathbb E|N(0,1/3)|^p$. For any rotationally invariant vector in dimension 3, its first-coordinate absolute $p$-moment is $1/(p+1)$ times its norm $p$-moment: the direction is uniform (away from 0) and the first coordinate of a uniform direction is uniform on $[-1,1]$. Hence it is equivalent to show
$$
 \mathbb E\Big|\sum_j a_j U_j\Big|^p-m_p \ \ge\ b_p\sum_j a_j^4
 \tag{6}
$$
for independent uniforms on $[-1,1]$, normalized by $\sum a_j^2=1$. We omit zero coefficients.

## A uniform estimate near the diffuse end

Write $h(t)=|\sin t/t|$ (with $h(0)=1$), $g(t)=e^{-t^2/6}$, and put
$$
 D_p(s)=\kappa_p\int_0^\infty
  [e^{-t^2/6}-h(t/\sqrt{s})^s]\,t^{-p-1}\,dt,\qquad s\ge1 .
$$
Here $\kappa_p^{-1}=\int_0^\infty(1-\cos t)t^{-p-1}\,dt>0$. The fractional moment identity used by Chasapis–Gurushankar–Tkocz (CGT), Lemma 4 in arXiv:2105.14079v3, follows immediately by scaling and Tonelli. Independence and weighted arithmetic–geometric mean yield
$$
 \prod_j {\sin(a_j t)\over a_j t}
 \ \le\ \prod_j h(a_jt)
 \ \le\ \sum_j a_j^2 h(a_jt)^{1/a_j^2}.
$$
It follows exactly as in CGT §2 that the left side of (6) is at least $\sum_j a_j^2D_p(1/a_j^2)$.

There exist $S_p<\infty$ and $b_p'>0$ such that $D_p(s)\ge b_p'/s$ for all $s\ge S_p$. Indeed $\log(\sin u/u)=-u^2/6-u^4/180+O(u^6)$ at zero, so choose $u_0>0$ small and $c>0$ such that $\log h(u)\le-u^2/6-cu^4$ there. For $t\le u_0\sqrt s$ the integrand difference is nonnegative; on $1\le t\le2$ it is at least $e^{-t^2/6}(1-e^{-ct^4/s})\ge c'/s$ for large $s$. On $t>u_0\sqrt s$ its negative part integrates against $t^{-p-1}$ to at most $(\sup_{u\ge u_0} h(u))^s(u_0\sqrt s)^{-p}/p$, exponentially small since $h(u)<1$ for $u>0$ and $h(u)\to0$. This proves the estimate. Also $D_p(s)$ is continuous on each compact subinterval of $[1,\infty)$ by dominated convergence: the difference is uniformly $O(t^2)$ near zero and globally bounded.

## Completing the range $0<p<1$

We use two specific results **from CGT**, not a new proof of their sharp qualitative inequality. Under $t=\sqrt s\,u$ we get
$$
 D_p(s)=\kappa_p s^{-p/2} H(p,s),\qquad
 H(p,s)=\int_0^\infty [g(u)^s-h(u)^s]u^{-p-1}\,du.
$$
CGT Lemmas 17–18 and Claims A and B of the proof of Lemma 18 give strict positivity of $H(p,s)$ for $s\ge2$, all $0<p<1$, and for $s\ge1$ if $0.6<p<1$. To be precise about strictness at the base exponents: in Claim A their comparison for $H(p,2)$ uses a strictly concave difference vanishing at both endpoints $p=0,1$; Claim B shows $H(0.6,1)>0$ and monotonicity over the needed range. The normalized integral in their sign-change lemma is nondecreasing in $s$, which propagates these strict base bounds. Their threshold numbers are not asserted to be optimal.

For $13/20<p<1$, positivity on $[1,S_p]$, continuity and the large-$s$ estimate give $\inf_{s\ge1}sD_p(s)>0$. This proves (6).

For $0<p\le13/20$, positivity at $s=2$ and continuity extend the valid range slightly: for some $0<\delta<1$,
$$
 \inf_{s\ge2-\delta} sD_p(s)>0 .
$$
This proves (6) if all $a_j^2\le1/(2-\delta)$. Otherwise write $a=\max_j|a_j|$ and $x=(1-a^2)/a^2\in[0,1-\delta]$. CGT Theorem 21 (valid for $0<p<0.69$, hence throughout the present case) applies to the first coefficient normalized to one, and to collinear coefficient vectors $a_j e_1/a$ for the rest. It gives
$$
 \mathbb E\Big|\sum_j a_jU_j\Big|^p
 \ \ge\ m_p\,a^p\,[2\phi(1)-\phi(2-x)],
 \qquad \phi(u)=(1+u)^{p/2}.
$$
One nonzero summand is covered by adjoining a zero coefficient. Since $a^p\phi(x)=1$ and $\phi$ is strictly concave, $2\phi(1)-\phi(2-x)-\phi(x)$ is strictly positive on the compact interval $[0,1-\delta]$. Also $a$ is bounded below in this case, so the excess over $m_p$ is at least a positive constant depending only on $p$. This implies (6) since $\sum a_j^4\le1$.

## The endpoint $p=1$

If $\max_j|a_j|\le S_1^{-1/2}$, the large-$s$ integral estimate already proves (6). For larger coefficients we work with the three-dimensional norms, without making any assertion about $H(1,s)$ at finite $s$.

For $x\in\mathbb R^3$, $y=|x|$, $r=\sqrt s$, direct integration of $(y^2+r^2+2yru)^{1/2}$ over the uniform $u\in[-1,1]$ gives
$$
 M_y(s)=\mathbb E|x+\sqrt s\,\xi|=
 \begin{cases}
 y+s/(3y), & r\le y,\ y>0,\\
 \sqrt s+y^2/(3\sqrt s), & r\ge y,\ s>0 .
 \end{cases}
$$
Set $M_0(0)=0$. For $y>0$ the branches meet with matching first derivatives. The second derivative on $s>y^2$ is $(y^2-s)/(4s^{5/2})<0$; the lower branch is affine. Hence $M_y$ is globally concave and is not affine on $[0,\infty)$ for any finite $y\ge0$.

With $T\sim\chi^2_3/3$, full support on $(0,\infty)$ and $\mathbb ET=1$, the Jensen gap $J(a,y)=M_y(a^2)-\mathbb E M_y(a^2T)$ is nonnegative, strictly positive for every $a>0$ and finite $y$. This follows from concavity with strict curvature on an open interval visited by $a^2T$. The gap is continuous in $(a,y)$ by the norm triangle inequality and $\mathbb E\sqrt T<\infty$. Therefore $J(a,y)$ has a positive minimum for $S_1^{-1/2}\le a\le1,\ 0\le y\le2$ (choose $S_1\ge2$). In replacing the maximum coefficient's sphere by its Gaussian-radius version, the residual $Y$ satisfies $\mathbb E|Y|^2\le1$ and so $\Pr(|Y|\le2)\ge3/4$. This one replacement gains a fixed positive amount; every other replacement has a nonnegative Jensen gap. Thus the total spherical-to-Gaussian moment gap dominates a positive constant times $\sum_j a_j^4$ when the maximum coefficient is large. Converting back to (6), or using the spherical statement directly, completes the proof. ∎
