# The uniform sphere minimizes radial obtuse-triangle probability in sufficiently high dimension

Yongxian Zhang

Take three independent uniform directions on the Euclidean unit sphere in dimension $d$. Multiply them by any three prescribed positive radii and connect their endpoints by straight segments. We prove that, in every sufficiently large dimension, the probability of obtaining an obtuse triangle is uniquely minimized, up to scale, by giving all three vertices the same radius. In particular, amongst nondegenerate iid samples from rotation-invariant laws, the only minimizing laws are uniform on a sphere. The common-scale value has an exact beta representation and a sharp asymptotic. This is not a minimization theorem over arbitrary laws in the problem of Drivas and Retakh: in fact arbitrary laws achieve exponentially smaller probabilities.

## 1. Probability kernel and the common-sphere value

Write $a=(d-1)/2$, $c_a=B(1/2,a)^{-1}$. The scalar product of a uniform direction with any fixed unit vector has density $c_a(1-t^2)^{a-1}$ on $(-1,1)$; for example, normalize a vector of independent standard normal coordinates, so the squared first coordinate is $\mathrm{Beta}(1/2,a)$, with independent uniform sign. Let $H_a(w)$ be the strict upper tail of this scalar product, equal to one for $w\le-1$ and zero for $w\ge1$. For positive radii $r_i$ let $p_i$ be the probability of an obtuse angle at vertex $i$ and $P_d=\sum_i p_i$. Nondegeneracy and the probability-zero right-angle exceptions follow by conditioning on two directions and using the continuous spherical marginal; under positive radii the difference or sum vector used in such conditioning is nonzero almost surely. At most one angle can be obtuse. With $A=r_j/r_i, B=r_k/r_i$,
$$
 p_i=\int_{-1}^1 c_a(1-t^2)^{a-1}H_a(w(t,A,B))\,dt,\qquad
 w(t,A,B)=\frac{1+ABt}{\sqrt{A^2+B^2+2ABt}}.                 \tag{1}
$$
Indeed condition on both other directions, of dot product $t$. The inequality at $i$ requires its independent unit direction to have projection larger than $w$ on the direction of $A U_j+B U_k$.

When $A=B=1$, $w=\sqrt{x}$ where $x=(1+t)/2$. Write $p_0=p_i(1,1,1)$, $S_d=3p_0$. Then for independent $X\sim\mathrm{Beta}(a,a)$, $Y\sim\mathrm{Beta}(1/2,a)$,
$$
  S_d=\tfrac32\Pr(Y>X)
  \sim\frac{9}{4\sqrt{\pi a}}\left(\frac{16}{27}\right)^a.       \tag{2}
$$
For the equivalent, the unnormalized tail integral at $x$ equals
$$
  \int_x^1 y^{-1/2}(1-y)^{a-1}\,dy
  =\frac{(1-x)^a}{a}\,\mathbb E[(x+(1-x)V)^{-1/2}],
  \qquad V\sim\mathrm{Beta}(1,a).
$$
The expectation is at most $x^{-1/2}$, and equals $x^{-1/2}(1+O(1/a))$ uniformly on each compact subinterval of $(0,1)$, by the mean-value theorem and $\mathbb EV=1/(a+1)$. Consequently
$$
 p_0\sim\frac{B(a-1/2,2a)}{2a B(a,a)B(1/2,a)}
 =\frac{\Gamma(a-1/2)\Gamma(2a)^2\Gamma(a+1/2)}
        {2a\sqrt\pi\,\Gamma(3a-1/2)\Gamma(a)^3}.
$$
Indeed the integrable beta density corresponding to the upper bound is proportional to $x^{a-3/2}(1-x)^{2a-1}$. Its mean tends to $1/3$ and its variance tends to zero; on every fixed compact neighborhood of $1/3$ the upper bound is relatively sharp. This also proves that for every fixed neighborhood of $t=-1/3$, the integral in (1) restricted there is asymptotic to $p_0$ in the equal case. Stirling's formula gives (2). The exponent comes from the interior maximum of $4x(1-x)^2$ at $x=1/3$.

## 2. Uniform second-order comparison near one shell

Put $u_i=a(\log r_i-\tfrac13\sum_h\log r_h)$. On the plane $\sum u_i=0$, we claim convergence with continuous derivatives through order two on each compact set:
$$
 \frac{P_d(e^{u_1/a},e^{u_2/a},e^{u_3/a})}{S_d}
 \longrightarrow \frac13\sum_{i=1}^3e^{-3u_i}.                 \tag{3}
$$
For a single vertex set $z=(u_j-u_i,u_k-u_i)$ and write $A=e^{z_1/a}, B=e^{z_2/a}$. On $J=[-9/10,9/10]$, the equal threshold $w_0(t)=\sqrt{(1+t)/2}$ ranges over a compact subset of $(0,1)$; for bounded $z$ so does $w$, for all large $a$. Let $q=1-w^2$, $q_0=1-w_0^2$. At $A=B=1$ both logarithmic radius derivatives of $\log q$ equal one. For example $\partial_{\log A}\log w=t/(1+t)-1/2$; inserting $w_0^2=(1+t)/2$ gives the assertion. Taylor's theorem on a compact smooth domain gives, uniformly for $t\in J$ and bounded $z$,
$$
 a\log(q/q_0)=z_1+z_2+O(a^{-1})
$$
also after differentiating the difference up to twice with respect to $z$. For $0<w<1$ the cap admits the exact expression
$$
 H_a(w)=\frac{c_a}{2a}(1-w^2)^a L_a(w),\qquad
 L_a(w)=\mathbb E[(w^2+(1-w^2)V)^{-1/2}].
$$
Here $V$ is as in §1. On compact subintervals of $(0,1)$, $L_a(w)=1/w+O(1/a)$ in $C^2(w)$: apply the mean-value theorem in $V$ to each of the first three functions, of orders zero, one and two in $w$, whose $V$-derivatives are bounded. Thus uniformly in $t\in J$ the ratio $H_a(w(t,A,B))/H_a(w_0(t))$ converges in $C^2(z)$ to $e^{z_1+z_2}$. This conclusion holds on every subinterval of $J$ as well.

For clarity, no differentiability at a singular endpoint of the angular integral is presumed. For bounded $z$, $D=A^2+B^2+2ABt=(A-B)^2+2AB(1+t)\ge c(1+t)$ with $c>0$ uniform for large $a$. Direct differentiation of $(1+ABt)D^{-1/2}$ bounds each first or second $z$-derivative by $C(1+t)^{-5/2}$; the constant may be enlarged near $t=1$. The clipped $H_a$ is $C^2(\mathbb R)$ for $a>2$, with $|H_a|+|H_a'|+|H_a''|=O(a^{3/2}+1)$ from its density, $c_a=O(\sqrt a)$, and the zero derivatives beyond the support. The chain rule bounds the whole cap and its first two derivatives by a polynomial in $a$ times $(1+t)^{-5}$. On $|t|>9/10$ the density factor satisfies
$$
 (1-t^2)^{a-1}(1+t)^{-5}\le 32(19/100)^{a-6}\qquad(a\ge6).
$$
This supplies local dominated differentiation for each $a$ and shows that both removed tails, with all those derivatives, are $o(p_0)$ by (2). Integrating on $J$ and using (1) now gives $p_i/p_0\to e^{z_1+z_2}$ in $C^2$. Since $z_1+z_2=-3u_i$, (3) follows.

The limiting Hessian is positive definite on the centered plane, uniformly on each fixed compact set: its quadratic form is $3\sum_i e^{-3u_i}v_i^2$. Hence on each fixed centered box and for every sufficiently large $d$, the actual normalized objective has positive Hessian on the plane. By permutation symmetry its derivative at the origin vanishes on that plane. Therefore the equal triple is the unique minimum in that box.

## 3. A uniform exclusion of all other radius ratios

Let $i$ have the smallest radius; thus $A,B\ge1$, and put $R=AB$. Use any fixed compact interval $J_1\subset(-9/10,0)$ with $-1/3$ in its interior. For $t\in J_1$,
$$
 w(t,A,B)\le \max\{0,g_t(R)\},
 \qquad g_t(R)=\frac{1+Rt}{\sqrt{2R(1+t)}}.
$$
This is true also for a nonpositive numerator; for a positive numerator use $A^2+B^2\ge2AB$. The function $g_t(R)=(R^{-1/2}+tR^{1/2})/\sqrt{2(1+t)}$ is strictly decreasing in $R>0$ on this angular band. Set $M=\log 4$ and $R_0=e^{M/a}$. Uniformly on $J_1$, $g_t(R_0)>0$ for large $a$. If $R\ge R_0$, monotonicity and the cap comparison give
$$
 H_a(w(t,A,B))\ge H_a(g_t(R_0))
  =H_a(w(t,e^{M/(2a)},e^{M/(2a)})).
$$
By the cap-ratio estimate of §2 at fixed $z=(M/2,M/2)$ the right side is $(4+o(1))H_a(w_0(t))$, uniformly on $J_1$. By the concentration in §1 its integral on $J_1$, including the density, is $(4+o(1))p_0>3p_0$. Thus for all sufficiently large $d$ this single vertex already exceeds $S_d$, uniformly for every $R\ge e^{M/a}$, without any upper bound on the radii.

Otherwise $0\le a\log A,a\log B\le a\log R<M$. The centered $u_i$ all lie in the fixed box $[-M,M]^3$, so §2 gives the strict inequality except at equal radii. This proves the deterministic theorem for all $d\ge d_0$ with some finite absolute $d_0$. We do not determine the least $d_0$.

## 4. What is optimized

For an iid law invariant under all rotations about a common center, translate the center to zero. Away from zero it has the representation $RU$, where $U$ is uniform on the sphere independent of $R$, by uniqueness of rotation-invariant probability measure on each sphere. The assumption that the iid triangle is almost surely nondegenerate excludes an atom at zero, since two coinciding samples would then have positive probability. Conditioning on the three iid radii proves the lower bound. Equality requires all three radii equal almost surely, hence a constant radius: if the law of $R$ is nonconstant, a threshold splits its mass into two positive parts and independent draws differ with positive probability. Conversely any fixed positive radius attains $S_d$. For deterministic radii with just one zero, the angle at the center alone is obtuse with probability $1/2$, already greater than $S_d$ in sufficiently high dimension. Two zeros always give a degenerate triangle.

The unrestricted optimization is different. By the acute-set construction of Gerencsér and Harangi, one can choose $N=2^{d-1}+1$ distinct points all of whose triples are acute. Around them choose disjoint positive-radius balls small enough so that every triple from different balls stays acute: there are finitely many strict dot-product inequalities at the centers. Draw uniformly from an equally weighted mixture of those balls. An obtuse triangle requires a repeated ball label, so the unrestricted infimum is at most $3/N$ by the union bound. This direct consequence of the existing point construction is exponentially below (2); it is not an exact determination of the unrestricted optimum.

## 5. Interpretation of the existing sphere integral

Equation (2) of Drivas and Retakh, arXiv:2508.18414v1, gives the conditional probability of an obtuse triangle, as a function of the angle $\theta$ between two independent uniform sphere points:
$$
 \tfrac12 I_{\sin^2(\theta/2)}(a,\tfrac12)+I_{\cos^2(\theta/2)}(a,\tfrac12).
$$
Here $I_z$ denotes the normalized incomplete beta integral. The subsequent exact angle integral has density proportional to $\sin^{d-2}\theta$. Reflection $\theta\mapsto\pi-\theta$ interchanges the two incomplete beta functions and preserves the angle law. Further, the first summand is exactly $H_a(\sqrt{(1+\cos\theta)/2})$ in (1). Thus the exact integral in that source is indeed $S_d$. Replacing $\theta$ by $\pi/2$, as in their subsequent approximation, gives $\tfrac32 I_{1/2}(a,1/2)$; its exponential base to power $a$ is $1/2$, since on $0\le u\le1/2$ the factor $(1-u)^{-1/2}$ stays between 1 and $\sqrt2$, and $B(a,1/2)^{-1}$ is subexponential. By (2) the actual base is $16/27$. The substitution cannot preserve the relative asymptotic of the sphere probability. This concerns the evaluation of this one distribution, not the validity of a numerical upper bound on the infimum over all distributions.

Greenwell, arXiv:2608.06591, treated arbitrary concentric-circle radii in the plane. Jandhyala, *Why the sphere beats the ball*, author preprint of 10 October 2026, treated all triples of concentric spheres in dimension three, with a closed formula: the minimum obtuse probability is $1/2$, attained exactly when the two largest radii agree; amongst admissible iid radial laws the optimizer is nevertheless a single sphere. Neither dimension is asserted as a new case here. Other classical problems optimize over the shapes of convex bodies with uniform volume sampling, not over all radial laws.
