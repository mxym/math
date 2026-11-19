# The planar Kaczmarz–Kac kinetic limit: no density concentration, and a sharp relaxation exponent

**Yongxian Zhang. Research draft.** This is separate from the finite-size absorption and determinant-time result. We take the many-particle limit at fixed time **before** the large-time limit. We also solve the different formal equation printed in §2.3 of [Steinerberger, *Kaczmarz Kac Walk*](https://arxiv.org/html/2411.06614v1). The two equations agree at antipodally symmetric profiles but not in general.

Write $\mathbb T=\mathbb R/(2\pi\mathbb Z)$, $w=\pi/2$, $I_x=(x-w,x+w)$, and extend functions periodically. For $m\ge2$ real planar unit rows, start with iid angles of probability density $u_0\in L^1(\mathbb T)$ (ordinary arc length $dx$). Each target row has a rate-one Poisson clock and at a ring independently picks a different row uniformly as pivot. Normalize the projection onto its pivot's orthogonal complement, skipping a parallel or antiparallel pair. Thus there are on average $mt$ updates by time $t$; the embedded jump-attempt chain is the original uniform-ordered-pair walk.

## 1. The many-particle limit and its gain

For every fixed $t$ and fixed $1\le\ell\le m$, the joint law of $\ell$ distinct tagged angles differs in total variation from $u_t^{\otimes\ell}$ by at most
$$\frac{\ell(\ell+1)(e^{2t}-1)}{2(m-1)}.$$
Here and below the density notation in a probability law includes $dx$. The single-particle limiting density is the unique probability solution in $C^1([0,\infty);L^1)$ of
$$\partial_tu(t,x)=-u(t,x)+[u(t,x+w)+u(t,x-w)]L(t,x),\qquad L(t,x)=\int_{I_x}u(t,y)\,dy.\tag{1}$$
Empirical averages of each bounded measurable test function consequently converge in probability to the corresponding deterministic integral at fixed time (use exchangeability and the one- and two-tag estimates).

**Branching construction.** To evaluate the tagged angles at time $t$, follow their update histories backward from $t$. Each extant target, at rate one, requires both its own pre-ring state and that of a uniformly random other pivot. Until a requested pivot is among the other already active labels, the explorations are independent rate-one branching trees: the target branch continues and one fresh pivot branch is added. This can be realized by assigning actual distinct labels on the fly to an independent forest with $\ell$ roots, stopping the coupling at its first collision. Across distinct labels the clocks and marks are independent; along a continuing label, earlier disjoint Poisson increments are fresh. The $k$ extant lines branch at total rate $k$; at a branch, the collision probability is $(k-1)/(m-1)$ whenever all $k$ labels are still distinct. If $Y_s$ is the number of lines in the unrestricted forest, the collision probability is at most $(m-1)^{-1}\int_0^t\mathbb E[Y_s(Y_s-1)]\,ds$. This usual collision-tree argument does not assume the angular update is continuous at parallel pairs. The pure birth process started from $\ell$ satisfies $\mathbb E Y_s=\ell e^s$ and $\mathbb E Y_s^2=\ell(\ell+1)e^{2s}-\ell e^s$, by its generator or the sum of independent Yule families. This gives the stated bound; it is harmless if that bound exceeds one.

Attach iid initial angles to the time-zero leaves. The forest is finite almost surely at any finite $t$; apply the two-input update from leaves to roots. On no collision this exactly supplies the finite tagged outputs, while the unrestricted root outputs are independent with a common law $\nu_t$. Define $Q(\nu,\eta)$ to be the output law when the target and pivot are sampled independently with laws $\nu,\eta$. Conditioning on the first split backward gives
$$\nu_t=e^{-t}\nu_0+\int_0^t e^{-(t-s)}Q(\nu_s,\nu_s)\,ds.$$
If both inputs have densities, their independent angles almost surely do not coincide modulo $\pi$. For a prescribed output angle $x$, either pivot $x+w$ or $x-w$ has the same one-dimensional orthogonal projection; normalizing gives direction $x$ precisely if the target $y$ obeys $\cos(y-x)>0$. More formally, conditioning on the pivot and splitting the target circle into the two open semicircles gives the gain density $(u_{\rm piv}(x+w)+u_{\rm piv}(x-w))\int_{I_x}u_{\rm target}$. Conditioning on finite tree shapes proves absolute continuity at every finite time. The bilinear probability pushforward is bounded by the product of total variation norms on signed measures, so the mild equation gives continuity and then differentiability in $L^1$; for instance the bounded forcing gives local Lipschitz continuity of the integral formula before one invokes continuity of the gain. Uniqueness follows by the probability-mass-one Lipschitz estimate on the gain and Grönwall's inequality. This proves (1).

**Fixed discrete step count.** The same limiting density holds after $\lfloor mt\rfloor$ updates of the original discrete walk. Use one common iid update list, and let $N\sim\operatorname{Poisson}(mt)$ independently. The law after $N$ updates is the Poisson-clock law. Unless a tagged row is a target of an operation between the two cutoffs, its final angle is unchanged. The total variation distance between the two tagged laws is at most $\ell\,\mathbb E|N-\lfloor mt\rfloor|/m\le \ell(\sqrt{mt}+1)/m$. This last comparison tends to zero at fixed $t$; the displayed $O(1/m)$ bound above was for the Poisson clocks.

## 2. Explicit invariant and sharp relaxation

Define the probability density
$$\rho(x)=\tfrac14\sum_{j=0}^3u_0(x+jw).$$
Then $0\le u_t(x)\le4\rho(x)$ almost everywhere for every $t$. In particular, not even at infinite kinetic time can concentration into four point masses occur from a density. More precisely
$$\|u_t-\rho\|_{L^1(dx)}
\le e^{-2t}+2e^{1/\pi}\exp[-(1-2/\pi)t].\tag{2}$$
The exponent $1-2/\pi$ cannot be improved, even allowing the constant in front to depend on the smooth positive initial density.

Put $h(x)=u(x)+u(x+\pi)$, $a(x)=u(x)-u(x+\pi)$ (time arguments are suppressed). The two half-circles have complementary masses. Adding (1) at antipodes gives $\partial_t h(x)=-h(x)+h(x+w)$, whence
$$h+h(\cdot+w)=4\rho,\qquad h_t=2\rho+e^{-2t}(h_0-2\rho).$$
This is the domination asserted above. With respect to the probability measure $\rho(x)dx$, put $f=a/(2\rho)$ on $\{\rho>0\}$, defining it as zero elsewhere. It is antipodally odd, with $|f|\le2$ at all times. Define the integral operator
$$(Kf)(x)=\int_{\mathbb T}\operatorname{sign}(\cos(x-y)) f(y)\rho(y)\,dy.$$
The difference between the two gains gives
$$\partial_t f=-f+g_t Kf,\qquad g_t(x)=\frac{h_t(x+w)}{2\rho(x)},\qquad |g_t-1|\le e^{-2t}.$$
Indeed $Kf=\frac12\int\operatorname{sign}(\cos(x-y))a(y)dy=2L(x)-1$. All multipliers are bounded almost everywhere in the weighted space. Its bounded-operator integral equation is valid in $L^2(\rho dx)$: the right side is uniformly bounded pointwise there, so this follows from the original $L^1$ integral equation by the time integral and dominated convergence (or linear Picard iteration in the weighted space).

**The angular change of variable.** Lift $H(x)=2\pi\int_0^x\rho(y)dy$ to the real line by periodicity. It pushes $\rho(x)dx$ onto uniform angular probability, satisfies $H(x+w)=H(x)+w$, and is one-to-one modulo a null set in the source measure: the interiors of flat intervals have measure zero and their endpoints form an at most countable exceptional set. In particular its generalized inverse yields a unitary identification of the two $L^2$ spaces. The sign kernel is positive just when $y\in I_x$ modulo $2\pi$; monotonicity and the quarter-turn identity preserve this condition under $H$ up to null fibers over the endpoints. Thus $K$ is unitarily equivalent to uniform angular convolution by $\operatorname{sign}(\cos\theta)$. On Fourier modes its eigenvalue is $2\sin(kw)/(\pi k)$ for nonzero integer $k$ and zero for $k=0$, by integration over the semicircles. Therefore its operator norm is $2/\pi$.

The differential inequality for $\|f\|_2$ is consequently bounded by the scalar growth rate $-1+(1+e^{-2t})2/\pi$ (equivalently use the squared norm). Integration yields $\|f_t\|_2\le e^{1/\pi}e^{-(1-2/\pi)t}\|f_0\|_2$. Since $u_t-\rho=(h_t-2\rho)/2+\rho f_t$, Cauchy–Schwarz and $|h_0-2\rho|\le2\rho$ give (2). For sharpness take $u_0=(1+\eta\cos x)/(2\pi)$ with $0<|\eta|<1$. Then $h$ is constant, $g=1$, $\rho=1/(2\pi)$, $f_0=\eta\cos x$, and this mode decays exactly by $e^{-(1-2/\pi)t}$.

## 3. Comparison: the formal equation printed in §2.3

The equation printed in the cited arXiv §2.3, also in [Steinerberger's March 2026 problem list §56](https://faculty.washington.edu/steinerb/openproblems.pdf#page=54), has instead the gain
$$u(x+w)L(x)+u(x-w)(1-L(x))\tag{3}$$
for probability densities. The second pivot does not in fact reverse the target semicircle in the projection: replacing a pivot by its negative leaves the projection matrix unchanged. Thus (3) and the gain in (1) are distinct. For instance they produce different decay rates of the antipodally odd part for the smooth first-harmonic example above.

For completeness, even (3), **as an equation in its own right**, does not create a singularity from a smooth probability density. Here we use the author's integral over the complementary half-circle where (3) writes $1-L$. The gain is nonnegative. For mass $s$ its integral is $s^2$: expanding it as $s h(x+w)/2 + a(x+w)(L(x)-s/2)$, the second term integrates to zero because $L'(x)=u(x+w)-u(x-w)=a(x+w)$. Thus along the loss-plus-gain equation $s'=-s+s^2$ and initial unit mass stays one. This bilinear gain is locally Lipschitz on $L^1$ (translations preserve $L^1$ and each partial mass is bounded by the norm). Local variation of constants/positive Picard iteration and conservation give global positive probability solutions. The explicit formulas below preserve smoothness.

In contrast to (1), the gain (3) is the same at $x$ and $x+\pi$. Hence $a_t=e^{-t}a_0$. Since $2L-1=\int_{I_x}a$, we have $L_t-1/2=e^{-t}(L_0-1/2)$, where $L_t$ denotes the value at time $t$ rather than a derivative. Define $F(x)=a_0(x+w)(L_0(x)-1/2)$, a $\pi$-periodic function, and set $v^w(x)=v(x+w)$. Then
$$\partial_t h=-h+h^w+2e^{-2t}F,$$
$$h_t+h_t^w=h_0+h_0^w+(1-e^{-2t})(F+F^w),\qquad
h_t-h_t^w=e^{-2t}\{h_0-h_0^w+2t(F-F^w)\}.$$
Together with $u=(h+a)/2$, these formulas give global convergence (in particular in every fixed $C^k$ norm for smooth initial data) to the quarter-turn invariant density $(h_0+h_0^w+F+F^w)/4$. This limit and the true walk's $\rho$ need not coincide: for $u_0=1/(2\pi)+A\cos x+B\cos3x$ with $0<|A|+|B|<1/(2\pi)$ and $AB\ne0$, $L_0-1/2=2A\cos x-(2B/3)\cos3x$, so $F+F^w=(16AB/3)\sin4x$.

These statements concern only the planar, iid-density, mean-field problem. At fixed finite $m$ the cross-voter process reaches a random single cross; taking arbitrarily large times after the fixed-time particle limit is not the same as taking absorption first. The finite-time tagged approximation above is not uniform over all times. No general higher-dimensional kinetic conclusion is asserted.
