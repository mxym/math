# The quadratic-power capacity of the real additive Laplace channel

The noise has density $k(z)=e^{-|z|}/2$ on $\mathbb R$ and is independent of the input. Inputs are arbitrary Borel probability laws, not just densities. Write $C(P)=\sup_{\mathbb E X^2\le P}[h(X+Z)-h(Z)]$; logs are natural and $h(Z)=1+\log2$. This is the information capacity of the scalar memoryless additive channel. The formula below also describes equality under the constraint $\mathbb E X^2=P$.

**Theorem.** For $R>0$ put $a=1/[2(R+1)]$ and define
$$
 V_R(y)=\begin{cases}ay^2,&|y|\le R,\\ aR^2+|y|-R,&|y|>R,\end{cases}
 \qquad A_R=2\left(\int_0^R e^{-au^2}du+e^{-aR^2}\right),
 \qquad q_R=A_R^{-1}e^{-V_R}.
$$
Set $P(R)=\int_{\mathbb R}y^2 q_R(y)dy-2$. This is a continuous strictly increasing bijection $(0,\infty)\to(0,\infty)$. With $P=P(R)$,
$$
 C(P)=\log(A_R/2)+a(P+2)-1 .
$$
The unique maximizing input is
$$
 \mu_R(dx)=\mathbf 1_{|x|<R}(1+2a-4a^2x^2)q_R(x)\,dx
       +(1-2aR)q_R(R)(\delta_{-R}+\delta_R)(dx);
$$
its output density is $q_R$. In particular for every $P>0$ even the supremum over all log-concave inputs is strictly less than $C(P)$. The noise is symmetric and log-concave and the optimal input symmetric but not log-concave. For general Laplace scale $b>0$ replace $P$ in the unit-scale formula by $P/b^2$ and dilate the maximizing input by $b$. For a variance-only budget, centering does not change mutual information, and the optimizers are exactly the translations of the stated law. The zero power endpoint for the second-moment problem is the point mass at zero, with capacity zero.

**1. Realizing the output.** The distributional identity $(1-D^2)k=\delta_0$ follows by the derivative jump $-1$ of $k$ at zero. The function $q_R$ is continuous and piecewise smooth. On its inner interval $(1-D^2)q_R=(1+2a-4a^2x^2)q_R$; on its outer intervals it vanishes. At $R$ the right derivative minus the left derivative is $-(1-2aR)q_R(R)$, with the same jump at $-R$. Consequently $(1-D^2)q_R$ equals the displayed $\mu_R$. It is positive since $2aR=R/(R+1)<1$ and $a>0$. Its mass is one by integration (the total distributional second derivative has mass zero since the first derivatives vanish at both infinities). Convolution with $k$ returns $q_R$: equivalently the Fourier multiplier of $k$ is $1/(1+t^2)$ and that of $1-D^2$ is $1+t^2$. This multiplier also proves injectivity on all probability measures. The input has mean zero and second moment $P(R)$, by independence and $\mathbb E Z^2=2$.

**2. A dual certificate.** Define $F_R(x)=\mathbb E V_R(x+Z)$. Since $k$ is the Green kernel for $1-D^2$, $F_R-F_R''=V_R$ distributionally; the integral has at most linear growth. In fact
$$
 F_R(x)=\begin{cases}
 a(x^2+2),& |x|\le R,\\
 aR^2+z+2ae^{-z},&z=|x|-R>0.
 \end{cases}
$$
To verify this formula, its right side satisfies the differential equation on each smooth piece. At $R$ the values match and its one-sided derivatives are $2aR=1-2a$; at $-R$ use evenness. Thus there is no delta contribution. The solution is unique among functions of at most polynomial growth: the difference solves $u''=u$ on the line, equivalently $(1+t^2)\widehat u(t)=0$ among tempered distributions, so vanishes. Therefore
$$
 F_R(x)\le a(x^2+2)
$$
with equality exactly for $|x|\le R$: outside, the difference (left minus right) is $a[2z-z^2+2(e^{-z}-1)]<0$. The bracket and its derivative vanish at zero and its second derivative is $-2+2e^{-z}<0$ for $z>0$.

For any input $\nu$ of finite second moment, its output $p=k*\nu$ has $0<p\le1/2$ and finite second moment, hence finite differential entropy (bounded below by $\log2$ and above by the Gaussian entropy bound). Also $V_R$ has at most linear growth. Fubini and the relative entropy identity give
$$
 h(p)=\log A_R+\int F_R(x)\,d\nu(x)-D(p\Vert q_R)\le\log A_R+a(2+\mathbb E_\nu X^2)-D(p\Vert q_R).
$$
For $\mu_R$ this is equality with divergence zero because its support is $[-R,R]$ and its output is $q_R$. This proves the formula at power $P(R)$. Equality at that budget requires $D(p\Vert q_R)=0$ and hence $\nu=\mu_R$ by injectivity.

**3. Which budgets occur?** For each $R$, $P(R)>0$ and $P(R)\le R^2$ by the input's support and positive interior. It is continuous by the formulas for $q_R$ and dominated convergence locally in $R$: on a compact range with upper endpoint $M$, the unnormalized tails for $|y|>M$ are at most $e^{M-|y|}$. If $R_2>R_1$, let $a_i=1/[2(R_i+1)]$. On the positive half-line, $q_{R_2}/q_{R_1}$ is strictly increasing up to $R_2$, then constant: the derivative of its logarithm is $2(a_1-a_2)y$ on $(0,R_1)$ and $1-2a_2y>0$ on $(R_1,R_2)$. Therefore the second moment under $q_{R_2}$ is strictly larger: with $U$ of density $2q_{R_1}$ on $(0,\infty)$, the difference of second moments is $\operatorname{Cov}(U^2,(q_{R_2}/q_{R_1})(U))>0$, as seen by pairing independent copies in the covariance identity. As $R\to\infty$, $A_R\ge 2\sqrt R\,e^{-1/2}$ for $R\ge1$ by integration through $\sqrt R$; hence $\|q_R\|_\infty\to0$. For each fixed $L>0$ the mass on $[-L,L]$ then tends to zero, so the second moments tend to infinity. This proves the claimed bijection.

**4. Strict loss for log-concave input.** A log-concave probability measure on the real line satisfies $\nu((I+J)/2)\ge\sqrt{\nu(I)\nu(J)}$ for intervals $I,J$; in particular this holds for every log-concave density (one-dimensional Prékopa–Leindler). But $\mu_R$ puts positive equal masses at $-R,R$ and zero mass at zero. If log-concave inputs $\nu_j$ with $\mathbb E_{\nu_j} X^2\le P$ approached capacity, §2 would give $D(k*\nu_j\Vert q_R)\to0$. By Pinsker the outputs then converge in total variation and hence their characteristic functions converge. Division by the nowhere-zero characteristic function of $k$ gives pointwise convergence of the input characteristic functions to that of $\mu_R$, hence $\nu_j\Rightarrow\mu_R$. For $0<d<R/2$ take $I,J$ to be the radius-$d$ open intervals about $-R,R$. Their boundaries and those of the radius-$d$ midpoint interval are $\mu_R$-null. Thus the midpoint mass inequality for $\nu_j$ passes to $\mu_R$. Letting $d\downarrow0$ gives $0\ge(1-2aR)q_R(R)>0$, a contradiction. This is strict inequality between the suprema, not merely exclusion of attainment.

The log-concavity question is the unnumbered final paragraph of §VII of Madiman–Nayar–Tkocz, distinct from their Question 1 asking which noise maximizes capacity at fixed noise variance. General discreteness theorems already imply a negative qualitative answer for certain smooth symmetric log-concave noises; they do not identify the present nonsmooth Laplace-channel mixed optimizer or its capacity. This result makes no best-noise determination.
