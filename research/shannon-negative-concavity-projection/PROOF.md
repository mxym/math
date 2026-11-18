# Shannon projection entropy does not define a norm for all convex measures

All logarithms are natural. For a real random variable with density $g$, write $h=-\int g\log g$ for Shannon differential entropy. For a planar law $Z$, the proposed projection norm is $u\mapsto\exp h(\langle u,Z\rangle)$ for $u\ne0$, with value zero at the origin.

**Theorem.** For every $H>0$ there exists a full-dimensional planar law of $(X,Y)$, invariant under both individual coordinate sign changes, which is jointly $\kappa$-concave for a finite $\kappa<0$ and satisfies
$$
e^{h(X+Y)}>H(e^{h(X)}+e^{h(Y)}).
$$
All one-dimensional nonzero projections have finite Shannon differential entropy. The example can be taken compactly supported. This violates the p=1 instance of the all-κ projection conjecture (Madiman–Melbourne–Xu, arXiv:1604.04225v2, Conjecture 3.22; Li, arXiv:1704.02634v2, Conjecture 3.1). It does not settle the original Ball–Nayar–Tkocz log-concave conjecture. The measure curvature may vary with the requested factor; no claim is made for each prescribed finite negative κ, or of unbounded factors at one prescribed finite κ.

## 1. Joint densities and their scale mixtures

Fix $D>1$, let $C=\log(1+D^{-2})$, and for $0<\varepsilon\le1$ put $T=\exp(C/\varepsilon)$, $\beta=2+\varepsilon$. Define
$$
P(x,y)=\max(1,|x|/D,|y|,D|x|-T),\qquad f_\varepsilon(x,y)=c_\varepsilon P(x,y)^{-\beta}.
$$
The positive potential P is convex and invariant under coordinate reflections. At density parameter $s=-1/\beta$, the power $f^s$ is a positive multiple of P and hence convex. Borell's characterization (equivalently Borell–Brascamp–Lieb) gives the measure parameter $\kappa=s/(1+2s)=-1/\varepsilon$. The density is everywhere positive. Normalizability follows either by comparison with $(1+|x|+|y|)^{-\beta}$ with a D-dependent constant or by the formula below. It is not log-concave: restricting to its vertical axis gives a positive multiple of $y^{-\beta}$ for $y>1$, whose logarithm is strictly convex there.

For $r\ge1$, $\{P\le r\}$ is the rectangle with half-sides $a(r)r,r$, where
$$
a(r)=\min(D,(1+T/r)/D)\in[D^{-1},D].
$$
The layer-cake identity $P^{-\beta}=\int_1^\infty\beta r^{-\beta-1}\mathbf{1}_{P\le r}\,dr$ realizes $(X,Y)$ conditionally on the scale $r$ as $r(a(r)U,V)$, where $U,V$ are independent uniforms on $[-1,1]$, independent of $r$. The scale density is proportional to $4r^{-\beta-1}a(r)r^2$. Therefore $Z=\varepsilon\log r$ has density
$$
q_\varepsilon(z)=I_\varepsilon^{-1}e^{-z}A_\varepsilon(z){\bf1}_{z\ge0},\quad A_\varepsilon(z)=\min(D,(1+e^{(C-z)/\varepsilon})/D),\quad I_\varepsilon=\int_0^\infty e^{-z}A_\varepsilon(z)\,dz.
$$
In particular $D^{-1}\le I_\varepsilon\le D$. For $z\ge0$, $z\ne C$, the aspect ratio $A_\varepsilon(z)$ tends to $A(z)$, defined to be $D$ below $C$ and $D^{-1}$ above $C$. The same limit holds for $A_\varepsilon(z-\varepsilon b)$ at every fixed $b$. Dominated convergence gives $I_\varepsilon\to I=\int_0^\infty e^{-z}A(z)\,dz$ and $q_\varepsilon\to q=I^{-1}e^{-z}A(z)\mathbf{1}_{z\ge0}$ a.e. The choice of $C$ gives $D(1-e^{-C})=D^{-1}e^{-C}$, so the two ranges each have limiting mass $1/2$.

## 2. Entropies of the logarithmic projections

Fix any nonzero $u=(u_1,u_2)$. In this section constants may depend on $u,D$ but not on $\varepsilon$. For $a\in[1/D,D]$ put $G_a=u_1aU+u_2V$. Its symmetric density $g_a$ is supported on $[-B,B]$, where $B=D|u_1|+|u_2|>0$, and bounded by $M=1/(2\max(|u_1|/D,|u_2|))$: convolution with a probability measure cannot increase the uniform density bound of the wider of the two intervals. If one coefficient is zero, use the other uniform density. The density of $\log|G_a|$ is
$$
k_a(b)=2e^b g_a(e^b),\qquad 0\le k_a(b)\le 2M e^b{\bf1}_{b\le\log B}.
$$
For $a_n\to a$, $k_{a_n}(b)\to k_a(b)$ for almost every $b$: if both coefficients are nonzero, use the overlap length of the intervals in the convolution formula; in the single-uniform case exclude the support endpoints. Thus $m_u(a)=\int b k_a(b)\,db=E\log|G_a|$ is bounded and continuous by integrability of $(1+|b|)e^b$ on $b\le\log B$.

Let $W=u_1X+u_2Y$. Its rescaled logarithmic magnitude $Z'=\varepsilon\log|W|$ satisfies $Z'=Z+\varepsilon\log|G_{A_\varepsilon(Z)}|$. Conditioning on $Z$ and changing variables $b=(w-z)/\varepsilon$ give the density
$$
F_\varepsilon(w)=\int_{\mathbb R}q_\varepsilon(w-\varepsilon b)\, k_{A_\varepsilon(w-\varepsilon b)}(b)\,db.
$$
Extend $A_\varepsilon$ to all real arguments by its displayed formula and put $q_\varepsilon=0$ off its support. For fixed $w\notin\{0,C\}$ the integrand tends to $q(w)k_{A(w)}(b)$ for almost every $b$ when $w>0$, and to zero when $w<0$. Domination by $2MD^2e^b\mathbf{1}_{b\le\log B}$ gives $F_\varepsilon(w)\to q(w)$ a.e.

Entropy convergence needs more than weak convergence. For $w\ge0$, the bounds $q_\varepsilon(z)\le D^2e^{-z}\mathbf{1}_{z\ge0}$ and $k_a(b)\le2Me^b\mathbf{1}_{b\le\log B}$ give
$$
F_\varepsilon(w)\le 2MD^2e^{-w}\int_{-\infty}^{\log B}e^{(1+\varepsilon)b}\,db\le K e^{-w}.
$$
Here $K$ is finite and independent of $0<\varepsilon\le1$. For $w<0$ the support condition additionally requires $b\le w/\varepsilon$, so
$$
F_\varepsilon(w)\le 2MD^2e^{-w}\int_{-\infty}^{w/\varepsilon}e^{(1+\varepsilon)b}\,db\le 2MD^2 e^{w/\varepsilon}\le 2MD^2e^w.
$$
Hence each $F_\varepsilon$ and $q$ are bounded by a common $K'e^{-|w|}$. On $[0,K']$ the function $|t\log t|/\sqrt t$ is bounded after extension at zero. This gives an integrable dominator proportional to $e^{-|w|/2}$ for $|F_\varepsilon\log F_\varepsilon|$. Thus $h(Z')\to h(q)$ for every fixed direction and these entropies are absolutely defined.

Moreover, conditioning on $Z$ and using bounded continuity of $m_u$ gives
$$
E\log|G_{A_\varepsilon(Z)}|=\int q_\varepsilon(z)m_u(A_\varepsilon(z))\,dz\ \longrightarrow\ \tfrac12[m_u(D)+m_u(D^{-1})]=:L(u).
$$
Each $W$ has a symmetric density, so its sign is independent of its magnitude. The inverse map on the two sign branches, $w\mapsto\pm\exp(w/\varepsilon)$, gives
$$
h(W)=h(Z')-\log\varepsilon+\log2+E\log|W|= B_\varepsilon+L(u)+o(1),\quad B_\varepsilon=h(q)-\log\varepsilon+\log2+E[Z]/\varepsilon.
$$
These terms are absolutely integrable: the exponential bound on $F_\varepsilon$ gives $E|Z'|<\infty$ for each $\varepsilon$, as well as $\int|F_\varepsilon\log F_\varepsilon|<\infty$. The common $B_\varepsilon$ uses the actual expectation under $q_\varepsilon$, not its limit; an $O(\varepsilon)$ replacement for that expectation need not disappear after division by $\varepsilon$.

## 3. Triangle violation and compact variant

For the coordinate vectors, $E\log|U|=-1$, hence
$$
L(e_1)=\tfrac12(\log D-1-\log D-1)=-1=L(e_2).
$$
For $|z|<1$ the function $F(z)=E\log|U+z|$ is even with $F(0)=-1$ and derivative $\frac12\log((1+z)/(1-z))$ on $0<z<1$, by integrating $\log|\cdot|$ on the shifted uniform interval. In particular $F(z)\ge-1$. For $u=e_1+e_2$ this implies
$$
m_u(D)=\log D+E\log|U+V/D|\ge\log D-1,\qquad m_u(D^{-1})=E\log|V+U/D|\ge-1.
$$
Thus $L(u)\ge\tfrac12\log D-1$. Only three fixed directions need to be compared:
$$
\lim_{\varepsilon\downarrow0}\frac{e^{h(X+Y)}}{e^{h(X)}+e^{h(Y)}}=\frac12e^{L(e_1+e_2)+1}\ge\frac{\sqrt D}{2}.
$$
Choose $D>\max(1,4H^2)$ and then any sufficiently small positive $\varepsilon$ to obtain a strict violation. For example, $D=16$ gives a limiting ratio at least two. The existence proof does not require a numerical cutoff for $\varepsilon$.

For the compact version, fix $D,\varepsilon$ after obtaining a strict violation, then condition on $P\le R$ as $R\to\infty$. The conditioning rectangles are convex and coordinatewise symmetric, so the restricted densities satisfy the same power condition on their convex supports. For each direction, the unnormalized restricted projection densities increase a.e. to the original density $g$ by monotone convergence on the fibers. Their normalizers tend to one. The normalized projection densities $g_R$ thus tend to $g$ a.e. and satisfy $g_R\le2g$ for large $R$. The mixture over $r\ge1$ shows that $g$ is bounded, and we have proved $\int|g\log g|<\infty$. On $g\le1/(2e)$ use $|g_R\log g_R|\le-2g\log(2g)$; on the complementary set the integrands are uniformly bounded and the set has finite measure. Dominated convergence preserves the strict inequality for all sufficiently large $R$. Boundedness and compact support give finite entropy in every nonzero projection of the truncated law. Taking $R>1$ retains an interval on the vertical axis on which the log density is strictly convex, so the truncated witness is not log-concave.
