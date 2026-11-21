# Signed smooth-modulus sectors of the actual predecessor-tagged prime statistic

Let $P$ be a prescribed even integer, $I=[P/3,2P/3]$, $L=\log P$. For fixed $K$, use a family of [neutral predecessor tags](https://github.com/mxym/math/tree/51304b57/research/theory-2026-11-20/strong-goldbach). The set $\mathcal A$ consists of products of one prime from each of $K$ disjoint sets (their union is the bank), all in $[\exp(L^{.1}),\exp(2L^{.2})]$, none dividing $P(P-1)$, and each set has reciprocal mass between $1/4$ and $1/2$. Put $\mathcal V=\sum_{a\in\mathcal A}1/a$, and $W(t)=\mathcal V^{-1}\sum_{a\in\mathcal A}{\bf1}_{a|t}$. Thus $W(t)\ll_K L^K$ for $1\le t\le P$. Uniformity gives the same assertions after averaging the families.

Fix $1/2<b_0<b_1<21/40$. Choose $\epsilon>0$ with $b_1<21/40-2\epsilon$, obtain $\delta(\epsilon)>0$ from [Stadlmann's Theorem 1, arXiv:2309.00425v3](https://arxiv.org/pdf/2309.00425v3), and fix
$$0<\eta<\min(\delta(\epsilon)/2,b_0/3),\qquad z=P^\eta.$$
Let $\omega$ be Buchstab's function, extended by zero for $u<1$, equal to $1/u$ on $[1,2]$, with $(u\omega(u))'=\omega(u-1)$ for $u>2$.

**Theorem.** For each fixed $b\in C_c^\infty((b_0,b_1))$, put
$$
 \mathcal T_b(P)=\sum_{\substack{x\in I\\x\ {\rm prime}}}(\log x)W(P-1-x)
 \sum_{\substack{d|P-x\\P^+(d)\le z}}\mu(d)
         \log\!\frac{P-x}{d}\ b\!\left(\frac{\log d}{L}\right).
$$
Then, writing $\mathfrak S(P)$ for the ordinary binary singular series,
$$
 \frac{\mathcal T_b(P)}{|I|\mathfrak S(P)}
  =\eta^{-2}\int_{b_0}^{b_1}(1-v)b(v)\omega'(v/\eta)\,dv+o_{\eta,b,K}(1). \tag{1}
$$
If also $\eta<b_1-b_0$, there are two fixed nonnegative masks $0\le b_\pm\le1$ with disjoint supports in this interval for which the constants have strictly opposite signs. The proof gives an existence choice from the known function. The constants may be tiny; no numerical size is asserted.

No restriction is imposed on the factorization layout of the true source prime. These are genuine portions of $\Lambda(q)=\sum_{d|q}\mu(d)\log(q/d)$ at $q=P-x$. Replacing the prime source with $\Lambda(x)$ changes them by $P^{1/2+o(1)}$: there are $O(\sqrt P L)$ proper powers and a $P^{o(1)}$ absolute divisor/tag bound per input. Nonsmooth moduli and the rest of the exponent range can cancel the known signs. There is no conclusion of a Goldbach representation.

## 1. Simultaneous distribution with no tag-count loss

For each squarefree $d\le P^{b_1}$ with $P^+(d)\le z$ retain $(d,P)=1$. A source prime $x|P$ costs $P^{o(1)}$ in total even after absolute divisor bounds; otherwise the unit condition on $d$ is automatic. Also $(a,d)=1$ is forced by $a|P-1-x$ and $d|P-x$. For admissible $(a,d)$ and $t\in I$ put
$$
 E_{a,d}(t)=\sum_{\substack{P/3\le p\le t,\ p\ {\rm prime}\\ p\equiv P-1\bmod a,\ p\equiv P\bmod d}}\log p
                     -(t-P/3)/\phi(ad).
$$
Uniformly in $t$, for every fixed $A$,
$$
 \sum_{a\in\mathcal A}\ \sum_{\substack{d\le P^{b_1},\ P^+(d)\le z\\
            \mu^2(d)=1,\ (d,aP)=1}} |E_{a,d}(t)|\ll_{A,K,\epsilon} P L^{-A}. \tag{2}
$$
The supremum in $t$ is outside the summed errors.

Color each bank prime independently red or blue with equal probabilities. For each fixed coloring choose **one** integer CRT class at all primes $\le z$: prescribe $P-1$ at red primes, $P$ at all other primes not dividing $P$, and $1$ at primes dividing $P$. This is everywhere a unit. The bank is below $z$ for large $P$. Stadlmann's Theorem 1 allows arbitrary integer representatives with constant independent of that integer; the class for this coloring is fixed before summing the moduli.

Retain $(a,d)$ if every factor of $a$ is red and every bank factor of $d$ is blue. Given $k=ad$ and the coloring, its red factors uniquely reconstruct $a$, and the other factors reconstruct $d$; discard invalid reconstructions. The CRT class modulo $k$ is now the required one. Each pair survives with probability $2^{-\omega_{\rm bank}(k)}$, since $k$ is squarefree. The left side of (2) is therefore the expectation of selected absolute errors multiplied by $2^{\omega_{\rm bank}(k)}\le\tau(k)$. This includes cases when unused bank primes divide $d$.

Here $k\le P^{b_1+o(1)}$ divides the product of primes $<t^{\delta(\epsilon)}$ for every central $t$. At any such endpoint Stadlmann estimates the sum of absolute prime-count discrepancies by $O_D(PL^{-D})$ for any fixed $D$; the strict slack allows the change from $P$ to $t$. Partial summation on the central interval gives the same for $\log p$ weights. Its main is interval length divided by $\phi(k)$, because no central prime divides $k<P^{b_1+o(1)}$, and PNT replaces the unrestricted sum of $\log p$ by interval length with arbitrary logarithmic saving even after $\sum_{k\le P}1/\phi(k)\ll L$. Endpoint conventions cost at most $P^{b_1+o(1)}L$. Let $E_k$ be this discrepancy for the single fixed CRT branch. Trivially $|E_k|\ll L(P/k+1)+P/\phi(k)$. Hence $\sum_{k\le P^{b_1+o(1)}}\tau(k)^2|E_k|\ll PL^{O(1)}$ by divisor moments, and Cauchy with the unweighted estimate pays $\tau(k)$ with arbitrary log saving. Taking the expectation proves (2).

Partial summation in $x$ pays the physical $\log((P-x)/d)$: endpoint magnitude is $O(L)$ and total variation $O(1)$; the bounded $b$ is constant at each $d$. Thus $\mathcal T_b(P)$ equals, up to $O_A(PL^{-A})$,
$$
 \int_I\frac1{\mathcal V}\sum_{a\in\mathcal A}\frac1{\phi(a)}
 \sum_{\substack{P^+(d)\le z\\(d,aP)=1}}\frac{\mu(d)}{\phi(d)}
 \big[L(1-v_d)+\log(1-x/P)\big]b(v_d)\,dx,\qquad v_d=\log(d)/L.       \tag{3}
$$
Removing $(a,d)=1$ costs inside the inner main at most
$$
 O_b\!\left(L\sum_{\ell|a}\frac1{\ell-1}
                 \prod_{r\le P}(1+1/(r-1))\right)\ll_{K,b}L^2 e^{-L^{.1}},
$$
with $r$ over primes. Also $\mathcal V^{-1}\sum_a1/\phi(a)=1+O_K(e^{-L^{.1}})$; its error may multiply the same $O_b(L^2)$ absolute budget. Thus the normalized neutral tags do not change the limiting profile.

## 2. The two signed moments, uniformly in the target

Write $c_P(k)={\bf1}_{(k,P)=1}\mu(k)/\phi(k)$. Define the multiplicative $h=h_{P,z}$ supported on integers with all prime factors $r>z$, $r\nmid P$, by $h(r^j)=(r-1)^{-j}$ on allowed primes. The exact identity is
$$ c_P(d){\bf1}_{P^+(d)\le z}=(c_P*h)(d).$$
Repeated prime factors on the right have not been omitted.

The two ordinary conditionally convergent moments are
$$
 \sum_k c_P(k)=0,\qquad \sum_k c_P(k)\log k=-\mathfrak S(P),\qquad
 \mathfrak S(P)=2\prod_{r>2}(1-(r-1)^{-2})\prod_{r|P,\ r>2}\frac{r-1}{r-2}.
                                                                         \tag{4}
$$
Indeed the Dirichlet series of $kc_P(k)$ is $\zeta(w)^{-1}H_P(w)$, with $H_P$ local factors $(1-\frac r{r-1}r^{-w})/(1-r^{-w})$ for $r\nmid P$ and $(1-r^{-w})^{-1}$ for $r|P$. The first product is absolutely bounded at $\Re w\ge3/4$ uniformly in $P$. Its product with the other factors at $w=1$ is exactly $\mathfrak S(P)$. The simple zero and unit derivative of $1/\zeta(w)$ at 1 yield (4) after truncation is justified.

In fact, for $j=0,1$ the tails $\sum_{k>y}c_P(k)(\log k)^j$ are $O_A(L^{-A})$ for all fixed $A$ uniformly for $y\ge K_0=\exp(L^{.1})$. For $y\ge K_0/2$ use the classical zeta zero-free contour $\Re w=1-c/\sqrt{\log y}$ up to height $\exp(\sqrt{\log y})$ with sufficiently small $c$. The reciprocal zeta costs a log power of $y$. The extra Euler factors at $r|P$ cost $L^{O(1)}$: below $\exp(\sqrt{\log y})$ use $r^{-\Re w}\le e^c/r$ and $\sum_{r|P}1/r\ll\log(2L)$; above it there are $O(L)$ such primes and their contribution to the log product is $o(1)$ since $\exp(\sqrt{\log y})\ge\exp(c_0 L^{.05})$. No pole occurs at 1. The coefficients satisfy $|kc_P(k)|\ll\log\log(3k)$. Truncated Perron at half-integer endpoints, estimating terms in $[y/2,2y]$ by this bound and the remainder by absolute convergence on $1+1/\log y$, gives
$$
 \sum_{k\le y}kc_P(k)\ll
 y L^{O(1)}(\log y)^{O(1)}\exp(-c'\sqrt{\log y}).
$$
The truncation and horizontal integrals are at most the same bound. Partial summation from $y$ to infinity proves the claimed tails and (4). No absolute decay of the Möbius sequence is involved.

For a smooth $F$ compactly supported in $(b_0,b_1)$, extended by zero, Taylor expansion through the linear term in $\log k/L$ for $k\le K_0$ now gives, uniformly for $t\ge0$,
$$
 \sum_k c_P(k)F(t+\log k/L)=-\frac{\mathfrak S(P)}{L}F'(t)
     +O_F\big(L^{-2}(1+\log K_0)^3\big)+O_{A,F}(L^{-A}).              \tag{5}
$$
Indeed $\sum_{k\le K_0}|c_P(k)|(\log k)^2\ll(1+\log K_0)^3$ by the harmonic Euler product. For $k>K_0$ use the uniform signed tail and bounded total variation of the translated test, not an absolute tail. The error is $o(1/L)$; both the main and left side vanish when $t>b_1$.

## 3. The rough harmonic measure and the two signs

The $h$-mass up to $m\le P^{b_1}$ is $O_{\eta,b_1}(1)$ by the Euler product and $\sum_{z<r\le P^{b_1}}1/r=O_{\eta,b_1}(1)$. Against continuous test functions supported below $b_1$, its limiting measure on $\log(m)/L$ is
$$ \delta_0+\eta^{-1}\omega(v/\eta)\,dv.                                \tag{6}$$
For a direct verification, replacing $1/(r-1)$ by $1/r$, allowing primes $r|P$, and ignoring repeated prime factors costs $o_{\eta,b_1}(1)$ in total variation on these scales: the local costs are $O(\sum_{r>z}r^{-2})$ and $O(L/z)$ times a bounded Euler product. At most $\lfloor b_1/\eta\rfloor$ distinct factors can occur. Mertens' theorem implies weak convergence of the reciprocal-prime measure on $u=\log r/\log z$ to the density $\mathbf1_{u\ge1}/u$ on each fixed compact interval. Thus the limit before rescaling $v=\eta u$ is its convolution exponential, including $1/j!$ in the $j$-fold convolution and the atom at zero. To identify its density $g$, multiplication by $u$ distinguishes one factor and gives $ug(u)=1+\int_1^{u-1}g(s)\,ds$ for $u\ge1$, the integral zero for $u<2$. This is the defining initial data and equation for $\omega$. The bounds on excluded target primes give uniformity.

Convolve (5) with $h$, then apply (6). Its $o(1/L)$ error is small enough for the factor $L$ in (3). The $\log(1-x/P)$ term costs $O_{b,\eta}(\mathfrak S(P)/L)+o(1/L)$ inside the integral by (5) without multiplication by $L$. For the leading term use $F(v)=(1-v)b(v)$. Its normalized limit is
$$
 -\eta^{-1}\int F'(v)\omega(v/\eta)\,dv
 =\eta^{-2}\int F(v)\omega'(v/\eta)\,dv .
$$
This proves (1), since $\mathfrak S(P)$ is bounded below by a positive absolute constant. The compact support removes boundary terms, $F'(0)=0$, and $b_0/\eta>3$; $\omega$ is continuously differentiable on the relevant range, including the integer delays. No mass from the jump of its zero extension at 1 enters the derivative here.

For the two signs, $\omega$ is constant on no nonempty open subinterval of $(2,\infty)$. Otherwise choose a smaller interval avoiding integers: constancy and the delay equation give identical constancy one unit earlier, and iteration contradicts $1/u$ on $(1,2)$. On any interval of length $>1$ in $(3,\infty)$, $\omega'$ must attain both signs. If it only had one weak sign, $\omega$ would be monotone there. On the portion more than one unit right of the left endpoint, $u\omega'(u)=\omega(u-1)-\omega(u)$ would also force the opposite weak sign and hence constancy on an open interval. Apply this to $(b_0/\eta,b_1/\eta)$ and select fixed nonzero nonnegative bumps in the rescaled neighborhoods of the two strict signs. The corresponding two physical signs hold at every sufficiently large prescribed target, each at a fixed (possibly very small) positive fraction of $|I|\mathfrak S(P)$ in magnitude.

**Comparison and scope.** Stadlmann's exponent is an input, not an improvement. Without predecessor tags the same profile follows directly from that result and the Euler/Buchstab calculation; the coloring accounts for both large residues with all physical tags present. Zheng's [simultaneous-progression Theorem 1.1](https://arxiv.org/abs/2512.22798) is related, under different modulus and residue conditions. Here the union modulus is smooth and squarefree, with one fixed CRT prescription per coloring, not an unrestricted pair of moduli. No estimate for the whole remaining signed divisor identity follows.
