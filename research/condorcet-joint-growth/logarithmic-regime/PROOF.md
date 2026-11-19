# Strict Condorcet winners when voters are proportional to the logarithm of candidates
A higher score means strictly preferred. Each voter's full strict order is an independent uniform permutation (impartial culture).
Let $Q(m,n)$ denote the probability of a strict global winner in every one of its pairwise contests, and put $d=n-1$. A tie is a non-win.

**Theorem.** Suppose $m,n\to\infty$, $m/\log n\to c\in(0,\infty)$. Let $a>0$ solve $\mu(a):=a\coth a-1=1/c$ and $\eta=m\bmod 2$. Then
$$
 Q(m,n)=\big(C_\eta(a)+o(1)\big)\frac{\sqrt m}{n},\qquad
 C_\eta(a)=\frac{\sqrt{6\pi}}{9}\,
 \frac{(1-e^{-2a})^2 e^{2a\eta}}{\coth a-a\,\mathrm{csch}^2a}.
$$
Equivalently this is a ratio asymptotic, separately or jointly across parity subsequences. At the same candidate count $n$, take adjacent electorate sizes $m_o,m_e$ with $m_o$ odd, $m_e$ even and both divided by $\log n$ tending to $c$. Then $Q(m_o,n)/Q(m_e,n)\to e^{2a}$. No assertion that this equivalent is uniform as $c\to0,\infty$. The unrestricted logarithmic exponent is already in the repository's earlier note; it gives no constant. Strict/weak distinction is essential.

## 1. Coordinate change that places a lattice mean on the same slice for all environments

Generate each ranking by fresh independent uniform scores. As in Sauermann and Pittel, conditional on the target candidate's independent uniform scores $u_i$, its votes against a fresh rival are independent Bernoullis of parameters $u_i$. Let $b(u)=\mathbb P_u(S\le m/2)$ be its one-comparison loss-or-tie probability. The probability it beats all $d$ rivals is $\theta=\int(1-b(u))^ddu$; $Q=n\theta$ by exclusivity.

On $\sum u_i\le m/2$, Markov applied to $S$ gives $b\ge1-(m/2)/(\lfloor m/2\rfloor+1)\ge1/(m+2)$. The associated contribution to $\theta$ is $\le\exp[-d/(m+2)]$ and negligible on the claimed scale.

On the upper half of the cube, each $u$ in its interior has a unique $s>0$ such that
$$q_i=\frac{u_i e^{-s}}{(1-u_i)e^s+u_i e^{-s}},\qquad \sum_iq_i=m/2.$$
The sum decreases strictly continuously from $\sum u_i$ to zero. Conversely take $q_1,\ldots,q_{m-1}$ in the open slice domain $D_m=\{q_i\in(0,1),\ 0<q_m=m/2-\sum_{i<m}q_i<1\}$ and $s>0$. Then
$$
 k_s(q)=(1-q)e^{-s}+q e^s,\quad u_i=q_i e^s/k_s(q_i),\quad
 X_s(q)=\sum_i\log k_s(q_i),\quad V(q)=\sum_i q_i(1-q_i).
$$
These inverse maps are smooth. The absolute Jacobian for $(q_1,\ldots,q_{m-1},s)\mapsto u$ is $2V e^{-2X_s}$. Indeed the one-variable derivative $u_q=k_s^{-2}$ and $u_s/u_q=2q(1-q)$. Taking out $u_{q_i}$ from every row of the Jacobian leaves its first $m-1$ columns $e_j-e_m$ and its last vector $(2q_i(1-q_i))_{i\le m}$. Its determinant is the sum of that vector's entries. There is **no** Euclidean-surface factor in the chosen first-$m-1$ coordinate volume.

For product Bernoulli probabilities, original outcome mass divided by tilted (parameters $q$) outcome mass is $e^{-X_s+s(2S-m)}$. Therefore $b=e^{-X_s}B(s,q)$ with
$$
 B(s,q)=\sum_{j\ge0} e^{-s(\eta+2j)}\,
             \mathbb P_q\{S=\lfloor m/2\rfloor-j\},
$$
where probabilities of negative sums are zero. Write $f_m$ for the density at $m/2$ of the sum of $m$ iid uniforms; $f_m=\mathrm{vol}_{m-1}(D_m)$ by convolution. Use $\mathbb E_*$ for uniform measure on $D_m$ normalized by $f_m$, with $q_m$ defined above. Then exactly, up to the negligible lower-half term,
$$
 \theta=f_m\mathbb E_* I(q)+O(e^{-d/(m+2)}),\quad
 I(q)=2V\int_0^\infty e^{-2X_s}(1-e^{-X_s}B(s,q))^d ds.       \tag{1}
$$
At fixed $q$, $X'_0=\sum_i(2q_i-1)=0$, and $X''_s=4\sum_i u_i(1-u_i)>0$. Thus $X_s$ increases strictly on $s>0$ to infinity. If $D=-m^{-1}\sum_i\log q_i$, then $X_s\ge m(s-D)$. Convexity gives $X'_s\ge X_s/s$.

## 2. Elementary slice tools

(i) The density at center satisfies $f_m\sim\sqrt{6/(\pi m)}$, and the supremum of the sum-of-$r$-uniforms density is $O(1/\sqrt r)$. For completeness, a centered uniform has characteristic function $\mathrm{sinc}(t/2)$. Fourier inversion at center, rescaling $t=z/\sqrt m$, gives the first limit from $[\mathrm{sinc}(z/(2\sqrt m))]^m\to e^{-z^2/24}$. Justify dominated integration on a fixed small neighborhood through $|\mathrm{sinc}(t/2)|\le e^{-ct^2}$, on bounded sets away from zero via a strict constant less than one, and for $|t|\ge4$ by $(2/|t|)^m$. The absolute integral bounds the density at any point for the second assertion.

(ii) For a set of at most $\lceil m/2\rceil$ coordinates, its marginal density under $\mathbb P_*$ relative to iid uniforms is bounded by an absolute constant: it is the complementary-sum density evaluated at the complementary sum required, divided by $f_m$. Exchangeability follows from the slice formula (equivalently disintegrate independent uniforms conditioned on their sum over intervals shrinking to $m/2$). Splitting the coordinates into two nearly equal groups and applying Hoeffding in each, with that density bound, gives for each fixed bounded continuous function $g$ and fixed $\epsilon>0$
$$
 \mathbb P_*\left(\left|m^{-1}\sum g(q_i)-\int_0^1g(u)du\right|>\epsilon\right)
 \le C_g e^{-c_{g,\epsilon}m}.
$$
Also for $t=o(m)$ positive,
$$
 \mathbb E_* e^{tD}\le C(1-2t/m)^{-m/2}=\exp[O(t+1)].
$$
Indeed apply Cauchy–Schwarz to the products on the two halves, the marginal bounds, and $\int_0^1u^{-2t/m}du=(1-2t/m)^{-1}$. The powers after the two square roots sum to $m/2$.

(iii) For any deterministic $q$ on the slice with $V\ge\delta m$, the lattice local CLT holds uniformly for its Poisson-binomial $S$:
$$
 \sup_j\left|\sqrt V\,\mathbb P_q(S=j)
   -(2\pi)^{-1/2}e^{-(j-m/2)^2/(2V)}\right|=o_\delta(1).
$$
By Fourier inversion for the centered sum, the product characteristic function has absolute value $\le\exp(-2V\sin^2(t/2))$ on $[-\pi,\pi]$, since $|1-q+qe^{it}|^2=1-4q(1-q)\sin^2(t/2)$. For $t=z/\sqrt V$ the log of the centered product equals $-z^2/2+O_\delta(|z|^3/\sqrt m)$ on bounded $z$ by the uniform single-factor Taylor expansion. Outside bounded $z$ the integrable uniform majorant $e^{-c z^2}$ follows from $\sin(|t|/2)\ge |t|/\pi$. The claimed uniformity in $j$ follows by bounding the Fourier difference in absolute integral, independent of the inversion phase.

In particular $\mathbb P_q(S=\lfloor m/2\rfloor)\ge k/\sqrt m$ on $V\ge\delta m$ for all large $m$. Also on a fixed compact subinterval of $0<s<\infty$,
$$
 \sqrt m B(s,q)=\sqrt{\frac{m}{2\pi V}}\,\frac{e^{-s\eta}}{1-e^{-2s}}+o_\delta(1)          \tag{2}
$$
uniformly: truncate the $j$ sum at a fixed large constant using $\sup_j\sqrt m\,P_q(S=j)=O_\delta(1)$ and geometric decay, then apply the central approximation at the finitely many sites. This is the origin of the parity dependence.

## 3. Exponentially unlikely slice environments do not affect the leading constant

Let $s_-=a/2$, $s_+=2a$ and $x_0=\log d-\frac12\log m$, so $x_0/m\to1/c$. The elementary integral $\int_0^1\log k_s(q)\,dq=\mu(s)=s\coth s-1$ is strictly increasing for $s>0$ because $\sinh s\cosh s>s$. Its derivative is the mean of $\partial_s\log k_s(q)$. By (ii), there are fixed $\delta,\epsilon,\gamma>0$ such that the following good event has complement of probability $O(e^{-\gamma m})$:
$$
 V\ge\delta m,\quad X_{s_-}\le x_0-\epsilon m,\quad
 X_{s_+}\ge x_0+\epsilon m,\quad X'_{s_-}\ge\delta m .
$$
Take $\epsilon$ smaller than half the gaps between $\mu(a)$ and $\mu(s_\pm)$, and $\delta$ less than both $1/6$ and $\mu'(s_-)$.

A uniform integrable envelope, not just this probability estimate, is necessary since the target is itself exponentially small. Under the inner Bernoulli law the sum has mean $m/2$. As above $P(S\le\lfloor m/2\rfloor)\ge1/(m+2)$, while Hoeffding gives $P(S<m/2-2\sqrt{m\log(m+2)})\le(m+2)^{-8}$. Thus with $h=4\sqrt{m\log(m+2)}$ and $\kappa=h/m$,
$$
 B(s,q)\ge e^{-hs}/[2(m+2)]\quad\hbox{for every }q,s.
$$
Set $x=X_s$. Since $s\le x/m+D$, the survival factor in (1) is bounded by $\exp[-Ue^{-(1+\kappa)x}]$, $U=d e^{-hD}/[2(m+2)]$. For $x\le1$, the integration length in $s$ is $\le D+1/m$, and $\exp[-Ue^{-(1+\kappa)}]\le K U^{-2/(1+\kappa)}$ with absolute $K$ when $m$ is large. For $x\ge1$, $ds/dx=1/X'_s\le s/x\le 1/m+D$. Extending the integral of $e^{-2x}\exp(-Ue^{-(1+\kappa)x})$ to the whole line gives $\Gamma(2/(1+\kappa))U^{-2/(1+\kappa)}/(1+\kappa)$. Combining and using $2V\le m$,
$$
 I(q)\le K\,m(1+D)[2(m+2)]^{2/(1+\kappa)}
 d^{-2/(1+\kappa)} e^{2hD/(1+\kappa)}.                   \tag{3}
$$
Since $\log d=O(m)$, $d^{-2/(1+\kappa)}\le d^{-2}\exp[O(h)]$. By Cauchy–Schwarz, (ii) with $t=O(h+1)=o(m)$ and the good-event probability,
$\mathbb E_*[I\,1_{\rm bad}]\le d^{-2}\exp[-\gamma m/2+o(m)]=o(m/d^2)$. This bound permits even extremely small coordinates $q_i$ near the slice boundary.

## 4. Laplace integral at good environments

On the good event the contribution to $I$ from $x\le x_0-\epsilon m$ is $o(m/d^2)$ uniformly: its $s$ interval is contained in $[0,s_+]$, while (iii) and the single $j=0$ term imply $B\ge k e^{-s_+}/\sqrt m$ there. Consequently the survival factor is $\le\exp[-k e^{-s_+}e^{\epsilon m}]$, the integration length is $O(1)$, and $e^{-2x}\le1$ because $x\ge0$.

For the rest put $y=x-x_0$ and write $s=s_q(x)$. After division by $m/d^2$, the remaining integrand is
$$
  \frac{2V}{X'_s}\,e^{-2y}
       \left(1-\frac{\sqrt m}{d} e^{-y}B(s,q)\right)^d.
$$
On $x\ge x_0-\epsilon m$ one has $s\ge s_-$, hence $2V/X'_s=O(1)$. When $-\epsilon m\le y\le0$, also $s\le s_+$, so the whole integrand is $\le K e^{-2y}\exp[-k'e^{-y}]$. When $y>0$, use $Ke^{-2y}$. Both tails are uniformly integrable.

For each fixed real $y$, the root $s_q(x_0+y)$ converges to $a$ in slice probability: bracket it with $a\pm e$ for arbitrarily small fixed $e>0$ using (ii) and strict increase of $\mu$. At this root $V/m\to1/6$, $X'_s/m\to\mu'(a)$ in probability; for the derivative use (ii) at $a$ and $0\le X''_s/m\le1$. Formula (2) then says $\sqrt m\,B\to B_0:=\sqrt{3/\pi}e^{-a\eta}/(1-e^{-2a})$ along each parity. The survival factor tends to $\exp[-B_0 e^{-y}]$. The good-event indicator tends to one. The deterministic dominating functions above justify convergence first of slice expectations (bounded convergence in probability at each $y$) and then of their integrals in $y$. We obtain
$$
  \mathbb E_* I(q)\sim \frac{m}{d^2}\frac{1}{3\mu'(a)}
   \int_{\mathbb R} e^{-2y} e^{-B_0 e^{-y}}dy
 =\frac{m}{d^2}\frac{1}{3\mu'(a)B_0^2},
$$
the last integral by direct substitution, $\Gamma(2)=1$. Now (1), the slice density asymptotic (i), and $d=n-1$ give the claimed constant.

**Scope check.** The small-$a$ expansion $\mu(a)\sim a^2/3$, $\mu'(a)\sim2a/3$ gives $C_\eta(a)\sim\sqrt{8\pi/3}\,a$ for either parity. Formally this matches the classical $\sqrt{8\pi\log n}/n$ in the iterated Gaussian regime but the theorem fixes $c$ and does not assert uniform matching.
