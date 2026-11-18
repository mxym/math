# When does an exponential product lose sharpness for the entropy of a difference?

**Mathematical proof.** We use natural logarithms. All densities below are with respect to Lebesgue measure. Assertions labelled “first variation” concern the specified paths at zero, not arbitrary local or global optimizers.

## What is being tested?

Take two independent copies of the same random vector, shrink each, then subtract them. Can the new vector have more entropy than the original? For normalized positive weights $\lambda+\mu=1$, Han–Zhan–Zhou–Zhu (HZZZ, [Theorem 3](https://arxiv.org/html/2610.15716v1)) prove that the answer is no for every log-concave density in every dimension for Rényi orders from 1 to infinity. An independent product of one-sided exponentials gives equality, even below order 1. But equality of a particular example need not mean an upper bound holds.

**Result A (all weights as a class).** Fix any dimension $n\ge 2$. Among positive Rényi orders, the bound
$$
h_p(aX-bX')\le h_p(X)+n\log(a+b)
$$
holds for every full-dimensional log-concave density and every pair $a,b>0$ if and only if $p\ge1$ (including infinity). The positive direction is HZZZ's theorem. The negative direction here allows the weights and density to depend on p. It does not assert failure for each fixed pair of weights. In fact, witnesses for every $0<p<1$ exist already in dimension two.

**Result B (one fixed pair of weights).** Write $\lambda=a/(a+b)$, $\mu=b/(a+b)$. For $0<p<1$ put
$$
A=\frac{\lambda}{1-\mu p},\qquad B=\frac{\mu}{1-\lambda p}.
$$
Whenever $A^n+B^n<1$, the proposed bound fails for these particular weights. It is also the precise criterion for whether a *positive right derivative* occurs along the fixed-support paths of §1, where the convex potential is nonnegative, finite, and has four finite expectations. For equal weights, this implies
$$
 C_{n,p}:=\sup_X[h_p(X-X')-h_p(X)]>n\log 2
 \qquad (0<p<2-2^{1/n}).
$$
In particular the strict inequality holds in the plane at $p=4/7$, where the uniform triangle is not a witness. We give a non-asymptotic exact witness there. This does **not** determine the unrestricted constant in [HZZZ, (61)](https://arxiv.org/html/2610.15716v1), establish sharpness of this sufficient range for the unweighted inequality, or answer their interval/optimizer questions. No conclusion about all weights in dimension one is needed.

**Route.** We vary the potential of the exponential-product equality example. Differentiating an apparently complicated convolution reduces the question to four elementary product probability laws. A corner atom in two mixing measures determines the sign test. A steep perturbation detects insufficient mass at that atom.

## 1. First variation

It is enough to treat normalized weights by the scaling identity $h_p(cZ)=h_p(Z)+n\log c$. Let $P_r$ be the law of n independent rate-r exponentials and write $P_r V$ for their expectation of V. Take a finite convex function $V\ge0$ on the closed positive orthant, and define
$$
 f_0(x)=\mathbf{1}_{x\ge0}e^{-\sum_i x_i},\qquad
 f_t(x)= f_0(x)e^{-tV(x)}/Z_t,\quad Z_t=P_1(e^{-tV}),\qquad t\ge0.
$$
Each is a full-dimensional log-concave probability density: its support is convex and its log is concave there. The values on the boundary do not affect the law. Let $X_t,Y_t$ be independent with density $f_t$. Put $J(t)=h_p(\lambda X_t-\mu Y_t)-h_p(X_t)$, where $h_p(f)=(1-p)^{-1}\log\int f^p$.

The density of $Z=\lambda X_0-\mu Y_0$ in one coordinate is $g(z)=\exp(-z_+/\lambda-z_-/\mu)$, with $z_\pm=\max(\pm z,0)$; use $g_0$ for its n-fold product. This follows by integrating the two exponential densities, or changing to signed excess and minimum as below. Then $\int g_0^p=\int f_0^p=p^{-n}$, so $J(0)=0$. All entropies needed for $t\ge0$ are finite since $f_t\le f_0/Z_t$ and the difference density is bounded by $g_0/Z_t^2$.

Tilt the joint law of $X_0,Y_0$ by $g_0(Z)^{p-1}/\int g_0^p$. Under this tilt, the law $T$ of $Z$ has density $g_0^p/\int g_0^p$; the conditional law of $(X_0,Y_0)$ given $Z$ does not change. Set $W=V(X_0)+V(Y_0)$ and $R_t(z)=E[\exp(-tW)\mid Z=z]$. The density of $\lambda X_t-\mu Y_t$ is $g_0R_t/Z_t^2$. Consequently
$$
 e^{(1-p)J(t)}=\frac{E_T R_t^p}{P_p(e^{-ptV})Z_t^p}.\tag{1}
$$
Write $Q_X,Q_Y$ for the marginals of the tilted joint law. Assume the four expectations $P_1V,P_pV,Q_XV,Q_YV$ are finite. For $T$-almost every $z$, $R_t=1-tE(W\mid z)+o(t)$ and $(1-R_t^p)/t\le(1-R_t)/t\le E(W|z)$. Using dominated convergence in (1) gives
$$
 \frac{1-p}{p}J'(0+)=P_pV+P_1V-Q_XV-Q_YV.\tag{2}
$$
This domination is important for the fast-growing potentials used below.

## 2. The two tilted marginals

In one coordinate put $U=\lambda X_0$, $L=\mu Y_0$. Their joint density factors in $(M,Z)=(\min(U,L),U-L)$ into an exponential density of rate $1/\lambda+1/\mu$ for $M$, times $g(z)$ for $Z$ (Jacobian 1 on either side). Tilting changes only Z; the tilted signs have probabilities λ and μ. Conditional on sign +, the excess Z/λ is rate-p exponential; conditional on sign −, the excess −Z/μ is rate-p exponential. Moreover $M/\lambda$ is exponential with rate $1/\mu$. Hence under the tilt $X_0$ is distributed as $M/\lambda$ plus an independent Bernoulli(λ) times a rate-p exponential. For s<p its moment generating function is
$$
 \frac{1}{1-\mu s}\left(\mu+\frac{\lambda p}{p-s}\right)
  = A\,\frac{p}{p-s}+(1-A)\frac{1}{1-\mu s}.
$$
Thus $Q_X$ is the $n$-fold product of $A\,\mathrm{Exp}(p)+(1-A)\,\mathrm{Exp}(1/\mu)$; $Q_Y$ is the $n$-fold product of $B\,\mathrm{Exp}(p)+(1-B)\,\mathrm{Exp}(1/\lambda)$. Here $\mathrm{Exp}(r)$ denotes the rate-$r$ law. Coordinate independence follows from factorization of the joint tilt. The two marginals need not be independent of one another, and the proof does not assume this.

## 3. Exact sign criterion at this density

Let E be an independent $P_1$ vector. Represent a sample of $Q_X$ as $\xi\odot E$, coordinatewise product, where each independent coordinate of ξ is 1/p with probability A, otherwise μ. For $Q_Y$ the corresponding scales are 1/p and λ with probabilities B and 1−B. Sum the two scale laws to obtain a measure of total mass two. Its atom at the all-(1/p) vector has mass $A^n+B^n$. The mean of coordinate i under the summed measure (unnormalized integral) is 1+1/p: by the excess representation, the two individual means are μ+λ/p and λ+μ/p.

If $A^n+B^n\ge1$, remove exactly unit mass at that atom. The remainder is a probability measure of mean vector (1,…,1). For fixed E, convexity of $\xi\mapsto V(\xi\odot E)$ and Jensen give a contribution of at least V(E) from the remainder. The removed mass contributes V(E/p). Taking expectation proves $Q_XV+Q_YV\ge P_1V+P_pV$. All first derivatives (2) are nonpositive, including when the atom has exactly unit mass. This is not a claim about arbitrary perturbations of the support or higher-order terms.

Conversely let $V_s(x)=\exp(s\sum_i x_i)$ for $0<s<p$. All four moments are finite. Let $u=p/(p-s)$. Then $P_pV_s=u^n$, $P_1V_s=(1-s)^{-n}$, and $Q_XV_s=[Au+(1-A)/(1-\mu s)]^n$, with the analogous expression for $Q_Y$. Dividing the right side of (2) by $u^n$ and sending $s\uparrow p$ gives $1-A^n-B^n$. If this is positive, choose s<p sufficiently close to p; then $J'(0+)>0$ and $J(t)>0$ for every sufficiently small positive t. By dominated convergence the witness densities even approach $f_0$ in total variation as $t\downarrow0$ (no uniform density-ratio assertion).

For each $n\ge2$, $p\in(0,1)$, choose $\mu=(1-p)^3/4$, $\lambda=1-\mu$. Then
$$
1-A^n\ge1-A=\frac{(1-p)\mu}{1-\mu p}\ge (1-p)\mu,\qquad
B^n\le B^2\le\frac{\mu^2}{(1-p)^2}=\frac{(1-p)\mu}{4}.
$$
So $A^n+B^n<1$. This proves A and the stated weight-specific negative direction. If $\lambda=\mu=1/2$, then $A=B=1/(2-p)$, and the condition simplifies to $p<2-2^{1/n}$. Scaling the half-difference back by 2 yields B.

## 4. A planar witness without limiting parameters

Take $n=2$, $p=4/7$, both weights $1/2$, $s=9/16$, and use the preceding $V_s$. Let $t=2^{-1512}$. All numbers are exact. Write
$$
P=P_pV=4096,\quad U=P_1V=256/49,\quad Q_XV=Q_YV=1081600/529,\quad
D=P+U-Q_XV-Q_YV=311040/25921>0.
$$
To directly certify this particular t, let $\delta=1/126$ and $K=P_p(V^{1+\delta})+P_1(V^{1+\delta})+PU$. Both moments are finite since $s(1+\delta)=127/224<128/224=p$. Conditional Jensen gives $R_t^p\ge\exp[-pt\,E(W\mid Z)]\ge1-pt\,E(W\mid Z)$. Thus the numerator of (1) is at least $1-pt(Q_XV+Q_YV)$.

For all $v\ge0$, $0\le\exp(-v)-1+v\le v^{1+\delta}$; indeed integrate $0\le1-\exp(-x)\le x^\delta$. Write $H=P_p(e^{-ptV})$ and $C=Z_t$. Since $C^p\le1-p(1-C)$ and $1-C^p\le1-C\le tU$, expanding $HC^p$ yields
$$
 HC^p
 =1-(1-H)-(1-C^p)+(1-H)(1-C^p)
 \le 1-pt(P+U)+pt^{1+\delta}K.
$$
Here $1-H\le ptP$, $p^{1+\delta}\le p$, and $t^2\le t^{1+\delta}$ for $0<t\le1$. Hence numerator minus denominator in (1) is at least $pt(D-t^\delta K)$. Direct rational arithmetic gives
$$
 K=17422205952/461041,\qquad K<4096D,\qquad t^\delta=1/4096.
$$
This proves strict positivity at the displayed t, with no numerical entropy integrations. For comparison the uniform triangle in [HZZZ (58)](https://arxiv.org/html/2610.15716v1) has unweighted p-power integral ratio $12/[(2p+1)(2p+2)]=98/55$ at this p; the required ratio for a violation is $4^{1-p}=4^{3/7}$. Since $98^7<64\cdot55^7$, the triangle gives no violation there.

### A second finite certificate (independent check)

The [independent reviewer](REVIEW.md) obtained a direct lower bound on the entropy gap that does not use the product estimate above. Conditional Jensen followed by Jensen under $T$ gives
$$
\log E_T R_t^p\ge -pt(Q_XV+Q_YV).
$$
Apply $\log u\le u-1$ to the two normalizers in (1), and use the same scalar exponential remainder with $\delta=1/126$. For $C_0=P_p(V^{1+\delta})+P_1(V^{1+\delta})=128^2+(224/97)^2$, this gives
$$
\log P_p(e^{-ptV})+p\log Z_t
 \le -pt(P+U)+pt^{1+\delta} C_0.
$$
Therefore at $t=2^{-1512}$ the *normalized* difference has entropy gap
$$
J(t)\ge t\,\frac p{1-p}\left(D-\frac{C_0}{4096}\right)
=t\,\frac{7802780287}{731672067}>0.
$$
Both certificates concern the same continuous density and both are exact. The small parameter makes the sign accessible to rational estimates, not to ordinary floating-point subtraction.

## Boundaries and provenance

The normalization, sharp theorem for p≥1, equality family, high-dimensional simplex obstruction, and fixed-dimensional unweighted question are due to HZZZ; the equality family is not new. [Melbourne–Tkocz, §VI](https://arxiv.org/pdf/2005.10930) treats the older unweighted p≥2 inequality. The repository's [one-dimensional/lattice note (PR 69)](https://github.com/mxym/math/pull/69) uses a concentration/ROC argument, not the present weighted perturbation. At $n=1$ or when $A^n+B^n\ge1$, a nonpositive first variation here is not a proof of the general inequality. We neither compute $C_{n,p}$ nor classify its extremizers. Current literature screening is finite, not evidence of priority; no external peer review.
