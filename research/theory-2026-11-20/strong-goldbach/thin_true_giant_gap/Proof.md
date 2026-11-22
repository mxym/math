# A thinner genuine Goldbach gap and its all-rank double-giant shoulder

This is a variant of the [direct composite-gap identity](../direct_goldbach_composite_gap/Proof.md), with the same two-small completion plus calibrated odd payer. It changes the gap width and recalibrates the payer at the new upper endpoint. The main error below is \(o(x\mathfrak S(N))\), not an arbitrary power of \(1/\log x\). It removes a genuine all-rank shoulder on a shrinking factor-size sector, not the full higher-rank signed remainder.

Let \(N=2x\) be even, \(L=\log x\), \(\ell=\log L\), \(z=\exp(L/\ell^2)\), and \(J=xJ_0\subseteq[x,1.5x]\) for fixed nondegenerate \(J_0\). Let \(P=N-y\), \(R_z(y)=1_{P^-(y)>z}\), and use the singular series and genuine prime count \({\cal G}_J(N)\) from the direct identity. Fix an odd \(m\ge3\), then fixed \(0<\epsilon<\min(.005,.04/m)\). Set
\[
 \Delta=100\frac{\log\ell}{\ell^2},\qquad
 \eta=\ell^{-6/5},\qquad
 R_{\pm}(y)=\sqrt y\,x^{\pm\Delta},\qquad C_y=y/x^{1-\epsilon}.
\]
Alternatively \(R_\pm\) can be taken constant at \(x^{1/2\pm\Delta}\); both theorems below still hold. In either form the cutoff inequalities are \(r>R_-\) and \(a>R_+\).

Write \({\cal P}_y\) for distinct actual prime pairs \(c=pq\ge C_y\) with \(z<p<q<C_y\), and \({\cal H}\) for the original odd payer family of genuine \(m\)-prime products, with disjoint exponent bands in \((.4\epsilon,.8\epsilon)\) and each such product \(>C_y\). Put \(\mu_2=\mu*\mu\), \(V_z=\prod_{p\le z}(1-1/p)\), \(\xi=.10\), and
\[
 H=\sum_{s\le x^\xi}\frac{R_z(s)\log s}{s},\qquad
 J_c^+(y)=\frac{H}{V_z}+\frac12\left[
       \log^2\!\left(\frac{y}{cR_+(y)}\right)-(\xi L)^2\right],
\]
\[
 \lambda_+(y)=
 \frac{4\sum_{c\in{\cal P}_y}J_c^+(y)/c}
      {2^m\sum_{c\in{\cal H}}J_c^+(y)/c},\qquad
 w_y(c)=\mu_2(c)1_{c<C_y}+4\,1_{c\in{\cal P}_y}-2^m\lambda_+(y)1_{c\in{\cal H}}.
\]
Define \({\cal R}_\Delta(y)\) by
\[
 R_z(y)\left[\sum_{\substack{r\mid y\\r>R_-(y)}}\mu(r)\log(y/r)
       +\sum_{c\mid y}w_y(c)\!
           \sum_{\substack{a\mid y/c\\a>R_+(y)}}\log(y/(ca))\right].
\]
The own-root reference \({\cal R}_{\rm rt}\) uses \(\sqrt y\) in both cutoffs and **the same** \(w_y(c)\), including \(\lambda_+(y)\).

**1.** Uniformly in the actual even target,
\[
  {\cal G}_J(N)=\sum_{\substack{y\in J\\P=N-y\ {\rm prime}}}
               \log P\,{\cal R}_\Delta(y)
                +o_{\epsilon,m,J_0}(x\mathfrak S(N)).                 \tag{1}
\]
**2.** Let \({\cal D}_x\) consist of the actual \(y\in J\) with two distinct prime factors \(p,q\ge x^{1/2-\eta}\); no restriction on the number of remaining factors. Then
\[
 \sum_{\substack{y\in{\cal D}_x\\P=N-y\ {\rm prime}}}
     \log P\,|{\cal R}_\Delta(y)-{\cal R}_{\rm rt}(y)|
 \ll_{\epsilon,m}x\mathfrak S(N)(\Delta+L^{-1})(1+\eta\ell^2)^2
                  +O_{A,\epsilon,m}(xL^{-A})
                 =o(x\mathfrak S(N)).                               \tag{2}
\]
Since \(\Delta(1+\eta\ell^2)^2\ll (\log\ell)\ell^{-2/5}\), the discarded shoulder covers a factor-size window materially larger than the actual gap width. It does not include all pairs of fixed exponents close to \(1/2\).

## 1. Trading arbitrary-log precision for a thinner gap

Use one upper and one lower dimension-one beta sieve for the free \(z\)-roughness condition, at level \(D=x^{\Delta/2}\). The allowed sieving primes are \(t\le z, t\nmid N\), with density \(g(t)=1/(t-1)\); \(2\mid N\) is omitted. Its dimension constant is absolute, by the ordinary prime Mertens bound and \(g(t)=1/t+O(t^{-2})\) for \(t>2\). The bounded coefficients and the factor \(1+O(u^{-u/2})\) in the fundamental lemma are as in Friedlander–Iwaniec, *Opera de Cribro*, Lemma 6.11 (also [Kurlberg, Lester and Rosenzweig, Theorem 2.2](https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/superscars-for-arithmetic-point-scatters-ii/3CCB969E058792C1803466AE0EF29136)). Here \(u=\log D/\log z=50\log\ell\), so \(u^{-u/2}=o(\ell^{-B})\) for every fixed \(B\). We apply upper and lower bounds to the positive measure in each actual fixed branch, then reinsert its coefficient sign. No approximate indicator is assumed valid pointwise when multiplied by a signed score.

In the short raw term \(r\le R_-(y)\), keep the roughness of \(r\) exact and apply this sieve only to \(y/r\). In the free term \(y=sca, a>R_+(y)\), keep \(b=sc\) rough and apply the sieve only to \(a\). Then the actual prime progression moduli are \(rd\) and \(bd\) with \(d\le D\) squarefree \(z\)-smooth and coprime to \(N\). The rough factors are coprime to \(d\); from their product with \(d\) they are uniquely recovered. Nonunit fixed factors at \(N\) are discarded: \(P\mid N\) accounts for only \(O(1)\) primes in \([x/2,x]\), at total \(x^{o(1)}\) cost since the scores are \(O_{\epsilon,m}(L\tau(y)^C)\) for fixed \(C\). The largest actual modulus is
\[
 \sqrt{1.5x}\,x^{-\Delta/2} \quad
 \text{(or }1.5\sqrt x\,x^{-\Delta/2}\text{ for fixed cutoffs)}.
\]
It is below the ordinary maximal-prefix Bombieri–Vinogradov level with every fixed log reserve. For the moving cutoffs the conditions are \(y\ge r^2x^{2\Delta}\) and \(y>(sc)^2x^{2\Delta}\); these are literal prefixes after reflection, as are the constant-cutoff alternatives. Each \(c\)-test is a fixed interval in \(y\). The raw logarithm is handled by partial summation. The payer is bounded and has variation \(O_{\epsilon,m}((1+\log\ell)^2)\): its denominator is \(\gg_{m,\epsilon}H/V_z+L^2\) by its fixed disjoint prime bands, the numerator is \(O(H/V_z+L^2)\) by the reciprocal prime-pair triangle, and each pair adds at most two jumps, whose total absolute weight is bounded by \(O((H/V_z+L^2)(1+\log\ell)^2)\). Continuous terms vary by \(O(L)\) before harmonic summation, since \(\log(y/R_+(y))\) has derivative \(1/(2y)\) in the reciprocal variant. For all these statements \(J_c^+(y)\asymp H/V_z+L^2\) on the admitted c-support. The combined coefficient of any modulus is bounded by \(L^C\tau(Q)^C\); only the decomposition \(b=sc\) is not unique. Ordinary BV combined by Cauchy–Schwarz with \(E(Q)\ll xL/Q\) and divisor moments thus gives \(O_A(xL^{-A})\) for all AP errors, just as in the direct identity.

The common roughness factor in both prime main terms is
\[
 V_N(z)=\prod_{t\le z,t\nmid N}(1-1/(t-1))
       =\mathfrak S(N)V_z(1+O(L/z)).
\]
All absolute Euler products here use the *actual* roughness of their fixed factors. Ordinary Mertens gives
\[
 \sum_{b\le1.5x}\frac{R_z(b)}b\ll\ell^2,\qquad
 \sum_{c\le 1.5x}\frac{R_z(c)|\mu_2(c)|}c\ll\ell^4,
 \qquad V_z\asymp\frac{\ell^2}L.
\]
For the second inequality dominate at each prime by \((1-1/p)^{-2}\), valid including \(p^2\). The two exceptional marked harmonic sums are \(O_{\epsilon,m}(1)\) by the same pair triangle and by the genuine disjoint payer bands. Pointwise \(\varphi(b)^{-1}=(1+O(L/z))/b\) for a rough b, including square factors. The absolute full raw model costs \(O(x\mathfrak S(N)\ell^4)\) and the absolute full free model costs \(O_{\epsilon,m}(x\mathfrak S(N)\ell^8)\). This pays the fundamental-lemma relative error \(O(u^{-u/2})\) to \(o(x\mathfrak S(N))\). There is no switch here to a merely logarithmically bounded **uncut** arithmetic envelope of size \(L^C\) in paying this relative error.

For the signed principal calculation, the unchanged rough harmonic moments of the direct identity are uniform for every endpoint with a fixed positive power lower bound: \(\mu R_z/r\) has moments \(0,-1/V_z\), and \(\mu_2 R_z/c\) moments \(0,0,2/V_z^2\) in degrees \(0,1\) and \(0,1,2\), up to arbitrary log error. The proof is the same rough Perron shift \(-c/\log z\); the endpoints \(R_-(y)\ge x^{.49}\) and \(C_y\ge x^\epsilon\) have the original reserve. Deleting rough fixed factors that meet \(N\) costs \(O_A(xL^{-A})\) in the principal, since only primes \(>z\) can meet it and \(\sum_{p\mid N,p>z}1/p\ll L/z\). In the free branch the true harmonic \(\sum_{s<y/(cR_+(y))}R_z(s)\log s/s\) equals \(V_z J_c^+(y)+O_A(L^{-A})\) by elementary integer sieving and partial summation on \(s>x^\xi\) (where the **old**, deep Bonferroni expansion has a fixed power reserve). This holds uniformly for all actual c, since \(y/(cR_+(y))\gg x^{.4}\) eventually. Inserting \(J_c^+\) gives the exact cancellation of the two corrective main models by the definition of \(\lambda_+\). The \(\mu_2\) hyperbola has mean \(+|J|\mathfrak S(N)\), from its second log moment, and the short raw term has the same mean from its first log moment. The constant term \(H/V_z\) and the moving \(\log(y/R_+(y))\) are unchanged common coefficients of these finite moments. Thus the short raw term subtracted from the exact identity \(\Lambda(y)=\sum_{r\mid y}\mu(r)\log(y/r)\) and the free term added in \({\cal R}_\Delta\) cancel to \(o(x\mathfrak S(N))\). Proper prime powers cost \(O(x^{1/2+o(1)})\) in the actual \(\Lambda\) correlation. This proves (1).

## 2. Literal orientation and actual two-form bound

One may restrict to squarefree rough \(y\) in (2). Indeed at most \(O(x/z)\) rough \(y\) have a prime square factor: sum \(\lfloor1.5x/p^2\rfloor\) over \(p>z\). Cauchy–Schwarz and the fixed divisor moments in the \(O_{\epsilon,m}(L\tau(y)^C)\) envelope give \(O_A(xL^{-A})\) even with \(\log P\). Do not use \(x^{o(1)}\) pointwise to pay this subpower sieve tail.

Write \(y=pqS\) with the two giant factors. They are uniquely determined as an unordered pair for sufficiently large \(x\) because three such factors would have product \(>1.5x\). They are both \(>C_y\) and \(S\le1.5x^{2\eta}<C_y\). Thus **all** small labels are factors of \(S\), all their subproducts are strictly below \(C_y\), and neither the missing-pair term nor the payer occurs. Any divisor between the cutoffs and the own root contains exactly one of \(p,q\), since a divisor of \(S\) is too small and \(pq\) too large. On a reciprocal pair \(a=p u<b=q v, uv=S\), with \(x^{-\Delta}\sqrt y<a<\sqrt y\), the raw term adds \(-\mu(u)\log b\) at \(a\), and the free term removes the coefficient at \(b\). That coefficient is exactly
\[
 \sum_{c\mid u}\mu_2(c)\log(pu/c)
        =\mu(u)(\log p-\log u);
\]
indeed \(\mu_2(c)=(-2)^{\omega(c)}\) here and the zeroth and first subset moments are \(\mu(u)\) and \(2\mu(u)\log u\), respectively. The combined change is \(-\mu(u)(\log y-2\log u)\), including \(u=1\). Outside the reciprocal gap there is no change. If an equality with one of the moving cutoffs occurs, at most \(O(\sqrt x\,x^{\Delta})\) physical y can occur: each such root-size actual divisor determines y uniquely. For the fixed cutoffs there are at most two equality divisors, each giving \(O(x^{.51})\) physical y. With the pointwise \(x^{o(1)}\) bound and the log weights these exceptional costs are power-small. A squarefree y has no own-root tie.

For constant cutoffs the two orientations may not move together, but the absolute bound by \(O(L)\) per changed actual divisor remains true since each individual raw and full free coefficient has size \(O(L)\) by the same subset moments. This also covers either choice of endpoint inclusivity. Thus in either version we pay no more than a constant times \(L\) per labelled \(u\mid S\) and per allowed p. Counting the two giant orders only doubles this bound.

Fix the actual \(S,u,p\). Membership in the changed strip requires \(p u\) to lie in \([x^{1/2-\Delta},\sqrt{1.5x}\,x^{\Delta}]\), so \(\sum 1/p\ll \Delta+L^{-1}\) uniformly in \(S,u\) by prime dyads and the lower giant endpoint \(p\ge x^{1/2-\eta}\). Put \(A=Sp\); a necessary condition for the remaining giant q is \(A\le1.5x^{1/2+\eta}\), and we keep that condition. Then for q in the possibly enlarged interval \([x/A,1.5x/A]\) the genuine two prime forms are \(q, N-Aq\). Their interval length is \(\asymp x/A\gg x^{.49}\), since eventually \(\eta<.01\). Only \((A,N)=1\) contributes after removing \(P\mid N\). At a prime \(t\nmid AN\) the forms exclude two distinct roots; at \(t\mid N\) they exclude one, including at \(2\) (since \(A\) is odd); at \(t\mid A\) they exclude one since the other form is a nonzero constant. The local product versus the ordinary Goldbach singular series changes by at most \(\prod_{t\mid A}(1+O(1/t))=1+O(L/z)\), since \(A\) is rough. An ordinary dimension-two Selberg upper sieve at a fixed small power of \(x\) gives at most \(O(x\mathfrak S(N)/(A L^2))\) genuine pairs, with absolute constant. For instance sieve to \(x^{.015}\) with divisor level \(x^{.12}\); the truncated singular product is \(O(\mathfrak S(N)/L^2)\) and the CRT floors over the square-expanded support save a fixed power relative to \(x/A\). Both primes exceed this sieving limit for every counted row. This use allows p's reciprocal width to be summed **after** the two-form bound and does not assert a short interval asymptotic for primes.

The two weighted logarithms cancel the \(L^{-2}\) loss. Finally
\[
 \sum_{S\le1.5x^{2\eta}}\frac{R_z(S)\mu^2(S)\,2^{\omega(S)}}S
       \le\prod_{z<t\le1.5x^{2\eta}}(1+2/t)
       \ll (1+\eta\ell^2)^2 .
\]
This is an all-rank harmonic bound, not a finite-rank estimate with nonuniform constants. It proves (2). In the shrinking double-giant window the full signed completion is essential for this sharpened power of \(1+\eta\ell^2\): bounding the missing-free subproducts by the absolute \(|\mu_2|\) mass instead would have cost a fourth power.

The proof does not transfer the old fee calibration without a change of endpoint, and it does not assert a small error on every near-root divisor. Fixed exponents such as \(p,q\asymp x^{.49}\), with a genuine \(x^{.02}\)-scale remaining core, are not in (2). That larger core couples its divisor parity to a true \(P=N-Spq\); its signed test is not supplied by this two-form upper bound.

The November 2026 [unitary Möbius sign-pattern result of Tian and Yang](https://arxiv.org/abs/2611.10499), Sections 3–4, uses multiple additive decompositions into arbitrary integers and separately leaves the reflected ordinary Möbius correlation conjectural. It does not estimate the shoulder on the genuine prime rows above.
