# A bilateral small-factor saving on the actual smooth Goldbach ledger

This note gives a fixed-target, two-leg small-factor estimate for one **complete** smooth Goldbach ledger. The two scores are actual Möbius divisor sums on \(q\) and \(m=N-sq\), not factors of an independent sieve model. The saving removes arbitrarily small prime factors at the \(M_N\) scale; it does not bound the signed expression on the remaining polynomially rough profiles.

## 1. Which actual ledger is represented

As in [SmoothAllLeastFactorDebit](SmoothAllLeastFactorDebit.md), let \(N=2x\) be even, \(L=\log x\), \(M_N=\mathfrak S(N)x/(2L)\), \(s\) be prime with \(x^{.10}<s<x^{.14}\), and restrict to \(n=sq\in(x/2,x]\), \(m=N-n\), \((n,N)=1\). Write \(W_s(q)=(1-t)(1-2t)^2\), \(t=\log s/\log(sq)\); it is nonnegative. Let \(f\) be the fixed kernel there (support \([-.310,.310]\), exactly \(1-t\) near zero), and take **any fixed** \(h\in C_c^\infty(\mathbb R)\) with \(h(0)=1\) and \(h(t)=0\) for \(t>.400\). For positive integers \(a>1\) write
\[
 H_g(a)=\sum_{d\mid a}\mu(d)g(\log d/\log a),
 \qquad C_f(m)=\Lambda(m)-(\log m)H_f(m),
 \qquad B_h(q)=\Lambda(q)/\log q-H_h(q).
\]
Set \(E_N=\sum_{s,q\ {\rm prime}} W_s(q) C(N-sq)\), with exactly the original \(C\) and the above physical restrictions, not a centered model after taking positive parts. Then for every fixed \(A\),
\[
 E_N=\sum_{\substack{s,q\\q,m\ {\rm composite}}}
        W_s(q)(\log m)H_h(q)H_f(m)+O_{A,f,h}(xL^{-A}).                 \tag{1}
\]

Indeed, the smooth replacement proof identifies \(\sum W_s(q)\Lambda(q)C_f(m)/\log q\) with \(E_N\), to arbitrary log reserve. The additional whole null
\[
 \sum_{s,q}W_s(q) H_h(q) C_f(N-sq)=O_{A,f,h}(xL^{-A})                \tag{2}
\]
is on a **free** \(q\) leg. Open \(d\mid q\); the modulus \(v=sd\) in \(m\equiv N\bmod v\) has size \(v\le x^{.4+.6(.14)}=x^{.484}\). The unit condition forces \((v,N)=1\), and every \(v\) has at most four possible prime labels \(s\). The weight \(W_s((N-m)/s)h(\log d/\log((N-m)/s))\) has uniformly bounded total variation on the physical interval (the positions of the endpoints are literal), so ordinary maximal Bombieri–Vinogradov applies to \(\Lambda(m)\) with arbitrary log reserve. On the smooth divisor side open \(j\mid m\), \(j\le(1.5x)^{.310}\). Coprime CRT gives density \(\phi(N)/(Nvj)\) for \((j,vN)=1\), zero otherwise, and an error \(O(\tau(N))\) per pair of modulus and divisor; their total is \(x^{.794+o(1)}\) up to log powers. For \(y\asymp x\) the finite coprime harmonic identity from the smooth replacement is
\[
 \sum_{(j,vN)=1}\frac{\mu(j)}{j}(\log y) f(\log j/\log y)
 =\frac{vN}{\phi(vN)}+O_{A,f}(L^{-A}).
\]
It comes from the exact affine neighborhood and uniform coprime Mertens tails; the log errors sum with reserve since \(\sum_v v^{-1}\ll L\). Multiplying by \(\phi(N)/(Nv)\) gives exactly \(1/\phi(v)\), the same principal as \(\Lambda(m)\). This proves (2) with an unaltered prime atom.

Thus \(E_N\) is the sum of \(W_s B_h C_f\), up to arbitrary log reserve. Each factor is **exactly zero on its own prime leg**. Proper prime powers \(q\) cause error \(x^{.57+o(1)}\): at fixed \(s\) there are \(O((x/s)^{1/2}L)\) and the scores are divisor-bounded times log powers. Proper prime powers \(m\) cause error \(x^{.5+o(1)}\): there are \(O(\sqrt x L)\), with at most \(\tau(N-m)\) allowed \(s\) per \(m\). On every remaining composite-composite row \(B_h=-H_h\), \(C_f=-(\log m)H_f\), proving (1). These power errors are harmless throughout.

## 2. Two-leg saving at each even target

For \(0<\kappa\le.04\) put \(I_q=1_{\{P^-(q)\le x^\kappa\}}\) and similarly \(I_m\). The following estimates even allow all integer rows on the right side of (1), dropping the composite restrictions. In the notation
\[
 \mathcal{A}(F)=\sum_{s,q} W_s(q)(\log m)|H_h(q)H_f(m)|\,F(s,q,m),
\]
uniformly in \(\kappa\) and the even target we have
\[
\begin{aligned}
 \mathcal A(1)&\ll_{f,h}M_N,\\
 \mathcal A(I_q)&\ll_{f,h}\kappa M_N+O_{f,h}(x^{.98}),\\
 \mathcal A(I_m)&\ll_{f,h}\kappa\log(2/\kappa) M_N+O_{f,h}(x^{.98}),\\
 \mathcal A(I_q I_m)&\ll_{f,h}\kappa^2\log(2/\kappa) M_N+O_{f,h}(x^{.98}).
                                                                    \tag{3}
\end{aligned}
\]
The exponent \(.98\) is inessential. Both distinct primes and higher valuations are handled before restricting ranks.

Use the transform convention \(\widehat g(\xi)=\int g(t)e^{-i\xi t}dt\). By Fourier inversion the sum \(H_g(a)\) is the integral of \(\widehat g(\xi)\prod_{p\mid a}(1-e^{i\xi\log p/\log a})\) divided by \(2\pi\). Its factorization uses **distinct** prime divisors regardless of how squareful \(a\) is. Since \(\log q,\log m\ge L/2\), a common pointwise upper for each absolute factor is the nonnegative multiplicative weight
\[
 a_\xi(p^\nu)=\min(2,2|\xi|\log p/L)\qquad(\nu\ge1).
\]
When considering any transformed pair of forms below, set \(a_\xi(p^\nu)=0\) at \(p\mid N\) to express the physical unit mask; every extracted prime is coprime to \(N\). There is an absolute bound \(a_\xi(n)\le 2^{\omega(n)}\), and the class constants for Henriot's theorem are uniform in \(x,N,\xi\). In particular the weights are multiplicative on coprime arguments, satisfy the required submultiplicative majorant \(2^{\Omega(n)}\) and, for every fixed growth exponent, have a uniform \(O_\epsilon(n^\epsilon)\) bound. The product of the two weights is multiplicative in the corresponding two-variable sense.

Here is the arithmetic upper used on each extracted column. With \(X=x/s\), the original two forms in free \(q\) are \(q,N-sq\). If \(r^\nu\parallel q\), open \(q=r^\nu u\); the forms become \(u,N-sr^\nu u\). If \(t^\mu\parallel m\), write \(q=q_0+t^\mu u\), \(q_0\equiv N\overline s\bmod t^\mu\), and use \(q_0+t^\mu u,(N-sq_0)/t^\mu-su\). In the simultaneous case \(r^\nu\parallel q,\ t^\mu\parallel m\), \(r\ne t\) since \((q,m)\mid N\) and both are units at \(N\). Write
\[
 q=r^\nu(u_0+t^\mu j),\quad
 u_0\equiv N\overline{s r^\nu}\pmod {t^\mu};
 \qquad
 \frac{m}{t^\mu}=\frac{N-sr^\nu u_0}{t^\mu}-sr^\nu j .
\]
These last two forms are primitive: \(u_0\) is a unit modulo \(t\), and the second constant is a unit modulo every prime factor of its slope \(sr^\nu\) because \(N\) is. The same argument works in the single extractions. All the matrices have determinant \(N\) up to sign, so their quadratic product discriminant is \(N^2\). The small primes \(r,t\le x^\kappa\) differ from \(s\), since \(s>x^{.10}\); every mask \((q,N)=(m,N)=1\) is exactly the pair of unit masks on the two divided forms (removed factors are units at \(N\)). Exact valuations let us first factor out \(a_\xi(r)\) or \(a_\eta(t)\), then **upper-bound** by dropping the residual unit-at-\(r\) or unit-at-\(t\) condition. This order prevents erroneously multiplying the same Fourier factor twice on a repeated prime.

Assume any extracted power is at most \(x^{.08}\). The free variable ranges over a physical interval of length \(Y\asymp X\), \(X/r^\nu\), \(X/t^\mu\), or \(X/(r^\nu t^\mu)\) respectively. Its starting point is comparable to its length, at least a constant times \(x^{.70}\); shifting the first representative by a bounded number of periods or enlarging the interval by a bounded factor is harmless for this nonnegative upper. Heights of the two forms and their product are at most \(x^3\) for large \(x\). Thus [Henriot, Theorem 5 and Corollary 2](https://arxiv.org/pdf/1102.1643), with the [published correction](https://doi.org/10.1017/S0305004114000280), apply with fixed small height exponent and a fixed short-interval exponent \(<1\). Since the two components are distinct irreducible primitive linear polynomials and the weight is multiplicative, the modified weight in the theorem is the original multiplicative weight. In the corrected discriminant factor every nontrivial local term at \(p\mid N\) is **zero** due to the imposed units. In particular there is no extra uncontrolled \(N/\phi(N)\) factor. For \(p>2\), the union of roots has size one at \(p\mid N\) (nonzero slopes, coincident roots), size one at \(p=s,r,t\) outside \(N\) when the relevant prime divides a slope (the other form has a root and the constant form is nonzero), and size two otherwise. This gives the single \(\mathfrak S(N)/L^2\) upper for the sieve product. The prime \(2\mid N\), omitted in Corollary 2's product, changes only the absolute constant. The finitely many \(s,r,t\) factors relative to \(1-2/p\) are uniformly bounded. Discriminant primes larger than the free-variable scale also cause no issue, since omitting their positive singular-series factors only weakens this upper.

The remaining Euler factors from the two weights are at most \(\exp(\sum_{p\le O(x)}(a_\xi(p)+a_\eta(p))/p)\). For \(|\xi|\le1\), the first sum is \(O(1)\) by \(\sum_{p\le z}(\log p)/p\ll\log z\). For \(1<|\xi|<L/\log2\), split at \(\exp(L/|\xi|)\) and use the prime reciprocal sum, giving \(2\log(1+|\xi|)+O(1)\); for larger \(\xi\), the bound by twice the entire reciprocal sum implies the same inequality. Thus, after the factoring of extracted local weights, the remaining sum is
\[
 \ll \frac{Y\,\mathfrak S(N)}{L^2}(1+|\xi|)^2(1+|\eta|)^2.           \tag{4}
\]
This constant is independent of the extracted primes, their exponents, and both frequencies.

Sum the exact columns for any required tiny factor. For either leg,
\[
 \sum_{r\le x^\kappa,\ \nu\ge1}\frac{a_\xi(r)}{r^\nu}
 \ll \kappa|\xi|,
\]
including bounded \(x^\kappa\); if \(x^\kappa<2\) the sum is empty. Both extractions multiply these costs. Trivial removal of a requested small condition replaces its cost by 1, so taking the best of the bounds with zero, one, or both extractions gives the product of \(\min(1,\kappa|\xi|)\), \(\min(1,\kappa|\eta|)\) on whichever legs are required. Equivalently one may first restrict all summed rows to have no powers \(r^\nu>x^{.08}\) of a tiny prime. The omitted set at fixed \(s\) has cardinality
\[
 \ll \sum_{\substack{r\le x^\kappa\\x^{.08}<r^\nu\le1.5x}}
         (X/r^\nu+1)
 \ll Xx^{-.08+\kappa}+x^\kappa L
\]
on each leg; the divisibility residue for \(m\) is unique since \(r<s\). Bounds by divisor functions and the one factor \(\log m\) show that its **total** effect is \(O(x^{.98})\) uniformly, summing \(\sum_s 1/s=O(1)\) and \(\#s\le x^{.14}\). The same bounds apply independently of Fourier frequencies before their integrals, since \(a_\xi(a)\le\tau(a)\).

Finally \(\widehat h\) is rapidly decreasing. For the published \(f\), the explicit cosine autocorrelation is \(C^2\) with a piecewise smooth third derivative of bounded variation; multiplying by \(1-t\) and the fixed flattening does not change that property. Hence \(\widehat f(\eta)\ll_f(1+|\eta|)^{-4}\). The two frequency integrals of (4) converge absolutely, uniformly after the weighted arithmetic bounds. With an extraction on \(q\) the integral saves \(O_h(\kappa)\); on \(m\), split at \(|\eta|=1/\kappa\) to save \(O_f(\kappa\log(2/\kappa))\). Taking both minima gives the product of the two savings. Multiplying by the log weight in \(\mathcal A\) and summing the primes \(s\) with \(\sum_s1/s=O(1)\) yields (3).

## 3. What has and has not been reduced

For each fixed small \(\kappa>0\) one may also delete all squareful rows on which both legs are \(x^\kappa\)-rough: at fixed \(s\), opening a square \(p^2\) costs \(O(X x^{-\kappa}+\sqrt x)\) by a harmonic-square bound and at most one physical residue, unless \(p=s\) on the \(m\) leg where it is impossible. Divisor bounds and the sum over \(s\) make this \(o_\kappa(M_N)\). Consequently (1) differs from its **squarefree composite-composite** restriction \(P^-(q),P^-(m)>x^\kappa\) by a uniform \(O_{f,h}(\kappa\log(2/\kappa)M_N)+o_\kappa(M_N)\). On this restriction both ranks are bounded solely in terms of \(\kappa\), while the doubly tiny complement even has the product saving in (3).

This is not a finite-dimensional occupancy solution: the surviving exponent profile distributions are actual pairs in the same equation \(m+sq=N\), and their signed count is not determined by the one-leg PNT or by the upper bound here. In particular this result does not cancel the displaced balanced-semiprime packet, cannot spend any of the earlier exact-one reflected mark budget twice, and does not itself establish positive prime-pair mass at any new target. It is a bilateral use of corrected Henriot, distinct from the one-leg unprogressioned Shiu/PNT estimate in the earlier smooth quotient proof.
