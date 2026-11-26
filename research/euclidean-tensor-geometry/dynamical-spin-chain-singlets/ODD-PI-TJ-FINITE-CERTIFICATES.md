# All-coupling odd twisted t–J gap through thirty-one sites

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review claimed.

In the [remaining regime of the deformed spin-one t–J chain](ODD-PI-TJ-GAP.md), namely odd \(N\), twist \(\pi\), and \(t=\zeta^2-1>0\), the full gap at each odd \(3\le N\le31\) is exactly
\[
\Delta_N(\zeta)=\min\{P_N(t),\lambda_{\min}(M_N(t))\},\qquad
P_N=4+2t(1-\cos(\pi/N)),
\]
where \(M_N\) is the one-minority matrix specified in that note (order \(N-1\)). This is an all-coupling finite-length theorem, not a sampled spectral fit. The general odd-length conclusion is not claimed, nor is uniqueness of the crossover asserted here beyond the independently shown lengths three, five and seven.

The [reproducible exact verifier](verify-odd-pi-gap-finite.js), run as `node verify-odd-pi-gap-finite.js`, checks 637 distinct comparisons at odd lengths 5 through 31 using BigInt arithmetic and bounds on cosine proven by alternating rational Taylor series. Length three is analytic in the previous note.

## Shared operator comparison

The no-hole and two-or-more-hole sectors can be excluded at all sizes by the [cycle argument](CIRCULAR-EXCLUSION-CYCLES.md#consequence-for-the-odd-pi-twisted-deformed-tj-chain). In the relative one-hole blocks, let \(L=N-1\), \(k\) the number of minority-letter \(Y\), and \(R\) the cyclic rotation. In the inversion gauge,
\[
H_k(q)=4I+S_k+t\,a_q(R),\qquad a_q(R)=2I-e^{iq}R-e^{-iq}R^{-1}.
\]
We use \(\zeta>1\) by spin exchange. Put \(x=(\zeta-1)/(\zeta+1)\in(0,1)\), so \(t=4x/(1-x)^2\). The kink line of \(S_k\) has normalized vector \(\phi\) whose entries are proportional to \(x^{\mathrm{inv}(w)}\) after an orientation choice, and
\[
S_k\succeq g_\mathrm{exact}(I-|\phi\rangle\langle\phi|),\qquad
g_\mathrm{exact}=4+\gamma t,\quad \gamma=2(1-\cos(\pi/L)).
\]
This is the positive-gap theorem for the finite kink XXZ chain [Koma–Nachtergaele, Proposition 2](https://arxiv.org/pdf/cond-mat/9512120#page=8) with normalization \(2(\zeta^2+1)\) and anisotropy \((\zeta^2+1)/t\), as detailed in the five-site proof. Reflection/complement and complex conjugation allow us to reduce content to \(k\le L/2\) and momenta to nonnegative \(q\le\pi\). Pure background \(k=0,L\) supplies \(P_N\); one minority \(k=1,L-1\) gives \(M_N\). For odd \(k\), positivity restricts to \(q=0\); for even \(k\) the \(q=\pm\pi/N\) blocks are bounded by the exact separate minimization of \(S_k\) and the rotation term.

Write \(D=10^6\) (an integer scale), \(\alpha_0=2(1-\cos(\pi/N))\), and choose an integer \(\beta\le D\gamma\) by rounding a rigorous rational lower bound down. Thus \(g=(t/D)A(x)/x\) is a lower bound on \(g_\mathrm{exact}\), where
\[
A(x)=D(1-x)^2+\beta x.
\]
For any positive definite \(B_0\), the rank-one inequality \(B_0-g|\phi\rangle\langle\phi|\succeq0\) is equivalent to \(g\langle\phi,B_0^{-1}\phi\rangle\le1\), by conjugation.

## Even mixed sectors

Let \(q=(2j+1)\pi/N\) with \(1\le j\le L/2\). The closest rotation eigenphase to \(-q\) is indexed by \(j\) up to a sign, at angular distance \(r_0=(L-2j)\pi/(NL)\). The next closest distance is \(r_1=2\pi/L-r_0\). Here \(r_0<\pi/N<r_1\). Write \(a_\mathrm{bad}=2(1-\cos r_0)\), \(b=\alpha_0-a_\mathrm{bad}\), \(c=2(1-\cos r_1)-\alpha_0\). The verifier chooses integers \(B\ge Db\), \(C\le Dc\), with \(B,C>0\) and \(B<\beta\). Under the rank-one comparison, it suffices that the squared overlap \(p\) of \(\phi\) with the closest rotation eigenspace satisfy
\[
p\le\frac{C(A-Bx)}{(B+C)A}.
\]
Indeed one may bound the bad diagonal by \(g-t B/D>0\) and the others by \(g+t C/D\) before the rank-one subtraction.

Put \(Z=\sum_w x^{2\mathrm{inv}(w)}\). The rotation character average expresses \(p\) as \(1/(LZ)\) times \(\sum_{w,l}\cos(2\pi jl/L)x^{\mathrm{inv}(w)+\mathrm{inv}(R^l w)}\). Let \(C_r\) be the polynomial of this numerator with cosine coefficients multiplied by \(D\) and replaced by rigorous integer upper bounds. Then \(p\le C_r/(LD Z)\) on \((0,1)\). The sufficient inequality is verified by certifying nonnegativity of
\[
C L D\,Z(A-Bx)-(B+C)A C_r
\]
there. This does not assume that the kink vector is an eigenvector of rotation.

## Odd mixed sectors

Let \(\Pi_0\) project onto the \(R\)-invariant subspace. Choose integer \(\rho\le 2D(1-\cos(2\pi/L))\) by lower rounding, and integer \(\alpha\ge D\alpha_0\) by upper rounding. Then \(t a_0(R)\succeq(t\rho/D)(I-\Pi_0)\). Use \(E=LZ-\sum_{w,l}x^{\mathrm{inv}(w)+\mathrm{inv}(R^l w)}\), so \(1-p_0=E/(LZ)\) for \(p_0=\|\Pi_0\phi\|^2\). For target excess \(T<\min(g,t\rho/D)\), positivity above \(T\) follows from
\[
g(t\rho/D)(1-p_0)\ge T(g+t\rho/D-T),
\]
the same rank-one test. Below a rational cut in \(x\), take \(T=t\alpha/D\), verifying \(\alpha<\min(\beta,\rho)\). The polynomial to check is
\[
\rho A E-\alpha L Z(A+(\rho-\alpha)x).
\]
Above the cut, take \(T=4-4/L\), bounding the one-minority branch's excess by its constant trial. Write \(B=D(L-1)(1-x)^2\), so \(T/t=B/(D L x)\). The polynomial to check, multiplied by an extra positive factor \(L\) in the code, is
\[
\rho L x A E-Z B(L A+L\rho x-B).
\]
At the cut the verifier ensures \(T<\min(g,t\rho/D)\) by using the lower bounds \(g\ge t\beta/D\) and \(t\rho/D\); the inequalities persist above the cut since \(t\) strictly increases. The cut is the least \(j/1000\) for which \(4-4/L\le (\alpha/D)t(j/1000)\), found with exact integer inequalities; its exact value has no physical significance. Together the inequalities place the odd mixed sector above at least one of the two candidate branches for every coupling.

## Numerical-free certification

The polynomial coefficients are obtained without enumerating binary words. If \(G_{n,k}(x)=\sum_w x^{2\mathrm{inv}(w)}\) on length-\(n\), content-\(k\) words, then \(G_{n,k}=G_{n-1,k-1}+x^{2k}G_{n-1,k}\), by appending a 1 or a 0. For a rotation by \(l\), split its word into pieces of lengths \(l,L-l\); if the first has \(r\) ones, the sum of full-word inversion counts before and after rotation equals twice the two internal counts plus \(r(L-l-k+r)+(k-r)(l-r)\). Thus the shift autocorrelation is a sum over \(r\) of \(G_{l,r}G_{L-l,k-r}\) multiplied by that corresponding power of \(x\). This dynamic program yields \(Z\) and the polynomials before the rigorous cosine weights are applied. A polynomial is checked on \([a/d,b/d]\) by setting \(x=(a+by)/(d(1+y))\), and multiplying by \((d(1+y))^{\deg}\). All coefficients of the resulting integer polynomial are nonnegative and at least one is positive in each verified comparison. Continuity covers interval endpoints in \((0,1)\). The implementation encloses \(\pi\) by Machin's arctangent identity and alternating series with rational integer-scaled terms. It reduces cosine arguments to \([0,\pi/2]\) using symmetries, and bounds them with alternating Taylor polynomials, rounding outward independently at every step. Array indices and lengths use only small exact integers. No floating-point spectral estimate is used in the proof.
