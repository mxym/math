# All-coupling odd twisted t–J gap through forty-one sites

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review claimed.

In the [remaining regime of the deformed spin-one t–J chain](ODD-PI-TJ-GAP.md), namely odd \(N\), twist \(\pi\), and \(t=\zeta^2-1>0\), the full gap at each odd \(3\le N\le41\) is exactly
\[
\Delta_N(\zeta)=\min\{P_N(t),\lambda_{\min}(M_N(t))\},\qquad
P_N=4+2t(1-\cos(\pi/N)),
\]
where \(M_N\) is the one-minority matrix specified in that note (order \(N-1\)). This is an all-coupling finite-length theorem, not a sampled spectral fit. The general odd-length conclusion is not claimed, nor is uniqueness of the crossover asserted here beyond the independently shown lengths three, five and seven.

The [reproducible exact verifier](verify-odd-pi-gap-finite.js), run as `node verify-odd-pi-gap-finite.js`, checks 1475 distinct comparisons at odd lengths 5 through 41 using BigInt arithmetic and bounds on cosine proven by alternating rational Taylor series. Length three is analytic in the previous note.

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

## Analytic even-content exclusion at every odd length

In fact the mixed even contents cannot improve the two-branch candidate at **any** odd length or coupling. It suffices to prove a lower bound \(4+\min(\alpha_0t,4)\), since the one-minority constant trial is below 8. Lengths \(3,5\) are covered separately. Below \(N\ge7\); the even momenta closest to zero are already excluded. Use \(b,c\) from the rank-one comparison before integer rounding, and put \(\theta=\pi/N\), \(h=2j/L\in(0,1]\). Then
\[
b\le\alpha_0(2h-h^2),\qquad
c\ge\alpha_0(2h+h^2).
\]
For the first inequality, concavity of sine on \([0,\theta]\) implies \(1-\cos((1-h)\theta)\ge(1-h)^2(1-\cos\theta)\) by integration. For the second put \(y=1+h+\varepsilon\), \(\varepsilon=2/L\). The second closest angle equals \(y\theta\), and integration of \(\sin z\ge z-z^3/6\), with \(1-\cos\theta\le\theta^2/2\), gives \(c/\alpha_0\ge y^2-1-\theta^2(y^4-1)/12\). Use \(y^2-(y-\varepsilon)^2\ge\varepsilon y\) and \(\varepsilon\ge\theta^2 y^3/12\). The latter follows from \(y\le2N/L\) and \(3L^2\ge N\pi^2\) for \(N\ge7\). The lower numerator used in this integration is positive on the indicated range.

First suppose \(t\le4/\alpha_0\), with target \(4+\alpha_0t\). The exact kink gap obeys \(g/t=\gamma+4/t\ge2\alpha_0\), so the permitted overlap threshold satisfies
\[
\frac{c}{b+c}(1-bt/g)\ \ge\
\frac{(2+h)(1-h+h^2/2)}{4}>\frac13.
\]
The last inequality follows by minimizing \(2-h+h^3/2\) on \([0,1]\) (its minimum is \(2-(2/3)\sqrt{2/3}>4/3\)).

For a nonreal rotation phase, any normalized nonnegative vector has squared projection at most \(1/3\). To see this, on a rotation orbit of length \(\ell\) which contributes at that phase, let \(m\ge3\) be the order of the phase. Align the complex sum defining its projection to be real, drop contributions with negative cosine, and apply Cauchy–Schwarz. It suffices that the sum of squared positive parts of the cosines at the \(m\) equally spaced angles, in any orientation, is at most \(m/3\) (the pattern repeats \(\ell/m\) times). For even \(m\) this sum is \(m/4\) by antipodal symmetry. For odd \(m\) there are \((m-1)/2\) or \((m+1)/2\) consecutive positive cosines. In the latter case their center has absolute angle at most \(\pi/(2m)\) and the sum of their doubled cosines is nonpositive. In the former case the geometric progression bounds the sum of their squared cosines by \((m-1)/4+1/(4\cos(\pi/m))\). Both bounds are at most \((m+1)/4\le m/3\). This applies to the nonnegative kink vector.

The only remaining rotation phase in the bad block is the real value \(-1\), which occurs for \(q=\pi\), \(h=1\). Here \(b=\alpha_0\), \(c\ge3\alpha_0\); writing \(s=\alpha_0 t\le4\), the threshold is at least \(3/(4+s)\). The positivity argument on each even orbit already gives \(p_{-1}\le1/2\), as in the [uniform interval proof](ODD-PI-TJ-GAP.md#uniform-analytic-interval-for-even-mixed-contents), so \(s\le2\) is covered. Also
\[
p_{-1}\le \tfrac14\|\phi-R\phi\|^2
 =\tfrac12(1-\langle\phi,R\phi\rangle)
 \le\tfrac12(1-\operatorname{sech}(\pi/\sqrt s)).
\]
Indeed the rotation amplitude ratio takes two positive values \(a=\nu^k,b_1=\nu^{-(L-k)}\) (or exchange the content by reflection), where \(\nu=(\zeta-1)/(\zeta+1)\). Under squared amplitudes its second moment is 1, hence its mean is \((1+ab_1)/(a+b_1)\), by the quadratic equation with roots \(a,b_1\). Writing \(a=e^{-A_1},b_1=e^{B_1}\), this is at least \(\operatorname{sech}((A_1+B_1)/2)=\operatorname{sech}((L/2)|\log\nu|)\). Use \(|\log\nu|=2\operatorname{artanh}(1/\zeta)\le2/\sqrt t\), by integrating the derivative bound, and \(L\sqrt{\alpha_0}<\pi\). On \(s\in[2,3]\) use \(\cosh(\pi/\sqrt2)<7\) to get \(p_{-1}<3/7\). On \(s\in[3,4]\) use \(\cosh(\pi/\sqrt3)<4\) to get \(p_{-1}<3/8\). For example these \(\cosh\) bounds follow by substituting \(9/4\) and \(11/6\), respectively, and bounding the tail after degree four by a geometric series using the successive term ratios. This finishes \(s\le4\).

For \(t\ge4/\alpha_0\) use the capped target 8. Write \(u=4/t\le\alpha_0\), and let \(a_0,a_1\) be the two smallest rotation energies before scaling by \(t\). If \(a_0\ge u\), positivity is immediate. Otherwise the same rank-one criterion has threshold
\[
\frac{a_1-u}{a_1-a_0}\frac{\gamma+a_0}{\gamma+u},
\]
which is nondecreasing as \(u\) decreases. For nonreal phases the preceding \(1/3\) bound is uniform in \(t\); for the \(-1\) phase the bound from the hyperbolic cosine only decreases as \(t\) increases. Thus the criterion still holds. This proves the even exclusion uniformly; the remaining obstacle to an arbitrary-length theorem is the odd mixed content \(k\ge3\).

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
