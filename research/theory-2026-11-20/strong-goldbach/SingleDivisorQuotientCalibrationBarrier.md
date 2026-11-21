# A uniform positive-part obstruction to single-divisor quotient calibration

This sharpens a tradeoff in [WholeQuotientTriprimeRemoval.md](WholeQuotientTriprimeRemoval.md). It concerns a specified class of globally admissible quotient changes and **positive-part** upper estimates, not the sum with its signs retained. No pointwise lower bound for the complement is claimed.

Retain \(x=N/2\), \(L=\log x\), \(n=sq\in(x/2,x]\), \(m=N-n\), the unit domain, the exact functions \(C(m)\), \(W_s(q)\), \(D_B(q)\), and \(B=x^{.501}\) of that note. Put \(\alpha=\log_x s\). Let \(h\) be any fixed continuous real function of \((\alpha,t)\) on the compact range of relevant exponents, with \(h(\alpha,0)=0\), and form
\[
 R_h(s,q)=\frac{D_B(q)}{\log q}
        +\sum_{d\mid q,\,sd<x^{.499}}\mu(d)h(\alpha,\log_x d).
\tag{1}
\]
This gives a whole fixed-target null by (1) of the cited note. For genuine prime \(q\), \(D_B(q)=0\) and the only eligible divisor is 1, so \(h(\alpha,0)=0\) is precisely the condition of not reinserting actual prime-\(q\) rows. Windows of the form \(sd<n/B\) also give the same obstruction below: the selected divisors are unchanged on our strict exponent boxes. An additional continuous physical-coordinate dependence \(h(\alpha,t,n/x)\) is allowed if it has uniformly bounded variation in that coordinate so that the whole null applies; then the identities below hold at each value of this coordinate. The result does not apply to arbitrary rapidly varying arithmetic coefficients in \(s,d\). Continuity is not needed for the two algebraic identities on exponent profiles, but supplies the prime-product measure limit for a fixed calibrated test.

Let \(\mathcal P_{2x}(h)\) be the sum of the positive part of the physical row \(W_s(q) C(m)R_h(s,q)\) over all its eligible pairs \((s,q)\). Then, for every fixed \(h\) above,
\[
 \liminf_{X\to\infty}
   \frac{\displaystyle\sum_{X\le x\le 2X}\mathcal P_{2x}(h)}
        {\displaystyle\sum_{X\le x\le 2X}M_{2x}}
     >10^{-13}.
\tag{2}
\]
The constant is deliberately only a universal strictly positive number, not the \(.010\) signed budget. Its merit is independence from the shape and size of \(h\). In particular not all of the selected chamber costs can be made arbitrarily small simultaneously by such a null. For equicontinuous uniformly bounded families of tests, the same proof controls the convergence uniformly.

## 1. Exact six-profile relation

Fix \(\alpha\), put \(w=1-\alpha\), and work first with limiting exponents so that the prime factors of \(q\) have exponent sum \(w\). All inequalities used below have fixed power slack, so the real condition \(n\in(x/2,x]\), which changes that sum by \(O(1/L)\), does not change the divisor admissibility. Abbreviate \(h(\alpha,t)\) by \(h_t\) and temporarily write \(\gamma=h_0\).

Three exact physical profile formulas from the prior notes are sufficient:
* **Giant prime with one small factor.** For \(q=aP\), \(a\) a true prime of exponent \(b\in(.010,.070)\) and \(P>B\), the only visible divisors in (1) are \(1,a\). Here \(D_B=0\). Its multiplier is \(G=\gamma-h_b\).
* **Two macros and the small factor.** For \(q=aPQ\) of profile \(\mathcal Q_1\), select the part strictly away from the upper \(P=B\) neck so that \(saQ>x^{.499}\) with fixed power slack. The only visible divisors are \(1,a,Q\) as checked below. The exponent of \(Q\) is denoted \(t\). Here \(D_B/\log q=1\), including the composite reverse \(k\) terms, so the multiplier is \(F(t)=1+G-h_t\).
* **Three true macros.** For profile \(\mathcal Q_2\), each factor has exponent less than \(.358\) and sum \(w\). Only 1 and the three singles are visible, and \(D_B/\log q=2\). The multiplier is \(J(u,v,z)=2+\gamma-h_u-h_v-h_z\).

Put \(t_0=w/3\) and \(\Delta=.025\). At the center \(\alpha=.120,b=.065\), take \(t_1=t_2=t_3=t_0\). Write
\[
 A=J(t_0+\Delta,t_0+\Delta,t_0-2\Delta),\quad
 E=J(t_0+2\Delta,t_0,t_0-2\Delta),\quad
 D=J(t_0,t_0,t_0).
\]
The algebraic identity
\[
 1-\gamma=-D-3A+3E-3G+6F(t_0+\Delta)-3F(t_0+2\Delta)
\tag{3}
\]
follows by expanding each \(h\) value; its normalized orientation (negative or positive signs as shown) forces one of the six coefficients to have magnitude at least \((1-\gamma)/19\) in that orientation. Equal limiting exponents in this center statement do not impose equality of prime factors. The open-box version proves a mass bound and allows genuine distinct primes.

For the open-box statement, select
\[
 .119<\alpha<.121,\qquad .0645<b<.0655,\qquad
 |\eta_1|,|\eta_2|<.00025,qquad
 \eta_3=-\eta_1-\eta_2,\quad t_i=w/3+\eta_i .
\]
Use indices cyclically mod 3 and write
\[
 A_i=J(t_i+\Delta,t_{i+1}+\Delta,t_{i+2}-2\Delta),\quad
 E_i=J(t_i+2\Delta,t_{i+1},t_{i+2}-2\Delta),\quad
 D=J(t_1,t_2,t_3).
\]
Let \(\langle\cdot\rangle\) be the mean over \(i=1,2,3\). The exact identity on the box is
\[
 1-\gamma=-D-3\langle A_i\rangle+3\langle E_i\rangle-3G
        +6\langle F(t_i+\Delta)\rangle-3\langle F(t_i+2\Delta)\rangle .
\tag{4}
\]
Indeed \(\langle A_i-E_i\rangle=-2\langle h_{t_i+\Delta}\rangle+\langle h_{t_i+2\Delta}\rangle+\langle h_{t_i}\rangle\), so all evaluations cancel on expanding (4). Each expression on the right may be replaced by its indicated sign's positive part for an upper bound.

All quoted profiles are admissible with strict edges. In \(F(t_i+j\Delta)\), \(j=1,2\), the marked prime's exponent is \(w-b-t_i-j\Delta\); it belongs to \((.470,.499)\), whereas the complementary macro \(Q\) belongs to \((.317,.345)\). The marked pair \(aP\) has exponent \(w-t_i-j\Delta>.535\), and the other pair \(aQ\) exponent is \(<.411\). For eligibility in (1), \(sQ\) has exponent \(<.466\), \(s aQ\) has exponent \(1-\log_x P>.501\), \(\log_x(sP)>.589\), and \(a\) is visible. These inequalities check all proper divisor products insofar as the others are multiples of the excluded \(P\). In \(G\), the prime \(P\) has exponent \(w-b>.813\), so no divisor other than \(1,a\) can qualify. In all \(J\) shifts the three exponents are between \(.242\) and \(.345\), so each singleton is visible even with \(s\), but all pairs (and the full quotient) are excluded since each pair exponent is at least \(w-.345>.533\). All factors are polynomially large; actual equal primes are a power-small exceptional set. These comparisons can be checked at rational corners as in [the companion](check_single_divisor_quotient_barrier.py).

## 2. From oriented coefficients to true dyadic occupancy

For a positive coefficient in (4), use genuine reflected \(m\) a product of three distinct primes of exponents in \((.25,.45)\), where \(C(m)=\log m\). Its measure limit at scale \(X\), including that weight and dividing by \(X\), has density \(I_+\ge.12375>3/25\), as proved in [AdjustedTriprimePositiveBudget.md](AdjustedTriprimePositiveBudget.md), §3. For a negative coefficient in (4), use \(m=pR\), \(p,R\) genuine prime and the exponent of \(p\) in \((.10,.40)\), where \(C(m)=-\log p\); the corresponding weighted absolute density is \(I_-=\log(3/2)>2/5\), as in the prior removal note. Thus \(-D,-A_i,-G,-F(t_i+2\Delta)\) use true reflected semiprimes. The terms \(+E_i,+F(t_i+\Delta)\) use true reflected triprimes. They are not being compared at a single target via an independence assumption.

The true quotient-product measures on each box have density at least \(1/18\) relative to Lebesgue measure in the free displayed exponent coordinates and the physical \(n/X\) coordinate, after including \(W_s(q)\) and dividing by \(X/\log X\). In \(G\) these exponents are \((\alpha,b)\), with density \(W(\alpha)/(\alpha b(w-b))\); in \(F\) they are \((\alpha,b,t)\) with density \(W(\alpha)/(\alpha b t(w-b-t))\); in \(J\) they are \((\alpha,u,v)\), with density \(W(\alpha)/(6\alpha u v(w-u-v))\) over ordered exponent coordinates (factor \(1/6\) for unordered prime factors). Here \(W(\alpha)=(1-\alpha)(1-2\alpha)^2>1/3\); each denominator exponent factor is at most 1. Using the restricted ordered exponent box with that \(1/6\) only lowers the contribution even on a nonsymmetric box. The measure statements are ordinary PNT with one last true prime, followed by reciprocal-prime measures on the other labels. All projected band walls can be handled by fixed interior approximation and then letting the approximation error tend to zero; every last-prime length has a fixed positive exponent. For \(h\) continuous the positive part is an admissible continuous multiplier on each such box. The counts of repeated primes and common factors of \(n,m\) are power-small, exactly as in the referenced proof. Multiple factor orderings and s-choices do not harm the lower bound: in these shapes the marked factor and the s label are unique when designated, and for the balanced triples the only remaining multiplicity is at most 6.

The actual dyadic mass behind any of these signed positive parts is obtained by taking the even \(N=n+m\), not a separately sampled target. The fixed physical domain \(1\le(n+m)/(2X)\le2\), \((n+m)/(4X)<n/X\le(n+m)/(2X)\) has area \(3/2\), both products are odd, and the same \(\sum M_{2x}\sim3X^2/(2\log X)\) normalization therefore cancels this area. In particular each true normalized chamber mass is at least \(1/150=(1/18)(3/25)\) times the integral of the proper positive part of its quotient coefficient on its projected exponent box. In the version with a physical-coordinate test, apply all estimates with the common physical area integral normalized by \(3/2\).

## 3. Uniformity in the calibrated test

The full box in (4) has volume
\[
 \mathcal V=.002\cdot .001\cdot(.0005)^2=5\cdot10^{-13}.
\]
For a \(J\) term, the projection from \((\alpha,b,\eta_1,\eta_2)\) to its displayed exponent coordinates \((\alpha,u,v)\) has unit Jacobian in the two free \(\eta\) coordinates, including cyclic permutations, and simply forgets the \(b\) interval of length \(.001\). For an \(F\) term, it keeps \(\alpha,b\), takes one \(\eta_i\) coordinate (unit determinant if paired with \(\eta_1\) for \(i=3\)), and forgets a coordinate of length at most \(.0005\). The latter holds also for \(\eta_3\), since its fibers intersect the original \((\eta_1,\eta_2)\) box in an interval of length at most \(.0005\) when parametrized by \(\eta_1\). For \(G\) the entire \(\eta\)-box is forgotten. Thus every pushforward density is bounded by \(.001\) relative to the corresponding free exponent measure. These are full-dimensional pushforwards, rather than profiles on a measure-zero equal-exponent curve.

Let \(P\) denote the liminf on the left of (2). For each individual positive oriented test the integral over the joint box is at most \(.15 P\): the density bound \(.001\) multiplies 150 from the preceding genuine-prime lower bound. Individual chamber limits exist, and bounding all by the liminf \(P\) does not require their disjointness. Integrate (4), with \(\gamma=0\), after taking these oriented positive parts, to get
\[
 P\ge \frac{\mathcal V}{19\cdot .15}
      =\frac{1}{5700000000000}>10^{-13}.
\]
With a nonzero \(\gamma\) the integral on the left of (4) measures the remaining \(1-\gamma\) outside the reinserted actual prime-\(q\) atom. Using \(\gamma=1\) to evade the obstruction without a new prime-row estimate does not bound the original row.

This is a precise obstruction to one size-only single-divisor calibration, including variants with an extra smooth physical coordinate. It does not apply to signed cancellation, higher coupled changes whose columns go past this admissible level, or a different analytic treatment of those columns. In particular, the quotient \(aQ\) in the two-macro packet really crosses the cap on our box. No conclusion about the \(.010\) signed budget, fixed-target positivity, or binary Goldbach follows from (2).
