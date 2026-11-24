# A safe-support obstruction for the genuine P3 cutoff

Written research note, 2026-11-24. Not a proof of P3. This rules out improving the ordinary affine Selberg main term by **any** downward two-label generating region whose expanded products are certified merely by pairwise exponent sums in the union of the two currently proved arithmetic regions. It does **not** rule out genuine LCM savings, cancellation of forbidden cross terms, more powerful analytic input, or a different non-square/Buchstab argument. It applies to the genuine rough cutoff .06 or .07, not merely to the earlier .02 experiment.

## 1. Geometry and a strict loss lemma

Keep \(q\) at exponent \(t\in[.20,.23]\) with \(H=\sqrt N\). Write
\[
 D_0=.5-t,\qquad T=D_0/2,\qquad V=\tfrac23(.25-t).
\]
For the exponents \((u,v)\) of the expanded divisors on \(p\) and its true cofactor \(j=(N-p)/q\), respectively, the two available sufficient domains (ignoring shaves, which only enlarge them) are
\[
 \mathcal D_{\rm aff}:\ u+v\le D_0,\qquad
 \mathcal D_{\rm PW}:\ u+3t+\tfrac52v\le1 .
\]
The two sloping boundaries meet at \(v=2V\). In particular, at any \(v\ge2V\) belonging to the union necessarily implies \(u+v\le D_0\).

Let \(\mathcal A\subset\mathbb R_{\ge0}^2\) be a downward generating set for the individual Selberg polynomial, write \(F(y)\) for the height of its \(x\) section (zero where the section is empty), and assume the strong *pairwise sum certificate*
\[
 \mathcal A+\mathcal A\subset\mathcal D_{\rm aff}\cup\mathcal D_{\rm PW}.
\]
No regularity beyond measurability and the downward property is needed; take limits inside the closed safe domains if heights are suprema rather than attained. For any \(\mu\ge .05\), let \(w_\mu(y)=\rho_{\rm Dickman}(y/\mu)\). The claim is
\[
 \int_0^\infty F(y) w_\mu(y)\,dy
 \ \le\ \int_0^\infty (T-y)_+w_\mu(y)\,dy
       -\frac{\Delta}{120},
 \qquad
 \Delta=\sup_{y\ge0}(F(y)-(T-y)_+)_{+}.
\]
Thus an actual positive extension past the old triangle incurs a strict net denominator loss, even if the shape is very irregular. If all sections are within the triangle the assertion with \(\Delta=0\) is immediate.

**Proof.** Any active \(y\ge V\) self-pairs above \(v=2V\) and forces \(x+y\le T\); in particular there is no active \(y>T\). Define the surplus \(d(y)=F(y)-(T-y)\) on \([0,T]\). A positive surplus can only occur at \(y<V\). By self-pairing in the other region,
\[
 d(y)\le \tfrac32(V-y)
\]
for such a point: the inequality \(2F(y)+5y+3t\le1\) and \(2T=.5-t\) give this exactly.

Fix a height \(h>0\) with \(G_h=\{y:d(y)>h\}\) nonempty, and put \(y_h=\sup G_h\). Then \(y_h\le V\le1/30\), and \(h\le\tfrac32(V-y_h)\) by taking a limit. For any \(y'\in(2V-y_h,T-h)\), choose \(y\in G_h\) sufficiently close to its supremum that \(y+y'>2V\). If \(y'\) is active then the union of the two supported regions at total cofactor exponent \(y+y'\) enforces the affine inequality, whence \(d(y')+d(y)\le0\), so \(d(y')<-h\). If inactive there is already loss \(T-y'>h\). Endpoints are irrelevant to the integrals.

The lost strip contains the subinterval \((1/15-y_h,1/10)\), because \(2V\le1/15\) and
\[
 T-h\ge T-\tfrac32 V+\tfrac32y_h=t/2+\tfrac32y_h\ge .10+\tfrac32y_h.
\]
Its weighted mass is at least \(y_h+1/120\). It suffices to check \(\mu=.05\), since Dickman is nonincreasing in its argument. For \(y_h\le 1/60\), on \([1/15-y_h,.10]\) one has \(w_{.05}(u)=1-\log(20u)\ge2-20u\), so the interval mass is at least \(10(1/30+y_h)^2\). Its excess over \(y_h\) has minimum \(1/120\) on that range. For \(y_h\ge1/60\), split at \(1/20\): the lower pieces give \((y_h-1/60)+\int_{1/20}^{1/10}(2-20u)\,du=y_h+1/120\). Meanwhile \(w_\mu\le1\), so the whole positive height set \(G_h\subset[0,y_h]\) has weight at most \(y_h\). Integrate the positive-minus-negative height masses over \(h\) (layer cake). All \(0<h<\Delta\) have the strict loss at least \(1/120\), and elsewhere there can be no positive mass. This proves the claim. \(\square\)

## 2. Why it applies to the genuine square main term, not merely a drawing

For a precise consequence keep \(N=2^k\), \(q\) genuinely prime at the stated scale, and take a fixed bounded downward log region \(\mathcal A\) obeying the pairwise sum certificate. Squarefree raw monomials are indexed by \(r_0\mid p,s_0\mid j\) meaningfully disjoint: any shared odd prime would imply it divides \(N\), and at 2 only one local test is used. The \(p\)-side can use all primes occurring in its allowed support; the \(j\)-side only primes below \(N^\mu\). In the range \(.05\le\mu\le.07\), all generator prime sizes are below \(q\) except the harmless limiting equality \(q=Q,N^{.2}\), which is absent when \(Q<q\le2Q\): self-pairing gives \(\max x\le .5-1.5t\le t\). The linear forms \(p=N-qj,j\) produce the ordinary CRT local densities for each labelled divisor condition.

The optimal denominator in the complete local model has planar exponent density \(w_\mu(y)\,dx\,dy\), not constant area. This is precisely the argument in the [short-cutoff tilted paper](DyadicTiltedTwoFormShortCutoff.md) and can be applied to any fixed downward shape, as follows:

* Precondition at small primes \(\ell\le Z=L/(\log L)^2\), either using the exact product of the zero-event indicators (its divisor support is \(N^{o(1)}\)) or, for a **lower bound on the best possible square main term**, simply retain only these survivors since a square is nonnegative. Conditioning a polynomial by setting these small indicators to zero leaves a downward-supported polynomial with value 1 at the completely sifted state.
* At each \(\ell>Z\), centered indicators normalized to variance 1 for the two sides have covariance \(-1/(\ell-1)\), and different unlabelled prime supports are orthogonal. Within a support the full tensor covariance and each principal submatrix have eigenvalues \(1+o(1)\), uniformly, since any support of product \(N^{O(1)}\) has \(\sum_{\ell\mid d,\ \ell>Z}1/\ell=o(1)\). Thus the minimum variance of a normalized square polynomial is \((1+o(1))/\sum v_a^2\), where \(v_a\) collects its centered basis values at the zero-hit state. The lower bound is Cauchy–Schwarz in the basis; the normalized admissible direction proportional to \(v_a\) attains the corresponding upper up to \(1+o(1)\). The basis change uses only submonomials, allowed by downward closure; alternatively replacing a generating set by its downward closure does not spoil the sum certificate, since both arithmetic regions are downward.
* The diagonal sum \(\sum v_a^2\) has weights \(\prod_{\ell\mid r_0s_0}(\ell-1)^{-1}\) on squarefree coprime pairs. The unrestricted \(p\)-side summation has linear cumulative asymptotic in \(\log r_0\). The \(j\)-side smooth-divisor summation has density \(\rho_{\rm Dickman}(y/\mu)\) in its log exponent, by the finite inclusion-exclusion/delay argument in the tilted proof. The common small-prime normalization is \(c_Z^2 L^2\), and the coprime restriction changes the result by \(1+o(1)\) (the omitted intersection weight is bounded using the uniformly tiny reciprocal weight of large primes dividing the other support). For any fixed downward shape, approximate its bounded monotone section function by finite Riemann rectangles or use weak convergence with its countably many discontinuities; the resulting denominator is \((c_Z^2 L^2)(\int F(y)w_\mu(y)dy+o(1))\).
* Finally the probability of surviving the small local primes divided by \(c_Z^2\) tends to \(S_N\), exactly as in the old affine benchmark. Thus the obstruction is to decreasing the **actual leading constant of this square upper construction**, not to a formal rearrangement of an unweighted region. The common comparison affine density is precisely \(\int(T-y)_+ w_\mu(y)dy\).

The all-pairs condition concerns **sums of exponent coordinates of two generator monomials**, i.e. a conservative bound on the later LCMs. It is sufficient, not necessary. An actual product term can instead have much smaller \(v_\ell\)-support because of genuine LCM overlaps, or vanish when a prime is assigned opposite forms in the two monomials (for an odd prime not dividing \(N\)); signed coefficients may also cancel unsafe terms. Those situations are not covered by this result. It also does not cover a Buchstab switch whose correction requires different analytic information rather than ending as a normalized square on the same certified region.

## 3. A concrete next analytic threshold rather than more shape tuning

One route escaping the no-go is to improve the q-aggregated nonzero Poisson remainder. In the same notation as the [joint Poisson–Weil paper](PrimeOppositeMiddleJointPoissonWeil.md), for a block \(r\asymp R=N^u,s\asymp S=N^v,q\asymp Q=N^t\) the existing floor error is
\[
 N^{o(1)}\bigl(R S Q^{1/2}+R^{1/2}Q^{3/2}S^{5/4}\bigr).
\]
On the signed coefficients of a genuine two-label Selberg square, a replacement of the second term by \(R^{1/2}Q^{3/2}S^{9/10}\) (or an equivalent gain in the q correlations) would be sufficient for a strict improvement with the **actual** .06 roughness in at least \(t\in[.20,.201]\). This is an unproved and demanding target; the exponent \(9/10<1\) shows why simply discarding the square-root loss at s and then summing s absolutely will not prove it.

Indeed the new safe half-plane would be \(u+3t+1.8v\le1\), whose crossing with the old affine boundary is at \(v=2V'\), \(V'=(.5-2t)/(2(.8))\ge .06125\) in this strip. Take generators
\[
 x+1.8y\le T+.8V'-.0005.
\]
Their squares obey the new half-plane with fixed spare, and the diagonal term, \(h<q\), and completion lengths behave as in the old proof (max u ≤.399 at t=.20). For the actual .06 cutoff, the truncated Dickman mean in the $y$ coordinate is at most $.06$: the identity $u\rho(u)=\int_{u-1}^u\rho(v)\,dv$ (with $\rho(v)=0$ for $v<0$) gives mean $1$ in the $u$ coordinate, and truncation from above can only lower it, so the new denominator would exceed the old affine one by at least \([.8(.06125-.06)-.0005]\cdot .06 = .00003\), with all signs positive. This is a sufficient test for breaking the actual .06 middle strip constant, not by itself sufficient for the global P3 budget. A route using actual LCM sharing in the dangerous cross terms could escape with a smaller analytic gain; the preceding geometric lemma says where those cross terms must be addressed.
