# Three-region composite extension of the prime-axis model, with a certified first rough-window obstruction

Research note, 2026-11-24. [The prime-axis model](CQPrimeAxisAngularCountermodel.md) itself survives the currently invoked prime-axis tests. This note is **only** an abstract extension to two composite axes and its first tested genuine failure, not a model of fixed-N integers and not an obstruction theorem for every nonnegative extension. Work with its base density \(g=d\nu/d\mu\) (no optional tail perturbation), genuine angular \(\mu\), and sharp amplitude \(h\). Thus \(g=1\) outside the \(.123\)-rough composite set, \(0\le g<3.446\), and \(\int h\,d\mu=1,\ \int gh\,d\mu=2\). Put the same \(\nu\) on both prime–composite orientations and no prime–prime rows. All output below is abstract normalized same-target data designed to test the required relations.

## 1. The explicit symmetric nonnegative outer blocks

Partition actual angle types by their true least:
\[
 R=\{t>.123\},\qquad L_0=\{.04<t\le.123\},\qquad T_0=\{t\le.04\}.
\]
Write \(r=m(R_{.123})\) for the **full** ordinary rough count including its one prime unit, \(m=r-1=\mu(R)\); \(\int_R g=r\) and \(\int_R (g-1)h=1\) by construction. Put \(u=\int_R h\), \(v=\int_{L_0}h\), \(w=\int_{T_0}h\); \(u+v+w=1\). All h-weights integrate absolutely. Define on \(R\)
\[
 f(x)=r-g(x)>0,\quad F=\int_R f\,d\mu=r(r-2)=m^2-1,
 \quad A_R=\frac{\int_R hf\,d\mu}{F}=\frac{m u-1}{F},
 \quad d_R(x)=2-g(x)-A_R f(x)-v .
\]
The reference composite–composite density is symmetric, with entries (each relative to the genuine product \(d\mu(x)d\mu(y)\)):
\[
 K_{RR}(x,y)=f(x)f(y)/F,\qquad
 K_{R,L_0}=K_{L_0,L_0}=K_{L_0,T_0}=1,\qquad
 K_{R,T_0}(x,y)=a(x)=d_R(x)/w\quad(x\in R).
\]
The reflected entries are transposes. Use \(K_{T_0,T_0}=\lambda\) initially, where
\[
 \lambda=1+(m-u)^2/(F w^2).
\]
This is a positive, bounded explicit kernel, not a correction by negative masses.

Numeric signs and ranges follow from genuine ordinary data. The old actual .123 rough estimates via ordinary averaging/certificate give \(4.4784588\le r<4.566568\). The full true positive rank-2/3 mass contributes \(p>2.0624\) in \(R\) and all negative scores in \(R\) are in \(A\), \(m(A)<.08472\), so \(u>1.97768\). For upper \(u<2.932\), use \(p<2.0625\), ranks 5 and 6 always negative, odd ranks \(\ge7\) zero, rank-four positive amplitude at most \(96\sqrt8/4^4<1.061\) (drop its negative \(\mathbb E|W|\) term), and rank-eight positive cap \(1.2\) with ordinary mass \(<10^{-12}\) from its true floor simplex volume. Rank-four count itself is at most \(\frac16\log((1-3(.123))/.123)^3<1.7^3/6\): multiply the symmetric actual reciprocal integrand by the sum of the four coordinates to cancel one denominator at a time, then bound each of the three unrestricted remaining widths by \(1-3(.123)\). All rational comparisons are in the companion runner.

For \(w\) the ordinary fixed-floor Dickman–Buchstab formula of ExplicitTinyUnion applies at \(b=.04\), giving \(-.875<w<-.874\). To audit its small error at this cutoff, \(D_k=\sup_{s\ge k}|\omega'(s)|\) satisfies \(D_2\le1,\ D_k\le D_{k-1}/k\) by \(s\omega'(s)=\omega(s-1)-\omega(s)\). Thus for \(s\ge12.5\), \(|\omega(s)-e^{-\gamma}|<3/12!\). The normalized ordinary signed divisor integral \(b^{-1}\int F(t)d(1_{t\ge0}\rho(t/b))\,\omega((1-t)/b)\) is supported in \(t\le.5\); the total variation of the Dickman factor is at most 2 including its initial jump. Replacing its Buchstab factor therefore costs less than \(6/(b\,12!)\). Integrate the Dickman term by parts as in the pinned proof. The polynomial extension of \(F'\) above \(1/2\) may be inserted at error less than \(3\cdot10^{-6}\): use \(|F'_{\rm poly}(bv)|\le1000(1+(bv)^4)\), \(\rho(v)\le1/\lfloor v\rfloor!\), and sum from \(j=12\) with ratio of consecutive upper terms \(<.11\). The signed polynomial \(w_b=-32b+288b^2-(2720/3)b^3+(3040/3)b^4=-.87463253333\ldots\) is thus within \(4\cdot10^{-6}\) of the real \(w\). This is a genuine ordinary normalization, not a model paired estimate.

Since \(u<m\), \(A_R<1\) (and \(A_R>0\)). Viewed as a function of \(g\ge0\), the largest possible \(d_R\) is at zero, where
\[
 d_R(0)=1+w+(1-u)/(r-2)<0.
\]
Thus \(a(x)>0\). Its mass is \(\int_R a=m\), because \(\int_R d_R=r-2-(m u-1)-mv=m w\). The runner certifies \(1.033<\lambda<1.30\).

## 2. Exact signed projection identities, and which genuine inequalities they satisfy

For \(x\in R\), the row against \(h\) in the composite domain gives \(A_R f(x)+v+a(x)w=2-g(x)\) by definition. For \(x\in L_0\) the row is exactly \(u+v+w=1=2-g(x)\). For \(x\in T_0\), the contribution from \(R,L_0\) is \(A_h+v\) with \(A_h=\int_R h a\), a constant. Direct integration of \(a=d_R/w\) gives \(w A_h=(1-v)u-1-F A_R^2\). Therefore
\[
 w(1-v-A_h)= w^2-u^2+1+F A_R^2
      =w^2+(m-u)^2/F,
\]
and the constant \(K_{T_0,T_0}=\lambda\) supplies exactly the missing \(h\)-row \(1-v-A_h=\lambda w\). Adding the prime companion term \(g(x)\) to each composite row gives exactly the target 2 on all ordinary composite angular tests. Integrating against \(h\) proves \(HH=0\); the two prime–composite raw projections are each 2 and prime–prime absent, so \(VV=4\). This concerns formal data on the real angular types, not actual arithmetic rows.

For **every** rough cut \(a\in[.04,.123]\), the model row to the full rough receiver \(R_a\) equals exactly \(m(R_a)\) for every composite source, including \(Y\), its actual low ranks and all true compact tests. If \(x\in R\), the \(R\) contribution is \(f(x)\), plus prime \(g(x)\), plus ordinary mass of the \(L_0\) slice. If \(x\in L_0\), the same roles give \(m+1\) plus that slice. If \(x\in T_0\) use \(\int_R a=m\) instead, with the same result. The \(T_0,T_0\) term never enters these rough rows; this is the precise scope of the positive repair. The full both-rough occupation including the two disjoint real-prime-type axes in this model is \(m(R_a)^2\), obtained by integrating \(m(R_a)-g\) against composite \(R_a\) and adding \(2\nu(R_a)\). These are the ordinary centers of the genuine interval constraints by averaged actual DHR / one-arm rough estimates. In particular it synchronizes the requested \(.04,.105,.123\) row and ambient constraints, not just \(.123\).

It also realizes some named true pair inequalities, still only in this tested extension:
- \(B_0\) and \(B_6\) lie in \(L_0\), and \(C\) lies in \(T_0\), so their cross and \(B_0,B_0\) are exactly the ordinary products. In particular \(B_6C=m(B_6)m(C)\) in each orientation, safely below the actual rank-six–deep bound \(2.742208\,m(B_6)\). Indeed \(m(C)<2.011\): use the pointwise real \(100tv\) tag amplitude, cancel the two small-angle denominators, and bound genuine residual quotient ordinary density by \(\omega(X/z)/z\le .6/z\) (here \(X/z>2\)). The exact accepted-cell sum \(\sum60\Delta t\Delta v/z<2.010235\) is replayed. This bound also gives \(\lambda m(C)<2.615< U_C\), so the model \(CC=\lambda m(C)^2\) is within the genuine deep receiver cap. Replacing \(B_6\) by its genuine squared weight in this cross works identically.
- If an old non-tiny negative source belongs to \(R\), it has \(g=1\) pointwise; hence in the model its \(R,T_0\) coupling scalar is \(a(1)=1+(m-u)/(F w)<1\), while all old \(\Gamma_-\) types have least \(>.04\). For any parts of \(Y,\Gamma_-\) not crossing \(R,T_0\) the density is 1. Thus total \(Y,\Gamma_-\) is at most \(2m(Y)m(\Gamma_-)\). The old smallest-label caps also give the unpaired \(m(B_0)\le U_6+m(B_8)<4.925\): in the ordinary least-tag integral the residual count factor is \(\omega((1-t)/t)/t\le.6/t\), just as in the genuine reverse receiver, and the verified ordinary rank-eight bound is .016. Together \(m(Y)<6.936,\ m(\Gamma_-)<.089087\), so this particular modeled overlap obeys the genuine \(1.651\) upper. Against the actual signed tiny type \(T_{\rm tiny}\subset T_0\), the model \(Y,T_{\rm tiny}\) has negative mean \(m(T_{\rm tiny})[m(B_0)+\lambda m(C)]\); no claim of satisfying every tiny test.
- Every above prime-axis constraint from the previous countermodel is unchanged, since only composite–composite rows were added. Not all finer actual fixed-target constraints have been checked, and the next section excludes the construction outright under one of them.

## 3. First explicit incompatibility, robust under arbitrary internal T-repair

Fix the outer blocks **as above**, but now allow *any symmetric nonnegative* \(K_{T_0,T_0}\), not necessarily constant. Suppose it preserves the genuine \(h\)-row identities and also obeys the true ordinary-BV rough receiver interval at cutoff \(\delta=.010\). This particular interval is tight enough to make repair impossible.

Set \(k_\delta=56.14571788103,\ U_\delta=56.14617889842\) as outward bounds on \(e^{-\gamma}f_1(10)/.010,\ e^{-\gamma}F_1(10)/.010\). They follow by ordinary genuine compact product BV at level \(N^{.10}\) and cutoff \(N^{.01}\), and exact linear delay recurrence at ratio 10 with outward mesh \(10^{-5}\), \(10^{12}\) integer ticks (companion check). Hence these are genuine true uniform bounds for **any nonnegative fixed-rank compact angular source**, even one in \(T_0\). Their width is \(<.000462\). The genuine ordinary \(m(R_\delta)\) lies in their interval by the true dyadic mean. Let \(S=\{\delta<t\le.04\}\), \(\sigma=\mu(S)=m(R_\delta)-m(R_{.04})>41.84\), using the old \(m(R_{.04})<14.303193375\).

For each test on \(T_0\), its modeled full rough receiver above \(\delta\) has prime plus \(R\cup L_0\) contributions exactly \(m(R_{.04})\) from the *fixed* outer blocks. Thus the internal count to \(S\), when normalized by any such source weight, may differ from \(\sigma\) by at most \(U_\delta-k_\delta<.000462\). By symmetry, the signed average over \(S\) of all rows' \(T_0\) contribution is forced to lie within \(.000462\int_{T_0}|h|\,d\mu\) of \(\sigma w\):
\[
 \int_S\!\left[\int_{T_0} h(y)K(x,y)d\mu(y)\right]d\mu(x)
   =\int_{T_0} h(y)\left[\int_S K(y,x)d\mu(x)\right]d\mu(y).
\]
One can first test \(h_\pm\) on genuine compact positive floors in \(T_0\), apply the uniform interval, and use their absolute ordinary integrability to release those floors. No new \(h\)-tail assumption on arithmetic pairs is required for this mathematical constraint in the relaxed model.

For an explicit ordinary absolute constant, the Fourier rank-sum inequality of [the prime-axis note](CQPrimeAxisAngularCountermodel.md) gives
\[
 \int |h|\,d\mu\le (2/\pi)\int_0^\infty|\widehat F(v)|e^{J_1(v)}\,dv<700.
\]
Use the same pinned left extension as ExplicitTinyUnion, \(\|\widehat F\|_\infty<1.203\) and \(|\widehat F(v)|<8000v^{-4}\): the old C4 computation bounds the left variation plus the base .5-branch fourth derivative integral by \(<7316.488\) even with its nonnegative taper terms, and returning to the original branch adds only its \(96\) jump at .5. Use \(e^{J_1(v)}\le4.6\max(1,v^{51/40})\). Split the integral at 1 and 10; \(10^{2+11/40}<200\) and \(10^{69/40}>50\) by integer powers enclose the two powers, and \(2/\pi<2/3\), giving \(<700\) without floating integration. Thus the permissible signed deviation just obtained is \(<.324\).

But each true signed row on \(T_0\), with its fixed outer contributions \(A_h+v\), requires its internal \(T_0\) contribution to be exactly \(\lambda w\), no matter how the internal kernel is repaired. The average over \(S\) is therefore \(\sigma\lambda w\), at distance
\[
 \sigma(\lambda-1)|w|>1.20
\]
from \(\sigma w\), using only the rigorously coarse \(\lambda>1.033, |w|>.874, \sigma>41.84\). This contradicts the genuine .010 rough window's allowed \(<.324\) deviation. Thus the synchronized .04/.105/.123 outer construction cannot be made compatible with the deeper true sieve simply by altering its \(T_0,T_0\) block. Its initial constant \(\lambda\) plainly fails too, but the signed averaging argument excludes *all* internal repairs under this fixed outer choice. The remainder is not an impossibility proof for other models: the key actual unknown is the **signed outer–tail coupling on the same rows** (or a choice of outer blocks yielding a different required tail moment). This is more specific than checking extra isolated scalar lower or upper terms.

Replay: run [check_cq_multi_rough_pair_extension.js](check_cq_multi_rough_pair_extension.js) with Node.js, reproducing the ordinary \(C\) upper, the directed tight .01 interval, the genuine radical-free parameter comparisons, and the signed needed/allowed gap. It prints required gap >1.2068 and permitted <.322713 with its exact tick interval.
