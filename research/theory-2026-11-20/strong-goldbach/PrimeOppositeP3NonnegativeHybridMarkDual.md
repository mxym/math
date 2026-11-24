# A continuous dual for nonnegative one- and two-prime angular penalties

Written research note, 2026-11-24. Follow-up to the [single-mark dual barrier](PrimeOppositeP3ArbitrarySingleMarkDual.md). This tests an actual switched-affine extension: nonnegative single marks and nonnegative **unordered distinct two-prime marks**, paid by their separate conditional BV and true switched affine caps. It does not constrain signed two-mark lower credits, Buchstab switching or stronger joint distribution estimates.

Use the literal square-root prime source window, \(L=\log N\), \(z=N^\mu\), and \(B=2XS_N/L\) as in the [current P3 target](PrimeOppositeSquareRootP3Target.md). Consider the score
\[
 1-\sum_{q\mid N-p} w(\log q/L)
   -\sum_{\substack{q<r\\ qr\mid N-p}}
                 v(\log q/L,\log r/L),
 \qquad w,v\ge0 .
\]
For a P3 proof excluding rank four by angular size/sum constraints alone, the total penalty must be at least 1 on every admissible distinct rank-four angle tuple, with sum 1 or the corresponding arbitrarily small collars. We do not assert that each formal tuple appears as an actual prime complement. The budget integrals below apply to fixed/step angular mark weights whose finite principal caps can indeed be summed harmonically. Unsupported higher total exponents have no finite cap of these types; hence a weight outside these cap ranges cannot garner a finite guaranteed budget and may be taken zero there.

## Actual cap families

For one prime the earlier exact affine kernel and conditional BV calculations give, in units of the main normalization \(B\), the cap density
\[
   C_1(t)=U_1(t)/t\ge64
\]
globally in the relevant interval \(0<t<1/2\), and \(C_1(t)\ge100\) for \(t\ge.20\). Indeed the BV candidate, when \(t<.25\), is at least \(1/(t(.25-t))\), whose minimum is 64; for \(t\ge.20\) in that range it is at least 100. The affine candidate is at least \(2/(t(.5-t)^2)\), whose global minimum is 108. The first bound uses the initial linear-sieve function and its nonnegative delay increments; the second even allows the unachievable full two-root optimal denominator, hence also the exact weaker asymmetric denominator. These floors apply to the classical one-mark cap families on all of the cutoff range below. For \(\mu\ge.05\), the already established compatible-support obstruction for optimized middle-strip squares permits inclusion of those specific square variants, since they cannot give smaller leading cap than the ordinary affine square. No additional optimized cap is claimed below .05.

For two true distinct marked primes \(q,r\), put \(t=\log q/L,\ u=\log r/L,\ m=t+u\) (here \(m\) denotes the exponent, not the integer modulus). In the BV method, \(qr\mid N-p\) consumes precisely level exponent \(m\), so for \(m<.25\) the conditional upper density relative to harmonic ordered angles is at least \(1/(tu(.25-m))\). In the switched method, the variable \(j=(N-p)/(qr)\) lies in the **actual** affine interval of length \(Y/(qr)\), where \(Y\asymp\sqrt N\) is the source length. The marks are true prime divisors, and the two actual linear forms are \(j\) and \(N-(qr)j\). Prime factors dividing \(qr\) do not create extra roots: on unit target support the second form never vanishes there, and \(q,r\ge z\) are not tested on the rough cofactor side. Treating such local factors as full two-root factors could only improve, not worsen, the optimistic cap density. For polynomial angular marks their direct normalization impact is \(1+o(1)\). The unweighted divisor cutoff from actual affine floors is at most \(N^{(.5-m)/2}\) in exponent units. Consequently the separate affine cap density, including any exact asymmetric denominator for this same switched progression, is at least \(2/(tu(.5-m)^2)\) for \(m<.5\). For \(m\ge.5\) this route supplies no finite usual-scale cap. Omitting \(q,r\mid N\) can only reduce the actual counted populations; their local main factors do not lower the stated normalized floor. The two-prime coefficients are paid once on the sorted domain \(t<u\), with harmonic measure \(dt\,du/(tu)\), not twice.

Thus every supported two-mark cap in this class is at least 1728 globally: \(tu\le m^2/4\) implies the BV floor is at least \(4/(m^2(.25-m))\ge1728\), attained in the optimistic expression at \(m=1/6\); the affine floor is at least \(8/(m^2(.5-m)^2)\ge2048\). A stronger fact near \(m=.5\) is that on \(.49\le m<.5\) the BV route is unavailable and the affine floor is \(\ge 320000\), since \(tu\le1/16\) and \(.5-m\le.01\).

## Positive-measure rank-four dual

Fix \(.0393\le\mu\le.07\). Draw a real \(P\) uniformly in \([.49,.51]\); this auxiliary real variable is not the original prime or target. Conditional on \(P\), independently choose \(U\in[\mu,P-\mu]\), \(V\in[\mu,1-P-\mu]\) with respective densities proportional to
\[
 g_P(x)=64+36\,1_{\{x\ge.20,\ P-x\ge.20\}}, \qquad g_{1-P}(x)
\]
on these intervals. Use the rank-four profile \((U,P-U,V,1-P-V)\), which has sum exactly 1 and almost surely distinct angles. It is exchangeable within each block of two. A shrinking strict collar in total sum changes all estimates continuously and leaves the fixed margin below unchanged.

For any \(P\) in this interval the conditional normalizer obeys
\[
 Z(P)=\int_\mu^{P-\mu} g_P(x)\,dx
       \ge 64(.49-2\mu)+36(.09)
       =Z_*:=34.60-128\mu .
\]
Indeed the enhanced interval \([.20,P-.20]\) is contained and has length at least .09. Each individual angle, conditional or unconditional, has density at most \(C_1(t)/Z_*\): the value 64 is always allowed, and the value 100 occurs only at angles where that stronger cap floor applies. Each conditional individual density is also at most 4, because \(g_P\le100\) and \(Z_*\ge25.64\) throughout the range.

Each of the four cross-block pair marginals has unsorted density at most 16 by conditional independence and then averaging \(P\). Sending the pair coordinates to their increasing order gives a density at most 32 apiece, or 128 collectively. For a within-block pair, the map \((P,U)\mapsto(U,P-U)\) has absolute Jacobian 1, and the uniform \(P\)-density is 50. Its joint density is at most \(50\cdot4=200\) before sorting, 400 after; both within-block pairs give at most 800. Such terms occur only where \(.49\le t+u\le.51\), whether supported by the mark cap or not.

Now scale the probability law by
\[
   \rho_*=\frac{Z_*}{4}=8.65-32\mu.
\]
The sum of its four single-angle marginal densities is at most the actual \(C_1\) selected by the method. The scaled sum of its six pair densities is at most \(128\rho_*<1108\) outside \([.49,.51]\) in the sum coordinate; this is below every supported pair-cap floor. Within that strip it is at most \(928\rho_*<8028\), versus the affine floor 320000 on its supported part \([.49,.5)\). On the remainder of the strip, the assumed nonnegative pair weights are zero if not supported. Thus the scaled marginals are pointwise dominated by the paid densities on the entire weighted domain; there is no use of signed cancellation or conjectured actual factor independence. The conditional independence above is just a construction of a feasible dual measure on formal size profiles.

Integrating the universal rank-four condition against this measure gives a minimum guaranteed *cap payment* of \(\rho_* B\) for any such hybrid weighting. But the standard rough-source linear lower coefficient is at most \(e^{-\gamma}/(2\mu)<.281/\mu\), and
\[
 8.65-32\mu>\frac{.281}{\mu}
       \qquad (.0393\le\mu\le.07).
\]
At the left endpoint it is the rational comparison \(7.3924>.281/.0393\); the difference is increasing since \(.281/\mu^2-32>0\) through .07. Thus no positive \(P_3\) budget is possible against these cap families solely by nonnegative two-mark linear penalty optimization. In particular the conclusion survives the new tighter P4 rough cutoff .0393 when only the classical one- and two-mark cap envelopes are used.

On the same dual profiles every angle is at most \(.51-\mu<.5\), so the sum of any **three** angles is \(>.5\). This means additional nonnegative triple-or-higher marks supported only at total exponent \(<.5\) do not affect the witness; it also excludes that extension with otherwise the same cap charges. This does not cover a genuinely different upper for large products, or any lower credit on unsupported/angular subsets.

Scope: all these are obstructions to a specified positive proof budget, not lower bounds on true marked counts. Signed two-prime credits, conditioning on true joint geometry beyond the above rank-four simplex, oscillatory remainders paid jointly rather than pointwise, or Buchstab switching are not covered.