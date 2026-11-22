# The antichain envelope on the same high four-tag exterior

Keep the original native sextic score, all true factor cutoffs, and
the literal high-arm exterior of the [high four-tag proof](Proof.md).
As before, neither arm lies in the separately charged rank 5–7
four-tag cohort. The signed sum on this unchanged physical support is
\[
                              >-.088M+o(M).
\]
This replaces the debit .124 in the [half-envelope proof](HalfEnvelope.md);
it does not change any included row or add a second credit.

## A bound for alternating endpoint shifts

Let \(k\ge2\) be even and differentiate \(k\) centered uniform
densities, of widths \(v_1,\ldots,v_k>0\), in the convolution
formula. The resulting derivative is an alternating sum of translates
of the remaining density \(g\), divided by \(\prod_i v_i\). The
translation parameters are the subset sums of the widths, up to a
common translation and a possible common sign. The remaining density
is nonnegative and symmetric unimodal: centered interval densities
are symmetric unimodal and convolution preserves that property.

For any threshold \(s\), pair the subsets using a smallest width
\(v_1\). In the alternating sum over subsets of total width
\(\le s\), all paired terms cancel except for subsets of
\(\{2,\ldots,k\}\) with sums in \((s-v_1,s]\).
The surviving subsets form an antichain, since a strict inclusion
adds at least \(v_1\), whereas two sums in the half-open strip differ
by less than \(v_1\). The strict-threshold version uses
\([s-v_1,s)\) and has the same bound. Coincident sums therefore do
not create an exception. By [Sperner's theorem](https://doi.org/10.1007/BF01171114)
the magnitude of each threshold sum is at most
\(\binom{k-1}{\lfloor(k-1)/2\rfloor}\).
Write the indicator of an interval as the difference of two threshold
indicators, choosing the endpoints according to which are included.
Since the superlevel sets of \(g\) are intervals, integrate this
interval estimate over the levels of \(g\). The derivative is bounded
in absolute value by
\[
  2\binom{k-1}{\lfloor(k-1)/2\rfloor}
       \frac{\|g\|_\infty}{\prod_i v_i}.
\]
The original half-envelope has coefficient \(2^{k-1}\) instead of
the coefficient above. The resulting factor for even \(k\) is
\(f_k=2\binom{k}{k/2}/2^k\).

## Applying the bound on the real high-arm exterior

The two orders here are \(k=r-5,r-7\), even and at least two
since \(r\ge9\) is odd. Use the same supremum bound by the inverse
of the longest undifferentiated box and the same actual first four
or six factors. In the high four-tag proof's common envelope after
the first four factors, the ratio of the second half-envelope term
to the first is at most
\[
    R_r=\frac{80640}{4\cdot1056(r-4)^2},
\]
since the remaining total \(T\) is at most one. As \(f_{r-7}\ge
f_{r-5}\), the pointwise majorant may be scaled by
\((f_{r-5}+R_r f_{r-7})/(1+R_r)\). These factors decrease through
odd ranks: both \(f\)'s decrease (the ratio for consecutive even
orders is \((k+1)/(k+2)\)), and the larger of them has a decreasing
relative weight. Safe factors for the original groups
\(9,11,13,15,\ge17\) are respectively .859, .661, .563, .501, .456.

Scale both the ordinary mass and genuine receiver coefficient of
each group of the half-envelope proof by its factor. The actual
product distribution, least-factor labels, and both overlap
subtractions remain unchanged. The direct and Cauchy mixed terms
have degree one in this scaling on each group; the high self-pair
bounds have degree one in each of their two group factors. The
old-low overlap is linear in the scaled high masses.

The [rational replay](check_antichain_envelope.py) verifies the
factors and the unchanged ledger with outward square roots, giving
a debit \(<.087136M+o(M)<.088M+o(M)\). There is still no conclusion
on the remaining signed exterior or on Goldbach.
