# A rooted overlap forced on the rank-38 {018,024,226} support

Assume Seidel rank 38 and all selected unit families outside {neutral 18, neutral 24, charge 2 cost 26} vanish. The number G226 of actual positive-charge cost-26 fields is then **at least 726**. By the [positive-pair and midpoint theorem](u226-pair-midpoint.md), these are exactly two per marked square, and no diagonal is repeated. Thus there are at least 363 distinct induced squares of this specified kind. Their 1452 or more edge incidences exceed twice the 693 graph edges, so some actual edge belongs to at least **three** marked squares. The conclusion is necessary on this support, not a contradiction.

Use the existing [rank-38 original-to-maximal Fourier chart](rank38-three-hit-sets.md), with p=344 and V226=G226/344. Write n=W018, Z=W028, V=8W024, L=4W022, S=W123−99−7W014. The [signed-centroid tangent](nearface-four-exclusion.md) applies in each maximal extension: its geometric inequalities use the absence of neutral 16, neutral 20 and raw (1,25), and the last absence follows from the unit (1,25) and neutral 16 vanishings. The tangent is linear so its forms can then be averaged. In particular the following linear combination is nonnegative at j=47:
```
T=84n+7Z+21L+525S/2+3675W014/4+(99/20)V − (3531/200)(2jn−j²).
```
Indeed the positive quadratic coefficient 12+4√2 is greater than 3531/200 and 7√2/2 is less than 99/20. In the native rank-38 chart with the specified absent unit columns, the [exact checker](u226_rank38_forcing.py) verifies
```
V226−31968538/(344·44055)
 = (12323/8811) W014 + (9917/26433) W222 + (608/26433) W335
   + (13811/15154920)(16166−344n) + (20/26433) T .
```
The norm18 cap 16166 in the penultimate term is the earlier graph-wide conditional no-16/no-20 bound encoded in that chart. Every term is nonnegative and 31968538/44055>725. This concerns the same true G226 counted by the graph-side upper 4158; the two numerical bounds themselves are compatible.
