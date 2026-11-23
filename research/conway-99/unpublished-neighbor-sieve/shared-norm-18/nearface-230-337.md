# Allowing the additional unit shell (3,37)

The [signed and unsigned source argument](nearface-230-exclusion.md) in fact rules out the four-type support **{018,024,230,337}** in even a single fixed maximal determinant-49 extension. All its graph-side uses of shell absence remain valid: allowing unit charge-three fields of cost 37 does not reintroduce N16, N20, G228 or G125, a Fano field, or a charge-one cost27 field with two positive doubles. The last fact can be seen without any shell support assumption: subtracting the mark at one positive double would leave a neutral norm18 field with another positive double, impossible. Norm18 resultant orientations and positive-P3/exterior slot counts are unchanged.

For exact details see [the native companion](nearface_230_337.py), which tests the enlarged row span, *without* inserting F=0 as a row. Write h=W337≥0. The earlier Fano-bound nonnegative combination has the identity
```
100443F + 1100 W129 + 41860 M + 1800 W335 + 886 S + 12 T54 + 4768 h = 170208.
```
Here `T54=35Z+(420−176·54)n+25V+105L+(2625/2)S+(18375/4)F+88·54²` is the nonnegative [strengthened signed-centroid tangent](nearface-230-hoffman.md), and all terms on the left are nonnegative. Since F is an even actual count, it must vanish. In the five scalar equations at the end of the preceding proof, the respective right sides now gain h, 88h/3, 14h/3, −24h and 5h/6, with all other terms unchanged (the fourth is the equation for A). The elimination of u and the unfavorable variance still works word for word; the forbidden polynomial simply gains
```
h (30078970 M + 12031588 S + 3007897 h + 537965019).
```
It is therefore strictly positive for all M,S,h≥0. The companion verifies this degree-two identity at the fifteen simplex interpolation points over the rationals and checks the strict discriminant bound. The assertion is support containment, so does not require that any of the four types occur. It does not exclude any full Seidel rank.

Combined with the earlier common filters, the necessary support counts by size zero through twelve are `0,0,0,15,113,333,537,545,371,175,56,11,1`. These count allowed supports, not realized graphs. Run `python3 nearface_230_337.py` beside the existing common harmonic verifier and its dependencies for the exact row, polynomial and support-count checks.
