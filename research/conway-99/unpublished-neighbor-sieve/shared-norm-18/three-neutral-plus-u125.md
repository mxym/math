# The large-Hoffman exclusion also permits U125

Both rank 40 and rank 42 exclude support contained in {020,024,026,125}. This strengthens the [three-neutral large-Hoffman exclusion](three-neutral-hoffman.md) by allowing an arbitrary population of unit charge-one cost-25 markings. It is not a whole-rank conclusion.

The native 78-original-coclique lower of [the large-family theorem](hoffman-fano-large-family.md) did not assume 125 absent (at rank 40 its relevant zero set is 018,127,228,230,337; at rank 42 it is 016,018,228,230,337). Thus each maximal extension has at least 78 eligible cocliques on the enlarged face. In the fixed-extension angular certificate, neutral 016 remains absent, so the raw 125 count equals its unit count, but is no longer suppressed. The source 123-to-339 incidence argument had no condition on type 125 or the total Fano count, so remains unchanged.

In the [replay](three_neutral_plus_u125.py) the precise same thirteen harmonic rows, signed coefficients and single-coclique normalization now give equality (2) of the three-neutral theorem with exactly these three additional terms on its right:
```
630 K125[−3] + 660 K125[4] + 690 K125[11].
```
All are nonnegative. Hence the same contradiction to the literal graph-incidence inequality applies. The verifier needs only the Python standard library.

The [five-way hitting theorem](high-rank-five-hit.md) further strengthens this result by simultaneously allowing both type 121 and type 226.
