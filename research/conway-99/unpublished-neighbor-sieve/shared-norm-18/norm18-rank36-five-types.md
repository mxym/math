# Rank 36 requires at least five selected unit types

At rank 36 no selected support is contained in **{018,020,024,026,121,226}**. This removes the last previously surviving exact-four support, {018,020,024,026}. Every rank-36 candidate must therefore use at least five of the twelve selected unit shell types. In particular it cannot use neutral types only: the remaining neutral possibility N16 itself forces U127>0. This does not exclude mod-seven rank 36.

Assume the other six selected types (016,125,127,228,230,337) vanish. The [exact certificate](norm18_rank36_five_types.py) gives
```
2,322,466,100,694 N18 ≥ 72,271,791,541,192,488,
N18 ≥ 31,120 by antipodality.
```
Here N18 is exactly the actual oriented neutral eigenfield population, 2402 times the native W018 coordinate at rank 36. In addition to the six specified vanishing unit types, the only signed zero used is the established rank-36 Fano exclusion. U121 and U226 occur with positive coefficients on the nonnegative side, not among the absences.

All the inequalities are native nonnegative unit populations, angular atoms or mandatory graph marks except the original-coclique Sidon tangent already present as ('Ct',34) in [the original scalar sieve](rank36_four_hit_sets.py), following the [coclique tangent argument](rank36-coclique-tangent.md) applied to true original-class labels. With original coefficients Y1=C014, Y2=C028+2C339 and original coclique population M0=C222, that exact tangent is 9Y2+18Y1−709M0+1622≥0. The native checker uses its explicit 205-column pullback and verifies the entire weighted identity exactly.

On the other hand, N16=U127=0 implies **N18≤29,842** by the [literal label-edge seed bound](norm18-label-edge-cap.md). The bounds are on the same global, oriented count. The exclusions accumulated before this result had left just {018,020,024,026} at exact size four, already in the forbidden six-type family. Larger supports have not all been tested or eliminated.
  
The five-type conclusion counts only these twelve selected unit types, not all raw shells. In particular unit 026 is not the whole norm-26 shell, and the proof does not claim a rank-36 example with five types.
