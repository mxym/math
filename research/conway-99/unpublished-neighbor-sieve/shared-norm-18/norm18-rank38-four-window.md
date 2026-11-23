# A dense genuine rank-38 neighbor for positive (2,30)

Suppose the mod-seven Seidel rank is 38 and the twelve selected unit types present are contained in `{018,024,226,230}`. Unlike [the excluded adjacent family](rank38-norm18-triple-closure.md), positive (2,30) labels are allowed. Then
```
11,576 ≤ N18 ≤ 12,320,    2,910 ≤ G226 ≤ 4,158,    U230 ≤ 13,130.
```
These are literal graph counts: N18 counts both signs, G226=U226 and U230 count the indicated positive charge only. This is a **necessary window, not a branch exclusion**.

In [the rank-38 native chart](rank38_three_hit_sets.py), p=344 converts each of the three corresponding averaged anisotropic unit counts V to its graph count. Write W for averaged raw entries and S for the ordinary-excess charge-one entry of that native chart. All are nonnegative. Let K=110880−9 N18, nonnegative by [triangle-freeness at each seed](norm18-triple-remaining-bridges.md), since N16=N20=0. With just the eight forbidden unit rows removed, three exact identities are
```
15 N18−173634 =7052 W014+172 W222+1548 W333+774 W335+774 W444+688 S,
27 G226−78552=16512 W014+5160 W222+2064 S+2 K,
27(39392/3−U230)=13416 W014+8256 W222+18576 W333+9288 W335+516 S+8 K.
```
The [exact checker](norm18_rank38_four_window.py) reduces each equation in the native row basis with rational arithmetic and no optimization. Use nonnegativity and take integer endpoints. The previously proved [positive-pair bound](u226-pair-midpoint.md) applies since unit (1,27) is absent; it bounds G226 by 4,158.

The same positive-pair theorem gives at most one (2,26) field for each positive nonedge, a c=0 square whose opposite diagonal is also positive for its paired distinct field. Consequently at least 1,455 distinct literal squares are active. At least one graph edge lies on nine of them: otherwise the four incidences per square give at most 8·693=5,544, short of 4·1,455=5,820. Some graph site also belongs to at least 59 distinct positive nonedges: 2·2,910>58·99. In particular the nine-square conclusion concerns the actual two-wing matching constraints in [the full root row](u226-full-root-row.md), not abstract four-cycles.
