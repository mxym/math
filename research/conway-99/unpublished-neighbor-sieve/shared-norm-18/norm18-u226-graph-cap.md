# Combining the two graph-population bounds at rank 38

The following second identity is also valid on the **full** folded unit dictionary of each maximal determinant-49 extension, with S=W123−99−7W014:
```
48V018 +12V226 −70V016 +33V020 +3V026 +81V121 −2V125 +8V127
       −19V228 +10V230 −3V337
 =2058+98W014+11S+10W444 .
```
As in [the first lower-bound identity](norm18-u226-lower.md), V024 does not occur. The [native exact checker](norm18_u226_graph_cap.py) reduces the complete displayed target against the higher harmonic rows, before any support hypothesis.

Suppose now that the rank is 38 and the twelve selected unit types are confined to (0,18),(0,24),(2,26). In each H,
`48V018+12V226=2058+98W014+11S+10W444≥2058`. Averaging gives `48N18+12G226≥2058·344`; both counts are graph-wide and N18 is oriented. Here U127 is absent, so every G226 has c=0, and [positive-diagonal uniqueness](norm16-height-two-edge.md) bounds them by 4,158 unordered nonedges *globally*, not in a normalized fold. Thus
```
 N18 ≥ (2058·344−12·4158)/48 = 27419/2 .
```
The count is an even integer; [the no-norm-16/20 packing](panel-heights.md) gives the upper bound. Consequently **13,710 ≤ N18 ≤ 16,166** on this rank-38 support. This sharpens 12,040, does not compare N18 to another count, and does not eliminate the support or the rank.

The [rooted-triple theorem](rooted-norm18-triples.md) feeds actual (4,44) fields back into this row and raises the lower bound to 13,772.
