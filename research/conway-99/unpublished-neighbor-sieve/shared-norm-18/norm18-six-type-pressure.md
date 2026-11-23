# The same collision count on a six-type rank-38 family

Suppose the selected unit support is contained in
`{018,024,125,226,228,337}` at rank 38. Let A,B,C be the positive-charge graph counts of the unit types 125,228,337, respectively. Then
```
  84 N18 + 200 A − 1004 B + 58 C ≥ 2,028,936.
```
In particular the support **cannot be contained in {018,024,226,228}**, even with arbitrarily many (2,28) labels.

The graph proof of [the collision closure](rank38-norm18-triple-closure.md) still gives 6(9N18−110880)≤11N22+8s, with the same s=344·E S_H. Here the six absent unit types are exactly 016,020,026,121,127,230. The 3-field seed and its all-seven classification require only no N16,N20,U127,U230. The sign independence of N22 uses U230; the m=2 exclusion does not use U125,U228,U337. In the m≤1 list the apparent cost-25 possibility for a unit (1,25) would require squared distance 20 between neutral N18 sources and is already excluded by N20 absence, independently of the existence of (1,25) elsewhere. The (1,23)-associated cross decompositions only use the absent raw neutral fields of norms 16,20,26; cost 26 is absent because U026 and U121 are. Thus letting A,B,C vary does not alter any collision or residue cap. In particular even if the lower bound for T becomes nonpositive the graph inequality remains true.

The [exact native span check](norm18_six_type_pressure.py) with all three additional columns retained gives the fixed-H row:
```
  4W022 = 12V018−420−14W014−2W335−S +2V125−5V228+V337.
```
The [earlier full norm-18 row](norm18-u226-graph-cap.md) on this same support is
```
  48V018+12V226−2V125−19V228−3V337
     =2058+98W014+11S+10W444.
```
Each of the added raw types has nonzero discriminant norm, so the same factor 344 converts the mean *unit* count to its graph-wide count. Dropping only nonnegative terms yields
```
  4N22 ≤ 12N18−144480−s +2A−5B+C,
  11s ≤ 48N18−658056−2A−19B−3C
```
using graph-wide G226≤4158, as before. Substitute the first inequality in the graph bound, then substitute the second for 11s. This gives exactly the inequality claimed above. As N18≤16,166, setting A=C=0 gives 84·16,166−1004B<2,028,936. Equivalently every rank-38 support within these six must satisfy 200A+58C≥670,992+1004B (with both sides counting the stated graph labels and N18 still oriented). No entire rank is claimed.
