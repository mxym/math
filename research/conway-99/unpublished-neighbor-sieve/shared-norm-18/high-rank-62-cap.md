# A rank-independent cap of 61 Hoffman cocliques in each maximal seven-extension on the prescribed face

The [previous incidence theorem](three-neutral-hoffman.md) is literal for any one maximal determinant-49 extension H, at any of the admissible mod-seven Seidel ranks. Here no original-coclique floor, or indeed any original coclique at all, is assumed. Suppose the full (not merely unit) populations 016,018,228,230,337 vanish. We do not set raw 026,121,125,127 or 226 to zero. Write U for the normalized eligible count of **unit** charge-one cost-27 fields in H, so W127−2W226=U by the ordinary nonunit subtraction and absence of 018. For M=W222>0 take the mean over its M eligible actual 22-cocliques. Then
```
(62−M)(mean K123[−3]−22) + 166 U ≥ 1190.
```
In particular, if U=0 then M≤61. This includes M=0 trivially and does not imply every H has a coclique. Alternatively if M≥62, then 166 U≥1190, requiring at least 58 actual eligible unit (1,27) fields because the nonisotropic fold is divided by eight.

**Proof.** The same angular transport normalization as in the [five-family gate](high-rank-five-hit.md) is used. No coefficient on raw 026 or 125 is constrained. The [standalone standard-library replay](high_rank_62_cap.py) uses the same harmonic quadratics at squared norms 2 and 4 in the four determinant-49 gluings. At each fixed eligible C it verifies the precise equality
```
62 K123[−3]−4 W339+88 M−7 W014−1630 = P−166 U,
P = 30 K444[16]+80 K444[9]+48 K333[12]+62 K333[5]
    +54 K335[12]+40 K335[5]+200 K226[8]+12 K232[8]+24 K232[1]
    +78 K121[4]+62 K123[11]+62 K125[11]+72 K125[4]+82 K125[−3]
    +112 K127[11]+150 K127[4]+188 K127[−3]+98 K014[7]+49 K014[0].
```
All nineteen terms are nonnegative. The only full marginal used beyond the 13 harmonic rows is W127−2W226=U; no individual slot is equated in that subtraction. The actual incidence bound is M(mean K123[−3]−22)≤4(W339−231−22M)+7W014, and each K123[−3]≥22. Combining it with the equality yields the displayed inequality, in fact with 1190+mean P on the right.
