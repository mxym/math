# A third rank-36 exclusion uses graph-wide, not just compatible, cocliques

At Seidel rank 36, unit types {(0,26),(1,25),(2,30)} cannot contain all present types among the twelve selected unit types. Use argument C of [the exact checker](rank36_primal_sidon.py). The shared [primal and extension dictionary](rank36-primal-local-cuts.md) is unchanged, including the distinct quantities X14, Y2 and the mean determinant-49 norm-four count.

Let m be the number of **all** actual 22-cocliques, m0 the number with zero original seven-class and M=W222 their mean count in a maximal H. Then m=pM−(p−1)m0 by the isotropic inclusion probability, with p=2402. The original lattice L receives every charge-zero difference and (3,39) translate used by the [variance proof](rank36-coclique-tangent.md) when the source cocliques both have zero original seven-class. It receives the ordinary 462 triangle marks too. Dropping the optional unit (1,23) source, that construction gives the nonnegative slack
```
Z_34=9[Y2+2Y1−462−41m0]−5(68m0−34²).
```
This does not apply the determinant-49 scalar formula directly to L; only the original Y_j are used here.

For 0≤k≤15 let B_k count ordered pairs of distinct cocliques in the **whole graph** with intersection k. The [global Sidon theorem](global-coclique-sidon.md) gives B_k≤2G(4,44+2k) and B_k≤N_(44−2k) simultaneously. Split at k=4. For k≤4 use 2G(4,44+2k)≤2pW_(4,44+2k). For nonzero seven-norm this is equality of the raw folded conversion, and for isotropic norm it is an upper bound since m=pM−(p−1)m0-type correction subtracts a nonnegative zero-class count. All these W are **raw** charge-four counts and may include −2 entries in the target.

For k≥5 put j=22−k, so 7≤j≤17. Define an upper bound U_j for N_(2j) by starting with X_j. If 7 does not divide j and the (3,2j+11) type is represented in the enumerated list, subtract 2pW_(3,2j+11) by the exact ±3 scalar decomposition. Without such a type no subtraction is required. At j=14 use instead X14−462−44m: the 231 genuine positive triangle marks and the 22 distinct charge-three fields per coclique furnish G(3,39)≥231+22m in the **whole graph**, irrespective of class. This is the [unique +2 injection](rank36-coclique-tangent.md); no difference images are subtracted a second time.

Consequently
```
B = 2p sum_{k=0}^{4} W_(4,44+2k) + sum_{j=7}^{17} U_j >= m(m−1).
T_15000 = B−29999m+15000² >= 0.
```
The second line is (m−15000)²≥0 applied to the first. The external threshold is only an integer specifying a valid tangent for all m, not an assumption that m is this large, nor a coclique search.

Take the six nonnegative slacks W333,W335,W444,Y1,990−N14,Y3−41058 as in the [two companion cuts](rank36-primal-local-cuts.md). Append Z_34 and T_15000 in that order. Their respective positive integer weights are
```
2556429271106, 1612023573249, 1281804597497, 2590642804582,
80688058247, 1450423520, 3678795393, 36159.
```
The resulting sum equals **−27971135327947**: the checker reconstructs the full higher-moment row system with the exact rank-36 primal/extension match and the specified unit zeros, then verifies rank 48 remains 48 on appending this claimed equality. Thus the eight nonnegative quantities cannot coexist on this face. This is not an assertion that a formal scalar or local positive profile is a graph.
