# Three more original-site exclusions when all Fano lines are orthogonal

Retain the exact 205-variable [original-site chart](original-site-populations.md) and its notation. The following are additional impossible positive-unit supports, with an entry encoding (charge,cost) by 100a+t. No graph automorphism or rank exclusion is asserted.

| Seidel rank over F7 | allowed support | Fano constraints (angles 1,2,4 respectively) |
|---|---|---|
| 36 | 20,26,125,228 | N24=0; N24=0; G230=0 |
| 38 | 20,24,26 | U125=G121=0; U127=N18=0; G230=0 |
| 38 | 26,125,230 | N24=0; N24=0; N20=0 |

Indeed write m_j for the number of unordered pairs of distinct unoriented norm-14 Fano lines with absolute dot j. For j>0 the only possibilities are 1,2,4. At angle one the [endpoint intersection argument](rank36-four-endpoint-cut.md) gives 2m1≤N24; alternatively m1≤7U125+4G121. At angle two the short difference gives 2m2≤N24; alternatively 2m2≤8U127+45N18. At angle four, 2m4≤N20 and m4≤3G230. These arguments are about actual labels of the graph, and do not depend on its Seidel rank; see the [palette transfers](rank36-four-fano-palette-cut.md) and [difference packing](fano-difference-packing.md). The types at 20,24,121,230 in these implications are unit automatically; the counts U125 and U127 are expressly unit, not raw. Reading the table from left to right shows that each m_j is zero. All distinct Fano lines are therefore orthogonal. Since [three pairwise orthogonal Fano configurations cannot coexist](../README.md#three-orthogonal-fano-configurations-cannot-coexist), at most two lines are present: **N14≤4**, counting both orientations. This is a bound on the global N14, not on its extension mean.

The individual duals use the displayed cap and site-specific edge/path labels from the preceding chart. The rank-36 witness also uses the original neutral nonedge mark: an ordered nonedge (i,j) yields d_i−d_j with twelve +1 sites, twelve −1 sites, one each of +3 and −3, and 73 zeros. Its exceptional sites recover the pair, so the 8316 ordered nonedges supply the row 99 C_(0,42,1)≥12·8316. The middle witness also uses the original-zero-class coclique tangent at 64, namely
```
9Y2 + 18Y1 − (369+640) M0 +5·64²−4158 ≥ 0,
```
where Y1,Y2 are the true unweighted norm-2 and norm-4 original coefficients, and M0 is the original-compatible coclique count. This is the published [original-coclique variance tangent](rank36-four-hit-sets.md), with no assumption on M0. It is valid at either rank.

The standalone addendum [checker](original_site_fano_four.py) imports the existing harmonic basis and site-orbit routines and reconstructs the common original-site equations. It then verifies the exact [three duals](original-site-fano-four-duals.json), including the prerequisites in each line of the table; 12, 11, 11 strictly positive terms certify the cases in order. Run `python3 original_site_fano_four.py` beside the preceding checker. Neither earlier checker nor any other data file is modified.
