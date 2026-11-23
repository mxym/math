# Simultaneous true norm-22 and charge-three mass forced by double differences

This uses only the rank-42 norm-18/norm-24 two-type face. In the four surviving tuples let n=50,51,52,53 respectively denote the number of actual norm-18 vectors in **each signed** residue class on the norm-four circle, and S=2,5,8,11 the number of extra unit (1,23) marks. The circle consists of four antipodal pairs of signed classes. Let L=N22/2 count actual unoriented norm-22 fields; let D count double norm-28 lines in the [Johnson graph](norm22-johnson-double-graph.md). The analytic bridge, independently replayable via the [scalar-bridge script](two-type-scalar-bridge.py) against the true-Hoffman chart, is
```
L=4W022,   N28=−1386+90n+8W022,
4W022+2W335=172+3S,   3W022−3W333=19+S.
```
Here N28 counts **oriented** original-zero norm-28 fields, W335/W333 are nonnegative eligible populations normalized by eight, and 8W333 is the number of actual (3,33) fields (charge +3, not its negatives). In particular the upper bounds for N28 are 3470,3578,3686,3794. No additional integrality of an orbit average is assumed.

In one signed norm-18 class, let e count unordered distinct pairs with inner product 4. All other distinct pairs have product −3. The integral centroid has nonnegative squared length
```
18n+8e−6(C(n,2)−e) = 14e−3n(n−7).
```
Select one signed class per antipodal pair. Together these four selections contribute at least E=4 ceil(3n(n−7)/14) close pairs. Each such pair produces the unoriented original-zero difference of norm 28. Each norm-28 line gets at most two preimages. In fact a norm-28 source decomposition in a chosen residue direction gives one unordered pair of actual fields in the selected signed class, regardless of which orientation of the difference is chosen; the other origination direction, if present, gives a second. Therefore D≥E−N28/2, namely D≥109,135,165,195. Substituting the first bridge row retains the shared variable and gives D+L≥K, where K=287,322,361,400 respectively.

Let h_j count vertices (i.e. actual norm-22 **lines**) of decomposition multiplicity j. The Johnson graph is simple with degree C(j,2), j≤6, and its site budget is 4h_5+6h_6≤12S. Hence
```
2D = Σ_j C(j,2)h_j ≤ 6L+4h_5+9h_6 ≤ 6L+18S.
```
Thus 4L+9S≥K. Rounding L up to the next integer yields, in tuple order:
```
                         S=2   S=5   S=8   S=11
L=N22/2                  ≥68   ≥70   ≥73   ≥76
N22                     ≥136  ≥140  ≥146  ≥152
G(3,33)=8W333            ≥80   ≥76   ≥74   ≥72
```
The last line is the exact conversion 8W333=2L−8(19+S)/3. In particular every surviving tuple requires actual (3,33) labels. These are conditional necessities on the face, not an exclusion of the face.

Run `python3 two-type-scalar-bridge.py` alongside `two_type_true_hoffman.py`, with the latter's dependencies, to check the exact scalar rows. The population bound above additionally uses the displayed graph-side centroid and exceptional-site argument.
