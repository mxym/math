# No high Hoffman edges in the last rank-42 cost-21 aggregate

On the [sole rank-42 cost-21 aggregate](cost21-four-coclique-walk.md), call a Hoffman coclique high when it meets each of the eight equitable 44-sets in 16 vertices. The [parallel-overlap result](cost21-eight-parallel-44.md) makes this a condition on any one of the eight sets. Call a pair of high cocliques meeting at one vertex a high edge. There is **at most one** such edge. If it exists, the actual equitable sets supply a norm-18 difference. The final cost-35 argument rules out that last edge as well. The zero-high-edge aggregate is not excluded by this note.

## Two high edges are impossible

Use the same letter for a set and its indicator, and let \(d_s=(3I-A)e_s\). For a high edge \(C,D\) through \(s\), the [cost-21 transport](cost21-eight-signed-44.md) gives the unit charged field
\[
 u_X=d_s-C-D+X
\]
for every equitable 44-set \(X\). For a second high edge \(F,H\) through \(t\), define \(v_X=d_t-F-H+X\). The same transport's high matching result gives four cross-coclique intersections all of size eight, and \(s\notin F\cup H,\ t\notin C\cup D\): each high coclique other than \(C,D\) meets them both in eight and omits \(s\), and conversely. In particular \(s\ne t\).

Write \(b=u_X-v_X\), independent of \(X\). The vector \(C+D-F-H\) has squared norm \(4(22)+2(1+1-4(8))=28\). Also \(d_s\cdot C=7[\,s\in C\,]-4\) for a Hoffman coclique, hence \((d_s-d_t)\cdot(C+D-F-H)=28\). Since \(d_s^2=23\) and \(d_s\cdot d_t=2-7A_{st}\), we obtain \(b^2=14+14A_{st}\). The actual neutral norm-14 shell is empty, so \(b^2=28\). The equality \(\|v_X+b\|^2=\|v_X\|^2=21\) for every \(X\) then gives \(b\perp X-Y\) for every \(X,Y\). Thus
\[
 \|u_X-v_Y\|^2=28+\|X-Y\|^2.
\]
On the other hand, the two unit cost-21 fields have inner product at least \(-10\), because any opposite-sign overlaps use at most five positive sites from each field. The displayed squared norm is at most 62.

Choose \(X,Y\) with perpendicular signed seven-residues; such pairs exist since the eight distinct residues exhaust the norm-five circle in the terminal anisotropic plane. Their centered norms \(220/9\) are congruent to five modulo seven, so \(k=\|X-Y\|^2/2\equiv5\pmod7\). The neutral minimum rules out \(k=5\), and absence of the norm-24 unit shell rules out \(k=12\) because a difference of indicators is unit. Thus \(k\ge19\), contradicting \(28+2k\le62\).

## A single high edge forces a norm-18 difference

For a high edge \(C,D\) through \(s\), every \(X\) omits \(s\). Its occupancy is 16 on each of the two 21-site coclique shores \(C-\{s\}\), \(D-\{s\}\), eight on the 14 neighbors of \(s\) by the 44-set equitable equation, and four on the remaining 42 sites. Consequently two \(X,Y\) share at least \(11+11+2=24\) sites, giving \(k\le20\).

In the norm-five circle over \(\mathbf F_7\), an orthogonal coordinate choice with Gram \(I_2\) represents the residues by \((\pm1,\pm2),(\pm2,\pm1)\). For two signed classes \(\beta,\gamma\) we have \(k\equiv5-\beta\cdot\gamma\bmod7\). Counting the unordered pairs in this list and using the neutral minimum and absent unit types gives:

| Pairing modulo seven | Number of pairs | Possible half-distances \(k\) |
|---:|---:|---:|
| 0 | 8 | 19 |
| 2 | 4 | 17 |
| 3 | 8 | 9 or 16 |
| 4 | 8 | 15 |

For each 21-site shore the eight missing five-sets give 40 incidences, so their total pair intersections are at least 19 by integer convexity. The sum of the 28 half-distances on that shore is at most \(28\cdot5-19=121\). The same calculation on the 14-site shore's missing six-sets gives at least \(6\binom42+8\binom32=60\) intersections and hence half-distance sum at most 108. The final shore's eight four-sets give at most \(28\cdot4=112\) in half-distance. Together the sum is at most 462. If all eight ambiguous half-distances were 16, the table would instead give 468. Therefore at least one is 9, yielding a true neutral norm-18 field in both orientations, on a support avoiding \(s\).


## The single-edge case is also impossible

The preceding distance table gives an even shorter obstruction once the exact mass \(G_{3,35}=0\) on this aggregate is imposed. If there is one high edge through \(s\), choose perpendicular equitable sets \(X,Y\). They have half-distance 19, so \(|X\cap Y|=25\). Since \(s\notin Y\), its eight neighbors in \(Y\) give \(d_s\cdot Y=-8\). The transported field therefore has
\[
 (-Y)\cdot u_X = 8+16+16-|X\cap Y|=15.
\]
The field \((-Y)-u_X\) has charge three and squared norm \(44+21-2\cdot15=35\), contradiction by the [exact aggregate mass](cost21-eight-signed-44.md). Thus there are in fact **no high edges** on this aggregate. This does not exclude a nonempty independent family of high cocliques or the aggregate itself.
