# Size 136 excluded in F_17^3

**Theorem.** There is no spectral set of size136 in F_17^3. This does not address the smaller remaining candidate cardinalities.

Use [FugledeF17Size136MomentNine.md](FugledeF17Size136MomentNine.md) for line cap6, affine plane cap17, the fact that every projective line meets each uniform-normal set at least six times, and the planar certificate that an eight-site cap-six planar set with at most seven directions always has two arms of length at least four. The same note verifies that a cap-six planar set with at most nine directions has at most ten sites.

## Moment degree ten by two rounds of factor-plane cap reduction

The additional exact planar verifier [verify-fuglede-f17-size136-degree-ten-caps.js](verify-fuglede-f17-size136-degree-ten-caps.js) establishes:
- A planar set with at most ten directions and affine line cap6 has at most fourteen sites.
- A planar set with at most ten directions and affine line cap4 has at most twelve sites.

The certifier uses a marked noncollinear triangle normalized to 0,e1,e2, all direction masks of size ten containing its three slopes, and all increasing extensions of the triangle within the allowed slopes and line cap. The six affine symmetries permuting this marked triangle act on masks; only the lexicographically least mask in each such orbit is retained without changing coverage. A branch with fewer remaining candidates than required is pruned. There are 1090 retained masks. The target15 with cap6 and target13 with cap4 searches visit 876878 and 1350260 states, respectively, with no completions.

Suppose a nonzero homogeneous form F of degree ten vanishes on U_B. Let B' be the partner. For any direction e of a secant of B', e∈U_B. Let k be the number of distinct rational factor lines of F through e in the projective normal coordinates of B. On a nonfactor radial line through e there are at most 1+10−k sites of U_B: away from e the k radial factors do not vanish, and only the residual form can supply zeros. Thus k≤5, since U_B is six-blocking. If k=0 the tighter nonfactor upper bound is ten. The affine planes through a B' line of direction e have these radial lines as their direction planes. Their occupancies are consequently constrained by the exact planar direction caps, because the difference directions of B' belong to U_B.

If B' has a line with at least five sites, the pencil through it has total occupancy at least136+5·17=221. But at least six of its normals are uniform for B' itself, with occupancy eight. For k=0 or1 nonfactor radial lines have at most ten U_B sites; since B' has line cap6, the corresponding plane cap is fourteen. At most k factor planes can have occupancy seventeen, so the pencil total is at most 6·8+12·14=216 when k=0 and 17+6·8+11·14=219 when k=1 (assigning the six uniform counts to nonfactor planes maximizes this upper bound). When k≥2 nonfactor radial lines have at most nine U_B sites, giving plane cap ten as already verified. Therefore the pencil total is at most 17k+6·8+(12−k)10=168+7k≤203. These all contradict 221. Thus in the presence of F, B' has line cap4.

Now suppose B' has a four-point line. Its pencil must sum to 136+4·17=204. For k=0 or1 the tighter planar cap at ten directions and line cap4 is twelve, giving upper bounds 6·8+12·12=192 or 17+6·8+11·12=197. For k≥2 the same previous inequality gives at most203. Thus B' has line cap3 in the presence of F.

In each projective line of U_B we can now find at least eight uniform normals: one associated parallel slice of B' contains at least eight sites by averaging; but an eight-site slice of cap3 cannot determine at most seven directions, by the two-arm certificate. This gives U_B at least eight sites per projective line. With N=|U_B| and n_L=|L∩U_B|, incidence gives
```
Σ_L(n_L−8)(n_L−10)=N²−307N+24560≥998.
```
The sum is nonpositive on nonfactor lines, and at most ten rational factors each contribute at most (17−8)(17−10)=63, total ≤630, contradiction. Hence no nonzero degree-ten form vanishes on U_B, and all degree≤10 moment forms vanish. This gives the claimed moments through degree ten for both members.

## At most one layer per member

Two distinct layer normals (each with eight full planes of size seventeen) imply a projection supported on X×Y for two eight-site level sets in F_17. The projection entries are in {0,...,6}, and all row/column integer sums are17. As in the size153 grid argument, barycentric interpolation gives
```
f(x,y)=λ_X(x)λ_Y(y) Q(x,y) modulo17,    total degree Q≤3,
```
where λ_X(x)=1/∏_{t∈X\{x}}(x−t), and similarly for Y. This follows by independence of all evaluated monomials with separate degrees≤7 and total degree≤10; their codimension is ten, and the weighted evaluations of the ten monomials of total degree≤3 belong to the annihilator. The latter follows because each product monomial has total degree≤13, so at least one separate degree is ≤6 and its barycentric sum vanishes.

The verifier [verify-fuglede-f17-size136-two-layers-M10.js](verify-fuglede-f17-size136-two-layers-M10.js) lists all 95 affine orbits of eight-site level sets and tests 4560 unordered pairs. For each Y, interpolate a possible row's polynomial after dividing by λ_Y from its first four values, and retain only rows with every entry in {0,...,6} and sum17. Across rows, the coefficient of y^j divided by λ_X(x) is a polynomial in x of degree at most 3−j. Interpolate each such coefficient from the first 4−j rows once available, thereby permitting only matching future rows, and prune column sums above17. The visited depth counts are [4560,189501,477361,72443,618,0,0,0,0,0]; there are no sequences of five compatible rows, and hence no full array. Thus each member has at most one layer.

The weighted argument of [FugledeF17Size136ConditionalM9Endgame.md](FugledeF17Size136ConditionalM9Endgame.md) now applies. The degree-ten conclusion in fact removes its sextic case. A genuine quintic profile forces a large projective support via the eleventh-moment form, and the indicator-versus-weight polarity estimate contradicts the tight-pencils upper bound with at most one layer. If there are no genuine quintics, the residues have degree at most four and the conditional quartic argument in [FugledeF17Size136ConditionalM11.md](FugledeF17Size136ConditionalM11.md) gives the same contradiction. This completes the exclusion of size136.
