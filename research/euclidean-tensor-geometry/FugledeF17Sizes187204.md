# Spectral cardinalities 187 and 204 excluded in F_17^3

**Theorem.** There is no spectral set in F_17^3 of cardinality 187 or 204. This does not settle the other candidate cardinalities.

For either hypothetical member B of size17m, put D(B) for its difference directions and U_B for normals of uniform plane occupancy m. The general preliminaries in [FugledeF17Size221CapBootstrap.md](FugledeF17Size221CapBootstrap.md) apply: D(B) lies in the other member's U, affine planes have cap17, and no U contains a full projective line. At least one normal on every projective line is uniform. If r uniform normals is guaranteed on every projective line of both members, the pencil through any affine line of occupancy a satisfies
```
17m+17a ≤ rm+(18−r)17.
```
A lower bound r follows from the minimum number of directions of an m-site planar set under the current line cap: for any pencil the parallel affine slices of the partner have average m, and select m sites from a maximal slice.

## Shared geometric and moment reduction

For m=12, the initial cap is 5. The exact planar census of 12 points at cap5 and at most eight directions is empty (3003 masks, 1176726 states, maximum9). For m=11, the initial cap is 6, and the 11-point at cap6 and at most eight directions census is also empty (3003 masks, 1226352 states, maximum9). Therefore both cases have r≥9. The pencil bound then makes both spatial line caps at most three. The common exact planar census of eleven points at cap3 and at most nine directions is empty (5005 masks, 3801003 states, maximum9), so both sizes now have r≥10. Each checker fixes a marked noncollinear triangle at 0,e1,e2, enumerates all enlarged slope masks containing its three slopes, then enumerates all cap-compatible extensions in increasing order. See [verify-fuglede-f17-sizes187-204.js](verify-fuglede-f17-sizes187-204.js).

If a nonzero homogeneous degree-thirteen form vanished on U_B, write N=|U_B|, and n_L for its intersection size with a projective line L. Then 10≤n_L≤17. Each nonfactor line has n_L≤13; at most thirteen factor lines can contribute positively to Σ(n_L−10)(n_L−13), each by at most (17−10)(17−13)=28. The sum therefore is at most364. But counting projective incidences gives
```
Σ_L(n_L−10)(n_L−13)=N²−397N+39910 ≥508
```
(the minimum runs over integers), contradiction. Therefore no nonzero form of degree≤13 vanishes on U_B (multiply by a nonzero linear form to raise degree). For j≤13 the homogeneous moment M_j(v)=Σ_{b∈B}(v·b)^j vanishes on U_B, since the field power sum is zero there. Thus all mixed moments through degree13 vanish, and each plane-occupancy residue profile is a polynomial of degree≤2 by orthogonality to evaluated powers 0..13 in F_17. A nonconstant affine profile has mass136 or153, both impossible. A constant profile is uniform or layered (m entries equal17, other entries zero).

The exact centered genuine-quadratic catalog tests a t²+c for all a≠0,c, with possible zero lifts k=(17m−sum of least residues)/17 an integer between zero and the number of zeros. For m12 it finds no compatible genuine quadratic profiles. For m11 it finds exactly 32, split evenly between (weight, zero lift count, constant) triples (9,2,13), (12,2,15), (8,2,3), (11,2,5). Here the profile weight is w=(Σ_t binom(n_t,2)−17 binom(m,2))/17.

## Closing cardinality 204

Only uniform12 or layered profiles remain. Fix a secant line of occupancy a≥2. Each of its eighteen incident planes is nonempty, hence has occupancy twelve or seventeen. If s have occupancy twelve, the pencil identity is (17−12)s=17(18−12−a). Thus s is divisible by17 and is either 0 or17. These yield a=6 or a=1, respectively. Both contradict 2≤a≤3.

## Closing cardinality 187

Use weighted projective polarity, with P(v,d)=1 iff v·d=0 on the 307 projective sites. It satisfies P1=18·1 and P²=17I+J. The pair direction count T_B obeys q_B=P T_B where q_B(v)=Σ_t binom(n_t,2); hence, writing w_B=(q_B−17 binom(11,2))/17, we have
```
T_B=P w_B−33·1,       Σ_v w_B(v)=1529.
```
Every nonuniform partner normal d has T_B(d)=0, so its polarity pencil has total w_B weight33 (a tight pencil). Positive profile weights are at least8 for genuine quadratics and exactly33 for a layer, so a tight pencil contains at most four nonuniform profiles. On a pencil with b nonuniform normals the planar projection f and its nonuniform profiles g_i(l_i) satisfy the integer Radon identity Σ_i g_i(l_i)=11(b−1)+17 f. By independence of distinct projective powers (Vandermonde), at most three profiles cannot have a nonzero quadratic coefficient. Since affine profiles are absent, such cases only contain layered profiles, and tightness forces a single one.

If b=4, all four are genuine quadratics by tightness and the exact quadratic catalog. Their weights summing33 are (8,8,8,9). Translate in the projection plane to put the first two centers at zero; the linear homogeneous congruence forces both remaining centers zero because their forms are independent. The centered constants must then sum to 11·3≡16 mod17 by the Radon identity. But the catalog gives 3+3+3+13≡5, contradiction. Thus every tight pencil consists of a single positive weight33. Every positive B weight belongs to a tight pencil contributed by a positive partner neighbor: apply the same identity with the roles reversed to a nonuniform normal of B, obtaining total positive neighboring partner weight33. Therefore all positive B weights equal33. This contradicts their total1529, not divisible by33.

Together with the separate 221-point exclusion, these results eliminate the three largest cardinalities not covered by the general Malikiosis threshold; no claim about the lower sizes follows here.
