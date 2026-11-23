# Five sparse supports excluded by keeping the original 7-class at each graph site

For a hypothetical unrestricted SRG(99,14,1,2) the positive support among the twelve selected **unit** types cannot be contained in any of these sets at the indicated rank. A code is 100a+t for the unit type (a,t); 26 means the unit neutral norm-26 subpopulation, not its raw shell.

| rank over F7 | allowed unit types, leading to contradiction |
|:---|:---|
| 36 | 16, 24, 127, 337 |
| 36 | 18, 26, 125, 230 |
| 36 | 18, 24, 26, 230 |
| 38 | 24, 26, 230 |
| 38 | 26, 228, 230 |

This strengthens the earlier [rank-36 support tests](rank36-four-hit-sets.md) and [rank-38 support tests](rank38-three-hit-sets.md); it does not eliminate either rank or assume a graph automorphism. Neither a numerical SDP nor a numerical LP is used in the proof.

## Two site populations instead of one

Use the 60 raw charge/cost types occurring in the four rank-48 neighbor constructions. At a graph site p, a graph field of charge a and cost t has integer coordinate k=b_p. The admissible slots and valid bijections among triples (a,t,k) are exactly those in the [single-site theorem](site-degree-ten.md), imported without change. There are 172 signed/translated representative triples. For a representative z, denote by W_z the site-averaged normalized population of the previous theorem, further averaged over all maximal totally isotropic spaces H of the original 7-primary discriminant space. These are real nonnegative numbers. Sum over the site values to recover the mean raw W(a,t), not its unit part.

At isotropic quadratic value (9t−11a² divisible by 7), introduce **separate** coordinates C_z: zero original 7-class fields, averaged over the 99 graph sites, without normalization by the number of extensions. There are 33 such representatives. Each C_z is nonnegative and C_z≤W_z because every extension contains the original zero class. Its signed site switches preserve the zero class, as 3u_p belongs to L, exactly as in the single-site proof. Let p_r=7^((44−r)/2)+1. The global raw count at this site slot, averaged over sites, is
```
G_z = p_r W_z                         at anisotropic value,
G_z = p_r W_z − (p_r−1) C_z           at isotropic value.
```
This is the [original/extension incidence formula](rank38-three-hit-sets.md) applied separately to each site signature. A field’s membership probability in H-perpendicular depends only on the discriminant class. Marking or averaging the graph site does not alter that probability. No class uniformity or vertex transitivity of graph fields is assumed.

The checker uses the raw/selected transfers, equalities of both first and second moments of the site coordinate, the unit-corrected higher-moment rows, and the rank-48 degree 2,4,6,8,10 marked identities from [the single-site theorem](site-degree-ten.md). Both W and, where defined, C satisfy the site-averaged first two moment identities separately; C000=W000=1. In particular the face constraints are on raw W(1,25)−8W(0,16), W(1,27)−9W(0,18)−2W(2,26), and W(0,26)−8W(1,21) when those selected types vanish. For the other nine selected types the raw W count is the unit count.

## Original level-seven theta data in the same coordinates

In the Euclidean site-coordinate model let P be the rank-44 projection onto the −4 eigenspace. At the chosen site use the axis 9P e_p, of squared norm 36 because P_pp=4/9. Against the K=√7 L* field v=b+(a/9)1 its inner product is 9k+a and the shell is v²=2j. The monic degree-d zonal harmonic at axis/norm pair (u,s) in dimension n=44 is
```
h_d(u,s)=Σ_l c_l u^(d−2l)s^l,   c0=1,
c_(l+1)=−c_l (d−2l)(d−2l−1) / [2(l+1)(n+2d−2l−4)].
```
Here s=36·2j; the checker multiplies each polynomial by a fixed positive denominator. The **global** weighted coefficient X_j is the sum over G-slots of the two signatures (0,2j) and (3,2j+11), with charge multiplicities 1 and 2. This is an averaged theta series of an actual lattice; equality of the individual site series is not needed. The **graph-scale original** coefficient Z_i at norm 14i is the same weighted sum using C-slots at j=7i. It is 7^(d/2) times the weighted norm-2i coefficient of L. The formula also applies at j=0 with d=0, and absent low shells contribute zero. In particular, using W in place of C for this second coefficient would not be justified.

For d=0,4,6,8,10,12,14,16 use the 22 successive X coefficients j=0,…,21 and the four Z coefficients i=0,…,3. Their combined tuple lies in the coefficient span of level-7 modular forms of weight k=22+d and trivial character, with second component the negative Fricke companion times 7^(r/2−11+d/2). Even-degree harmonic Poisson summation gives the same negative sign as for d=0: the transform of a Gaussian times a degree-d harmonic contributes the factor τ^(−d), and d is even. The scaling 7^(d/2) remaining in the stated companion comes from evaluating H on √7 L. The odd-weight Eisenstein products with the two character placements are as in [the quartic calculation](original-site-quartic.md); the checker verifies independent echelon pivots for all 1+2⌊k/3⌋ basis directions, the standard dimension of M_k(Γ₀(7)) at these weights. It then imposes the exact nullspace constraints of the indicated 26-entry tuple. This is the extra connection between original true classes and marked maximal-extension populations.

## Nonnegative rows and graph counts

The certificate outputs use only explicitly named nonnegative orbit masses, W_z−C_z, some site-specific mandatory graph marks, and four published packing inequalities. In the names, n16 is 6930−N16, fn is 198−N14 when N20=0, fn2 is 112−N14 when N20=N24=0, and n18b is 16166−N18 when N16=N20=0. See [the Fano difference bound](fano-difference-packing.md) and [the rank-36/38 packing rows](rank36-four-hit-sets.md). All conditional prerequisites are checked for each allowed set; type 14 is counted globally, not in an averaged extension.

For an (a,t) original mark present with M distinct images, each with f_k entries k, we have 99 C_(a,t,k)−M f_k≥0. The marks used in the stored duals are literal:
* The 99 individual d_i have signature (1,23), one +3, fourteen −1, eighty-four zeros.
* The 693 edges give d_i+d_j of signature (2,36), with two +2 at the edge ends, one −2 at the unique common neighbor, 24 entries −1 and 72 zeros. The two +2 positions distinguish every edge.
* The 8316 three-site induced paths give charge-three norm-53 fields, with one center +1, two +2, three −2, 32 entries −1 and 61 zeros. Their full positive support gives the path, and the exterior −2 slots are the distinct edge caps and the second common neighbor of the leaves. See also [the quartic mark calculation](original-site-quartic.md).

All these literal marks have zero 7-component before any residual averaging: each site generator u_i has 3u_i∈L. This also holds for the listed non-neutral charges; it is zero seven-component, not neutral charge, that defines C. Only these marks are cited by the duals; the checker may construct additional known necessary slacks which no witness uses.

Run `python3 original_site_populations.py` with SymPy and the existing upstream dependencies including python-flint. The [five rational duals](original-site-population-duals.json) use 11,12,12,11,11 strictly positive coefficients respectively. Common homogeneous equations have rank 184 on 205 coordinates. For each allowed set the checker verifies that the sum of its nonnegative terms plus W000 is exactly zero modulo the common equations and the forbidden-unit equalities. Since W000=1 this is a contradiction. No conclusion about the existence of a graph realizing any other candidate follows.

The [common four-way hit](ranks38-40-four-way-hit.md) applies the same chart at both ranks 38 and 40 to prove that at least one of `020`, `024`, `125`, `127` occurs, without assumptions on the remaining eight types.

A [Hoffman projection obstruction and four native population bounds](hoffman-fano-large-family.md) show that a maximal extension with 55 eligible 22-cocliques cannot contain two Fano directions, and force that obstruction to apply in every extension on specified rank-40 and rank-42 support faces.
