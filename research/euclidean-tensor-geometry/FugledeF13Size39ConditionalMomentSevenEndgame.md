# Size 39: arithmetic endgame and a necessary weight-one profile

Assume a 39-point spectral pair in F_13^3, with no layered direction, affine plane cap9, and all mixed moments through degree seven zero. This conditional reduction does not assert degree-seven vanishing.

For each projective normal v of a member B, write its thirteen affine plane occupancies n_t, and let w_B(v)=(Σ_t binom(n_t,2)−39)/13. The polarity pair-count identities (as for size65) give
```
T_B=P w_B−15·1,       Σ_v w_B(v)=249,
```
where T_B(d) counts unordered B-pairs of difference direction d. Let V_B be the positive weight support (the nonuniform normals). Each d∈V_{B'} has T_B(d)=0; its neighboring positive weights therefore sum to 15. Regard incidence between V_B and V_{B'} as a bipartite graph.

Reduced residue profiles have degree ≤4 by moment orthogonality. Nonuniform constant profiles require a layer, already excluded; affine and quadratic nonconstant mass39 profiles are impossible (see the M5 proof). All genuine cubics have weight3 and constants 3 or9 in centered form. The [quartic verifier](verify-fuglede-f13-size39-quartic-tight.js) checks the whole centered genuine quartic census: possible weights range from 2 to 6. Hence every tight pencil has at most seven positive profiles. An almost-uniform pencil with at most five positive profiles would force a layer by the M5 proof, so each vertex has degree six or seven.

In a six-profile tight pencil, there must be a genuine quartic because cubic weights already give 6·3>15. The quartic leading congruence forces all six to be genuine quartics, since any five distinct projective fourth-power columns are independent. Normalize their forms to x,y,x+y,x+s y,x+t y,x+u y, and translate to kill the first two centered shifts. The remaining four shifts vanish by independence of their four cubic-power columns and the cubic homogeneous congruence. Thus the six profiles have the form a_i l_i^4+b_i l_i²+c_i l_i+d_i, with a_i≠0 and all degrees<13. The cited verifier enumerates all 165 normalized slope masks, with 12 nonzero leading choices each (1980 in total). The remaining equations are fixed positive-profile weight15, quadratic relation, linear relation, and constant sum 3·5=15 modulo13. Each profile must have cap9, so no zero can be lifted to 13. Exactly 720 tuples satisfy all necessary conditions, each with sorted weight pattern (2,2,2,2,3,4). For degree seven, weight at least two and sum15 immediately gives (2,2,2,2,2,2,3).

Now let H_B be the subset of V_B with weight4. Every degree-six opposite vertex has exactly one neighbor in H_B, whereas degree-seven vertices have none. The weighted mass of degree-six vertices on the opposite side is therefore 15|H_B| by double-counting each incident opposite weight at H_B. A second weighted count gives
```
15 |V_B| = Σ_{d∈V_{B'}} degree(d) w_{B'}(d)
         = 7·249 − 15|H_B|.
```
This is impossible modulo15. Consequently affine plane cap9, no layers, and moments through seven suffice to exclude cardinality39. At the time of this note, only moments through six have been established.

## A necessary weight-one profile without assuming degree-seven vanishing

One can sharpen the reduction using just the proved [moments through degree six and plane cap nine](FugledeF13Size39MomentsSix.md). Under those assumptions each residue profile has degree at most five. The six-profile tight-pencil result above remains valid without degree-seven vanishing: the positive-degree Radon relations alone make every profile in such a pencil have degree at most four.

For a seven-profile tight pencil, if there is a genuine quintic then all seven profiles are genuine quintics, by independence of any six distinct fifth powers. Translate the projection plane to remove the \(t^4\) terms in two profiles. Independence of the other five fourth powers removes those terms in all seven profiles. A common scalar change of the planar coordinates normalizes a chosen leading coefficient to one, because raising to the fifth power permutes \(\mathbb F_{13}^{\times}\).

The [quintic verifier](verify-fuglede-f13-size39-quintic-seven.js) takes all seven-direction subsets of the projective line containing a marked \(0,1,\infty\), minimizes across all ordered triples to obtain the five projective mask orbits, and works over their normalized representatives. The degree-five relations then fix the one normalized leading vector. The degree-three relations determine four of the cubic coefficients from the other three. For each such choice, centered mass-39 profiles with occupancies at most nine are tested against the remaining quadratic, linear and constant congruences and the exact weight sum fifteen by matching a group of three profiles against a group of four. The only resulting weight patterns with a genuine quintic are:
 
| Sorted weights | Number of centered tuples in the chosen normalizations |
|---|---:|
| \(1,1,1,2,3,3,4\) | 2 |
| \(1,1,1,1,3,3,5\) | 1 |
| \(1,1,2,2,3,3,3\) | 9 |

These are normalized tuple counts, not orbit counts of valid spatial sets. In particular each such pencil contains a weight-one profile.

Suppose now that a member \(B\) has no weight-one profile. The weights are nonnegative integers and each tight pencil into \(V_B\) therefore has only six or seven nonzero profiles, as the upper bound of seven follows from its weight sum fifteen and the lower bound of six was proved without moments. The seven-profile quintic census excludes genuine quintics on those pencils, so the same degree-six and degree-seven patterns as above hold. The weighted double count uses only these pencils and the tightness relation in the other member. It again gives \(15|V_B|=7\cdot249-15|H_B|\), impossible. Consequently **each member of any hypothetical size-39 spectral pair has a weight-one normal**. Excluding weight one in just one member now suffices, even without a global seventh-moment proof.
