# Actual truncation sharpness: analytic proof and Lean obligations

This is an independent proof of the actual truncation construction in the
published sharp-stability note. It preserves the paper's `entryDefect`, a
genuine maximum inscribed simplex, and that simplex's own centroid. The
previous finite-pyramid/B delivery remains frozen. No statement in this
document alone is a kernel certificate.

## 1. The bodies, facets, and volumes

Fix an integer d ≥ 3 and 0 < t < 1. In Euclidean coordinate space define

    K_t = {x : x_i ≥ 0 for all i, t ≤ Σ_i x_i ≤ 1}.
    P_0 = {x : x_i ≥ 0 for all i, Σ_i x_i ≤ 1}.

K_t is compact and convex, has nonempty interior, and equals the convex hull
of the actual 2d points e_i and t e_i. To see the last assertion, put s=Σx_i
and p=x/s. Then p_i≥0 and Σp_i=1, and

    x = (s-t)/(1-t) · p + (1-s)/(1-t) · t p.

These are nonnegative convex coefficients. Conversely all displayed vertices
satisfy the inequalities and the inequality set is convex. Its interior
contains the point ((1+t)/(2d), …, (1+t)/(2d)).

The volume is |K_t|=(1-t^d)/d!. Indeed P_0 decomposes into K_t and tP_0,
whose overlap is contained in the hyperplane Σx_i=t and has d-dimensional
Lebesgue measure zero. Dilation multiplies the removed volume by t^d.

Put c=1/(d-1)!, q=t^(d-1), and r=1-q. The actual coordinate facets x_i=0
are (d-1)-dimensional simplex shells, with area c r. The actual top facet
Σx_i=1 has area c√d; its bottom homothet Σx_i=t has area c√d q. With the
outward *unit* normal n, facet area A, and support h, their raw area vectors
u=A n and area-support products b=A h are

    coordinate i: (u_i,b_i)=(-c r e_i,0),
    top:          (u_+,b_+)=( c·1, c),
    bottom:       (u_-,b_-)=(-c q·1, -c t^d).

The negative bottom support is not a probability weight. To consume the
proved finite-halfspace cone law, translate the interior point z above to
zero. All new support heights are positive; b changes to b-u·z. A single
row operation in each lifted determinant preserves it, and the proved
affine invariance restores the original `entryDefect K_t`.

## 2. Real projection/pyramid invariant

The previously certified finite-facet, zonotope, and pyramid/B identities
give, for the actual polytope,

    entryA(K_t) = L/(d |K_t| H),

where H sums absolute horizontal d-minors of the u's, and L sums absolute
lifted (d+1)-minors of the (u,b)'s. These are unordered distinct-facet sums;
permutations contribute d! and (d+1)! in the iid formulas.

The all-coordinate horizontal minor contributes c^d r^d. The d minors
with top and d-1 coordinate facets contribute c^d r^(d-1) each; with bottom
they contribute c^d q r^(d-1) each. Any minor containing both top and bottom
has parallel columns and vanishes. Therefore

    H = c^d r^(d-1) [d+1+(d-1)q].

The lifted minors with all coordinate facets and top or bottom contribute
c^(d+1)r^d and c^(d+1)r^d t^d. The d remaining minors contain top, bottom,
and d-1 coordinate facets, and each has magnitude
c^(d+1) r^(d-1)(q-t^d). Here q-t^d=q(1-t)>0. Thus

    L = c^(d+1)r^(d-1)
        [1+(d-1)q-(d-1)t^d-q t^d].

Since d|K_t|=c(1-t^d), the actual excess defect is exactly

    e(K_t) =
      t^(d-1)[d(d-1)-(d+1)(d-2)t-2t^d]
      / [(d+1)(1-t^d)(d+1+(d-1)t^(d-1))].       (D)

Every canceled factor is strictly positive. The numerator bracket equals

    (d+1)(d-2)(1-t) + 2(1-t^d),

which is positive in the stated domain. In particular e(K_t)>0. Dividing
(D) by t^(d-1), continuity at t=0 gives the exact analytic limit

    lim_{t→0+} e(K_t)/t^(d-1) = c_d=d(d-1)/(d+1)^2>0.       (L)

This is not a numerical asymptotic or a replacement scalar invariant: the
geometric-to-(D) theorem is a separate required Lean obligation.

## 3. The prescribed simplex is actually maximum

Take S_t=conv(e_1,…,e_d,t e_1). Every nondegenerate simplex drawn from the
2d actual vertices must use each of the d coordinate rays, with one ray
doubled. Its absolute lifted determinant is (1-t)t^k, where k counts bottom
vertices among the other d-1 rays. It is ≤1-t, with equality exactly when
all other selected vertices are top vertices. Missing rays or repetitions
give determinant zero.

For arbitrary d+1 points z_j in K_t, expand each into its 2d-point convex
combination. Multiaffinity expands the lifted determinant as a convex
combination of the above actual vertex determinants. The triangle inequality
bounds its magnitude by 1-t. Since actual simplex volume is its determinant
magnitude divided by d!, this proves

    M(K_t)=(1-t)/d!, and S_t is maximumInscribed.

This proof covers arbitrary inscribed points and does not assume the maximum
occurs at polytope vertices.

For completeness every maximum simplex is, up to ordering,
S_p=conv(e_1,…,e_d,tp), with p_i≥0 and Σp_i=1. Equality in the expansion
forces every positive-weight selected vertex tuple to be maximal. Regarding
the independent convex weights as finite probability laws, the sum of the
independent bottom indicators is identically one. Its variance is the sum
of nonnegative p_j(1-p_j), so each slot has deterministic top/bottom type.
There is exactly one bottom slot. The d top supports are nonempty and
pairwise disjoint, hence are the d distinct singleton top vertices. The
bottom point may be any convex combination tp. This classification is useful
for best-maximum estimates but is not required for the literal existential
`truncationSharpnessGoal`.

## 4. Exact excess about the same original centroid

For S_p set s_x=Σx_i. Its actual barycentric coordinates are

    β_0(x)=(1-s_x)/(1-t),
    β_i(x)=x_i-tp_i β_0(x).

On K_t, 0≤β_0≤1 and β_i≥-tp_i. Equality for β_i occurs at t e_j, j≠i;
such a j exists because d≥2. The simplex's own centroid has every
barycentric coordinate 1/(d+1). Consequently its centroid dilation with
excess ε≥0 is precisely β_i≥-ε/(d+1) for all i. Hence the literal infimum
in the target definition is

    excess(K_t,S_p)=(d+1)t max_i p_i.

For the chosen p=e_1 this is exactly (d+1)t. Neither the reference-simplex
centroid nor a freely optimized center is substituted.

## 5. The original exponent and quantifiers

Fix α>1/(d-1), C≥0, ε>0. By (L), for all sufficiently small positive t,
0<e(K_t)≤2c_d t^(d-1). In particular e(K_t)→0. Since α>0,

    C e(K_t)^α / [(d+1)t]
      ≤ [C(2c_d)^α/(d+1)] t^((d-1)α-1) → 0.

The exponent on t is strictly positive. Choose t small enough for this ratio
to be <1, for e(K_t)<ε, and for 0<t<min(ε,1). The actual body K_t and
actual maximum simplex S_t then satisfy every conjunct of the unmodified
`truncationSharpnessGoal`. The case C=0 also follows immediately from
positive excess.

At α=1/(d-1), the same exact limit forces every universal
every-maximum constant to be at least

    (d+1)[(d+1)^2/(d(d-1))]^(1/(d-1)).

For all maximum simplices the smallest excess is ((d+1)/d)t, realized by
p_i=1/d. No premise of the published construction appears insufficient;
no counterexample or change of exponent is needed.

## Lean implementation obligations and existing reusable interfaces

1. Construct `truncationBody d t` from the literal `truncationSet`. Prove
   compactness, convexity, interior, and the exact 2d-vertex convex hull.
2. Construct the genuine `Affine.Simplex` S_t. Prove arbitrary-vertex lifted
   determinant ≤1-t; consume the real-volume/determinant bridge to conclude
   `maximumInscribed`. The all-maxima classification is an optional extension.
3. Derive actual facet chart areas and the volume. Reuse the certified
   finite-halfspace charts/Cauchy/radial volume interfaces; official upstream
   standard-simplex volume is available but its current extra module must be
   compiled and axiom audited before consumption. Supply no area/Jacobian axiom.
4. Derive actual finite horizontal/lifted sums (H,L). Reuse the certified
   pyramid/B and zonotope interfaces; translate to a proved interior point,
   use positive heights, then `entryDefect_affine_image`. This closes (D) for
   the target's real geometric invariant.
5. Prove the exact barycentric halfspace description of `centeredDilation`
   and the actual `sInf` equality `excess(K_t,S_t)=(d+1)t`.
6. Prove continuity and positivity of the rational expression and the
   real-power obstruction. A conditional scalar theorem is an assembly tool,
   not a formalization of (D); the final sharpness theorem must discharge (D).

The frozen `Targets.lean` must remain byte-identical. Kernel-checked claims
will be recorded separately with exact theorem statements, all assumptions,
axiom closures, and clean compilation logs. The Main upper bound remains
owned by the other task.
