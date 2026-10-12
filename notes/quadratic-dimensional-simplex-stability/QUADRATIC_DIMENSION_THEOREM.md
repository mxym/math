# Quadratic dimension growth for sharp simplex stability

Date: 7 October 2026. Status: complete written mathematical proof; independent analytic model audit PASS. This is not a Lean formalization, human peer review, or priority claim. The earlier d^6 sources remain unchanged.

## Theorem

For every d>=3, every full-dimensional convex body K in R^d, and EVERY prescribed maximum-volume inscribed simplex S with its own centroid z_S, the exact invariant of the pinned manuscript satisfies

    E(K,S) <= G_d e(K)^(1/(d-1)),
    G_d = 16(d+1)^2 [3d^2(d+1)^3(d+2)]^(1/(d-1))
        <= 2^12 d^2.

The exact coefficient is asymptotic to 16d^2. The exponent 1/(d-1) is unchanged and remains sharp by the pinned actual simplex-truncation family.

Here the definitions are unchanged:

    R_proj(K) = |Pi K|/|K|^(d-1),
    a(K) = (d/(d+1))^d R_proj(calP K)/R_proj(K) - 1,
    e(K) = a(K)-1/(d+1),
    E(K,S) = inf{t>=0: K subset z_S+(1+t)(S-z_S)}.

The names Pi and calP refer to exactly the operators defined in the pinned source, not a replacement polar-projection invariant.

## Proof organization and source pins

The self-contained new chain is in these two companion files, which should be read as parts of this proof:

1. [INTRINSIC_NORM_CONVERSION.md](INTRINSIC_NORM_CONVERSION.md) proves that, writing

       C=(d+1)^3(d+2), H=3d^2 C,

   every e<=1/H yields a genuine enclosing simplex P with

       sup_u [pi_P(u)-pi_K(u)]/pi_P(u) <= H e.

   The denominator is the unnormalized projection volume of P. Its proof uses the norm h_(K-K), actual cone-law directional dispersion, multiplicative barycentric weight correction, and Minkowski's first inequality. There is no Euclidean outer-radius loss.

2. [intrinsic_caps/INTRINSIC_GEOMETRIC_BRIDGE.md](intrinsic_caps/INTRINSIC_GEOMETRIC_BRIDGE.md) proves that an enclosing simplex P with relative projection deficit delta yields

       E(K,S)<=16(d+1)^2 delta^(1/(d-1))

   for every prescribed maximum S. It proves an exact affine vertex cap, constructs near-vertex points, compares determinants, matches stochastic-matrix columns, and uses maximality. The local coefficient improves to 8(d+1) when delta^(1/(d-1))<=1/[16(d+1)]; the uniform coefficient here is quadratic.

The only nonclassical imports are the first-moment weighted-anchor theorem in [imports/weighted_anchors.md](imports/weighted_anchors.md) and the actual cone-law identity in [imports/POLYNOMIAL_REFINEMENT.md](imports/POLYNOMIAL_REFINEMENT.md), Section 3, and [sources/entry005-v3.md](sources/entry005-v3.md), Section 4. Exact source and public-derivative hashes are recorded in SOURCE_PINS.json and SOURCE_FIDELITY.json. The anchor theorem uses D/B, with V the unnormalized lifted determinant; no determinant moment is changed. All classical geometric inputs are stated explicitly in the conversion companion.

## Assembly, including all branches

Translate by the centroid of the prescribed S. This preserves the invariant and the relevant centroid homotheties. Replacement maximality gives |alpha_i(x)|<=1 for all x in K. Therefore E(K,S)<=d+1 without a smallness assumption. It also gives -K subset dS subset dK, the asymmetry estimate needed in the intrinsic norm proof.

Set n=d+1, m=d-1, H=3d^2 n^3(n+1).

If 0<=e<=1/H, the intrinsic conversion yields P and relative projection deficit delta<=H e. Its strict anchor/weight gates hold because h<=C e<=1/(3d^2)<1/(2d). The geometric bridge gives

    E(K,S)<=16n^2 delta^(1/m)
           <=16n^2 H^(1/m) e^(1/m).

If e>1/H, the universal bound gives

    E(K,S)<=n< n H^(1/m)e^(1/m)
             <=16n^2 H^(1/m)e^(1/m).

Both proof chains include e=0: anchors then have zero assignment cost, all relative projection deficits vanish, the cap points are exactly the vertices of P, and every maximum S is P up to vertex relabeling. Hence E=0. The endpoint e=1/H belongs to the first branch; every strict gate remains strict there.

No replacement maximum simplex was selected. Translating back restores the original prescribed S and its original centroid. General affine invariance is not needed by the new norm/cap proof, although the source invariant has it.

## Uniform polynomial bound and asymptotic order

For d>=3, n<=4d/3 and n+1<=5d/3, so

    C=n^3(n+1)<= (320/81)d^4 <4d^4,
    H<12d^6.

The elementary inequality d<=3^((d-1)/2) follows from d=3 and induction, using (d+1)/d<=4/3<sqrt(3). Since d-1>=2,

    H^(1/(d-1)) <=sqrt(12)*27=54sqrt(3).

Consequently

    G_d <=16*(16/9)*54sqrt(3) d^2
         =1536sqrt(3) d^2
         <4096d^2.

Also log H=6log d+O(1), whence H^(1/(d-1))=1+O(log d/d), and therefore

    G_d=16d^2[1+O(log d/d)].

## What this does and does not settle

This substantially improves the frozen d^6 dimension exponent to d^2 without changing the sharp deficit exponent or the every-maximum-simplex requirement. The realized square-pyramid family still supplies the lower bound

    G_d >= (d+1)[d(d+1)]^(1/(d-1)),

which is asymptotically linear. The optimal dimension order remains between d and d^2. The local linear geometric coefficient does not close that global gap because its admissible relative cap parameter shrinks as 1/d.

The separate Euclidean-radius construction is outside this supplement. The quadratic upper proof does not depend on it.

No assertion of first discovery or formal verification is made. The independent analytic model audit is included as [INDEPENDENT_QUADRATIC_AUDIT.md](INDEPENDENT_QUADRATIC_AUDIT.md).
