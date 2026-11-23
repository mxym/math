# Any Fano field forces one of five short unit types

Fix a true neutral norm-14 field f, and any maximal determinant-49 extension H containing its normalized norm-two root. Such an H exists because the class of this root is isotropic. Let W_at be the usual **fixed-H**, isometry-averaged folded masses: for nonisotropic norm the H-eligible population divided by eight; for isotropic norm the unscaled zero-residual-class population. No equality of individual class counts is assumed. Then

    7W020 + W024 + 2W226 + 2W230 + W337
          ≥ 6 + 2W016 + W121 + W335 + W444.

In particular any Conway graph having any Fano field must have a selected unit type among neutral norms 20,24 and (2,26),(2,30),(3,37). This is unconditional in Seidel rank and permits more than one compatible Fano. Conversely if all five types are absent, every triangle wing is two-cut-free by [thin-cut emission](../arbitrary-wing-thin-cuts.md). This is not a proof that the seven complementary selected types cannot constitute the support without a Fano.

## Root-angle variables

For a field b of charge a and squared cost t, set k=b·f/7, its pairing in the graph summand against the normalized norm-two root. This integer has 63k²≤2(9t−11a²) by centering and Cauchy. Its only possible denominator is seven, at which integrality follows from b being H-eligible and f in H. Translating by n f preserves the charge and residual class and changes (t,k) to (t+14nk+14n²,k+2n). Reflection b−k f proves that the two signed angles ±k have equal populations even within each charge. For j=0,1 put K_atj equal to the corresponding folded mass at *one specified signed angle j*, not the sum over signs. Any slot at positive k therefore has single-sign mass K_(a,t−7(k²−j)/2,j), j=k mod 2. Use the [usual impossible short costs](site_degree_ten.py) and omit odd angle at (0,0) or (0,14); no two distinct Fanos in H have nonzero angle by the Fano overlap bound. The angle-zero (0,14) variable is **not** set to zero.

We have K016,1=K018,1=0. Otherwise b and b−f are two distinct norm-16 or norm-18 fields with squared difference 14. This is impossible by the [norm-16 theorem](../norm16-packing.md) and the [norm-18 angular cap](unconditional-cross-shell-centroids.md). Thus W016=K016,0. Also K123,1≥14. The seven site labels d_i=3e_i−Ae_i on the positive side of f have angle +1; the seven d_i+f from the negative side have the same charge/cost and angle +1. These families are disjoint: a difference of two distinct site labels has squared cost 42 or 56, not 14. All belong to the zero residual class before counting. Finally K222,1≤1: a cost-22 charge-two field is minus the indicator of a Hoffman coclique. Angle +1 requires all seven negative sites of f in the coclique and none of its positives; independence forces the other 15 sites to be precisely the 15 missing the signed support. This is an upper bound even if that unique endpoint is not eligible in H.

## Exact harmonic relation

Write S=14W020+2W024+4W226+4W230+2W337. The [integer coefficient checker](fano_axis_five.py) verifies that
```
S − 8K016,1 + 48K018,1 =
 12 + 4K016,0 + 36K020,1 + 16K022,1 + 12K024,1 + K028,1
    + 4K121,1 + 72K226,1 + 4K228,0 + 4K234,1
    + 2K335,0 + 4K335,1 + 4K337,1
    + 2K444,0 + 4K444,1 + 2K446,1 + 2W121
    + 2(K123,1−14) + 28(1−K222,1).
```
At (3,35) or (4,44) no |k|≥2 occurs: the translated minimum cost would be 21 or 30. In the relation the corresponding two terms on each type are therefore twice its total W. The previous paragraph makes all other terms nonnegative after retaining the constant, W016 and W121. All five left-hand types and (0,16),(1,21) are unit automatically at their displayed costs; the W335 and W444 terms need only be nonnegative.

For reproducibility, use the existing [four rank-48 gluings and projection tables](higher_moments.py) and [zonal harmonic identities](site-degree-ten.md). On the sum of the Fano root and any auxiliary probe h, use three times this axis to clear the auxiliary denominator. Its norm is 9(2+hᵀGram·h), and its pairing is 3k+(3/scale)h·w for an auxiliary numerator w of denominator scale=1 or 3. Reconstruct the even degree 2,4,6,8,10 harmonic shell rows on norms 2,4,6, with charge multiplicity 1 for neutral and 2 otherwise, folding each signed k exactly by the preceding translation. Append the existing auxiliary higher-moment rows after undoing their four unit substitutions. On 118 angular keys these 224 integer rows have rank 84 before and after adjoining the displayed exact equality. Run `python3 fano_axis_five.py` beside the existing checkers. The proof uses no optimizer, fixed scalar tuple, projected-site uniformity, or original-class hypothesis on f.

If f **is** original, apply the inequality to every H. Every species in that inequality has nonisotropic residual norm, so the usual graph-wide averaging multiplies each mean W by p=7^((44−r)/2)+1. In particular
```
7N20+N24+2G226+2G230+G337 ≥ 6p+2N16+G121+G335+G444
```
for the unnormalized graph populations. At rank 36 the 6p alone is 14,412. At rank 36 with no original Fano, each extension instead contains at most one direction by [the no-orthogonal-Fano theorem](../rank36-no-orthogonal-fanos.md); each nonzero isotropic Fano line occurs in precisely 1/p of the maximal extensions. Summing the constant bound over occupied extensions only gives 7N20+N24+2G226+2G230+G337 ≥3N14 even then. This last consequence counts true oriented Fano fields and uses the absence of compatible pairs, not independence of H-events.
