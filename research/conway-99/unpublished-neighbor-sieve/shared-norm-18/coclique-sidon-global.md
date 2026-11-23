# An unconditional four-family population bound

For any putative Conway graph of any of the four remaining Seidel ranks r, put p=7^((44−r)/2)+1. Let N_t be the number of oriented neutral norm-t labels, and let U_(a,t) count positive-charge labels with every nonzero entry equal to ±1, as in the [twelve-type dictionary](../short-shell-moments.md). Then
```
676N18 + 212N20 + 92U(2,30) + 72U(3,37)
 >= 545p + 193N16 + 112U(1,21) + 52U(1,25) + 304U(2,26) + 12U(2,28).
```
In particular at least one of the four families on the left must occur. Since N18 and N20 are signed units, all nine quantities in this display count actual unit labelings, not glue-class multiplicities. No short-type absence assumption, norm-14 upper bound, norm-18 packing bound, prescribed automorphism, or rank-36 conditional population cut is used.

**Proof.** On each maximal determinant-49 extension keep raw W where not restricted, and the **unit** folded count V on the twelve named types. Thus W_(1,25)=V_(1,25)+8V_(0,16), W_(1,27)=V_(1,27)+9V_(0,18)+2V_(2,26), W_(0,26)=V_(0,26)+8V_(1,21); all other named types are already units, including W_(2,26)=V_(2,26). These are exactly the substitutions used to produce the [full higher-moment rows](higher_moments.py), not extra assumptions. Let M=W222, S=W123−99−7W014. The [Sidon and disjoint injection](coclique-sidon-cut.md) giving
```
K = Y2+W014−462−144M−2S+2W446+2550 >= 0
```
is valid separately in every extension, including those with no cocliques or no Fano roots. It uses the global minimum 14 for a nonzero neutral label, the actual integer count M, and the proved short charge-one dictionary. The scalar relation from [the quadratic cut](rank36-coclique-tangent.md), **without** sparsity restrictions, reads
```
Y2=1000−8W014+200V016+88V018+64V020+24W022+48W333+8V024+16W335.
```
Here the factor eight at nonzero value is essential, and the charge-three contributions in the x11,x12 scalar slots are retained.

Take the full zero row E in [the restricted Sidon proof](coclique-sidon-cut.md), but now retain the omitted columns. In the order (016,018,020,121,125,226,228,230,337), their coefficients on the **unit** variables V are (593,−500,−84,112,52,304,12,−92,−72). The [exact unprojected checker](coclique_sidon_global.py) appends this entire target row to the reconstructed rational moment matrix with **every column present** and verifies unchanged rank. Substitution gives
```
676V018+212V020+92V230+72V337−193V016−112V121−52V125−304V226−12V228
 = 545+2K+154W014+24W335+62W444+3W448 >= 545.
```
Finally average over H. Each of the nine V types has nonzero residual norm; a given oriented graph labeling occurs in H-perpendicular with probability 8/p, and the folded count divides by eight. Thus each mean V is the actual unit graph count divided by p. Multiply through by p to obtain the displayed graph bound.
