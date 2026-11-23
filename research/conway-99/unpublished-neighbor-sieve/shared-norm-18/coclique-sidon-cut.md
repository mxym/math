# A Sidon bound on compatible cocliques excludes a three-type alternative

At any of the remaining ranks, the selected unit types cannot be confined to norm 24, unit norm 26 and unit (1,27). This excludes one more of the exactly-three-type alternatives at rank 36. No symmetry of the graph is used.

Use the normalization of [the quadratic coclique cut](rank36-coclique-tangent.md): within the determinant-49 extension for H, let M=W222 count the actual 22-cocliques whose seven-component lies in H, with no divisor of eight here. Count ordered distinct pairs by their overlap k=1,8,15, with populations n1,n8,n15. The earlier proof gives difference injections at overlap 8 and 15. At overlap one the ordered difference also determines the pair: on the two exclusive sides of size 21 it identifies the signs, the common residual site is anticomplete to them, and every other point outside the sides sees three or four members of either side (it has four contacts to the whole first coclique, at most one the residual site). Thus all nonzero ordered differences determine their operands. In particular the family is a Sidon set: C+D=C'+D' for distinct unordered pairs would give the same ordered nonzero difference C−C'=D'−D. The coclique labels here can simply be viewed as their actual integer indicator vectors; the statement is not about equality of discriminant residues.

At overlap one, adding the two negative indicators gives charge-four norm 46, with seven-component in H. For this type the quadratic value at seven is zero, hence its unscaled H-count is W446. Each such target admits at most two *ordered* preimages by the Sidon property. Therefore n1≤2W446.

Let S=W123−99−7W014 count unit charge-one norm-23 fields in this same extension; this equality is the [one-site translation dictionary](../affine-witness.md). We strengthen the previous norm-four budget by disjointly injecting S more positive-charge fields. A unit field b here has 6 positives P and 17 negatives N; from Ab=−4b−2, counting cross edges at the two ends gives 36+2e(P)=34+2e(N), so N contains an edge ij. As usual d_i=3e_i−Ae_i. The translate b+d_i+d_j has charge 3 and evaluation norm 39 because the true edge has (d_i+d_j)^2=36 and b·(d_i+d_j)=−10. Its entries at i,j are both +1. No additional positive site is adjacent to i or j, since every such vertex loses at least one from b. There are at most three positive sites: sum_x c_x(c_x+1)=39−33=6. Thus ij is the unique positive edge; from it and the translate the source b is recovered. These marks are neither the ordinary triangle marks (their positives form a triangle) nor the coclique shifts (the latter have a unique +2 and no positive edge). The charging and extension membership are unchanged at seven, since 3u_i,3u_j lie in L. With the negatives counted on the opposite charge, the disjoint budgets are
```
n8 <= Y2−462−44M−2S,    n15 <= W014.
```
Now M(M−1)=n1+n8+n15. Also M is an integer, so (M−50)(M−51)≥0, even when M<50 or M>51. Together these give
```
K=Y2+W014−462−144M−2S+2W446+2550 >= 0.
```
This holds in every H and on averaging. In fact no global rank-36 count or upper bound enters this specific argument, so any rank with exactly these allowed types has the same contradiction.

In the present face absence of N16,N18,N20 and the earlier charge-three minimum give the [determinant-49 scalar formula](rank36-coclique-tangent.md)
```
Y2=1000−8W014+24W022+48W333+8W024+16W335.
```
The following expression is zero by the [original full higher-moment rows](higher_moments.py) restricted to the stated three allowed unit types. All short nonunit subtractions have zero source here. The additional coordinate W448 is nonnegative and was eliminated in the original nine-row projection; no assumption about its vanishing is needed.
```
7117W000+168W014+48W022+16W024−4W123−288W222
  +96W333+56W335+62W444+4W446+3W448=0.
```
Since W000=1, substitution rewrites this exactly as
```
2K+154W014+24W335+62W444+3W448 = −545.
```
The left side is nonnegative. Run `python coclique_sidon_cut.py` beside the [upstream projected checker](rank36_three_types.py) to regenerate the row and the final equality. The residue and difference proofs work for actual labels in an extension, not just for radial multiplicities or a putative automorphism action. This is a sparse-type exclusion, not a full rank exclusion.
