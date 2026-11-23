# A quadratic norm-18 population bound without any support hypothesis

This uses neither the two-type hypothesis, a Hoffman coclique, the absence of Fano markings, nor any symmetry. Fix a maximal isotropic subgroup H at seven and work in its determinant-49 extension. Its residual seven-plane is anisotropic with bilinear form 4I. A field in the following argument is **H-eligible**; its class always means its class in this quotient plane, and its norm the ordinary squared norm on its graph coordinates. Let N be the number of oriented neutral norm-18 fields, V the number of oriented neutral norm-24 fields, and Z the number of oriented neutral norm-28 fields of zero class in this plane. Put n=N/8, which need not be an integer. Then
```
(12+4√2)n² ≤ 84n + 84Z + (49√2/2)V .
```
The coefficients on Z and V are respectively 7R and 7K√2/2 with the unconditional R=12,K=7. If norm 16 is absent take R=4; if norm 20 is absent take R=8,K=1; if both are absent take R=2,K=1. These allowances need only the corresponding absences for H-eligible true fields.

Use the four signed classes β_i=(1,0),(0,1),(2,2),(2,−2) in 4I. Let n_i and A_i be the size and actual vector sum in class i. The total s=sum_i n_i=N/2 by antipodality. Distinct non-antipodal norm-18 fields have absolute product at most 10: a larger value would give squared distance at most 14 after a sign choice, forbidden by the unconditional [norm-18 separation](../short-shell-moments.md#bounding-the-norm-18-alternative). In particular distinct fields in one signed class have product only 4,−3,−10.

**How many source pairs give one norm-28 line?** A within-class unordered dot-four pair gives by subtraction the antipodal line of a zero-class norm-28 field. Fix its orientation z and one of the possible four projective source directions. Every representation counted along that direction can be uniquely written z=t_i+u_i with t_i in the chosen signed class and u_i in its negative. For different indices t_i·t_j must equal 4: t_i·u_j=14−t_i·t_j since t_i·z=14, while the two other candidate values would give 17 or 24, impossible (equality with \(u_j\) is ruled out by opposite nonzero residue classes, and antipodality would give a negative dot). Thus h_i=t_i−z/2 has diagonal 11 and off-diagonal −3 in its own direction. If m labels occur there, the norm-square of their sum m(14−3m) bounds m≤4.

Between perpendicular source directions all h_i·h_j vanish: t_i·t_j and 14−t_i·t_j are both at most 10, and the former is a multiple of 7, hence equal to 7. Between any two nonperpendicular directions the h-products have a single fixed sign and absolute value one: these t-products lie between 4 and 10 and are congruent to a fixed ±1, hence all are 6 or all are 8. For two such nonempty direction groups of sizes m,k, Cauchy applied to the two sums of h_i gives
```
(14−3m)(14−3k) ≥ mk .
```
If m=4 then each of its two nonperpendicular groups has at most two and its perpendicular group at most four: at most 12 in total. If all sizes≤3, the same bound is immediate. Thus over the four signed classes together the number of unordered dot-four pairs is at most 12Z/2. If norm 16 is absent, repeated sources in one direction would give 10 as t_i·u_j and hence a forbidden norm16 difference, so each direction contributes at most one. If norm 20 is absent, distinct nonperpendicular groups cannot both occur since one of the two cross products 6,8 equals 8, giving a forbidden norm20 difference. This proves all stated R bounds.

**The norm-24 sum.** A pair of distinct source directions with absolute product six determines a norm-24 line by choosing signs to sum with product −6. For an oriented representative z' its unordered source residues are determined: each source has norm four, product 12 with [z'], and the corresponding affine line meets an anisotropic circle in at most two points. The two source classes are distinct, since 24 is not 4·18 modulo seven, and are nonopposite since [z'] is nonzero. Orient the representations consistently with t_i in one fixed source class. For any two different ones, t_i·t_j=4: the other possibilities −3,−10 give t_i·(z'−t_j)=15,22. As above, centered sources t_i−z'/2 have diagonal 12 and off-diagonal −2, implying at most seven by taking the sum. If norm20 is absent the cross product 12−4=8 also cannot occur, forcing at most one. Unoriented source pairs are unchanged on replacing z' by −z' and there is no extra multiplicity from another pair of residue directions. Thus E6, the number of exceptional absolute-six pairs across the four nonperpendicular blocks, obeys E6≤KV/2.

**Combining the two bounds.** Let e count all the within-class dot-four pairs. Direct expansion, dropping only the nonpositive correction −14 for each within-class dot-minus-ten pair, gives
```
T=sum_i||A_i||² ≤ 14e+21s−3 sum_i n_i² .
```
Write p=n_1+n_2 and r=n_3+n_4. After the 1,1,1,−1 sign correction on the four cross blocks their products are 1,−6,8, so the ordinary centroid expression is
```
(A_1+A_2)·A_3+(A_1−A_2)·A_4 = pr−7E6+7E8 ≤ T/√2 .
```
Here E8 is nonnegative and may be dropped in bounding pr from above. Combining yields
```
3 sum_i n_i² +√2 pr ≤ 7R Z +21s+(7K√2/2)V .
```
No equality of the four n_i is needed. Indeed the left side is at least (3/2)(p²+r²)+√2 pr, which at fixed s=p+r is minimized at p=r, giving (3+√2)s²/4. Substitute s=4n to conclude.

**Averaging safely.** Each determinant-49 extension obeys this inequality, so Jensen also gives exactly the displayed inequality with n,Z,V replaced by their extension means and the same universal R,K (or conditional R,K under graph-wide absences). The averaged n is W018, equivalently N18(graph)/(7^((44−rank)/2)+1). The averaged V is 8W024. The averaged Z is W028, the mean neutral count in the zero class of the selected *residual plane*, not in general the count Z0 in the original full discriminant space. At rank 42 there is no distinction between these two zero classes. This note gives a mass constraint, not an additional rank or support exclusion.
