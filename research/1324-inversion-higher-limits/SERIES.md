# All five tertiary generating functions

Let C_p(y) be the **previously known** fixed-inversion primary limit series of Av(1324,p), in the notation of [CLÚV, Corollary 5.8 and Theorem 5.10](https://arxiv.org/html/2604.01143v2#S5). Let E(y)=∏_{i≥1}(1+yⁱ) be the distinct-part series. With j=k−n+1 unchanged, the tertiary limits from SPLIT.md satisfy

|p|∑ A_j y^j|
|---|---|
|2143|−2|
|2413|3 C_p(y)|
|2431|y C_p(y)|
|3412|2y C_p(y)|
|4231|2y² E(y)²|

For 2143 the only nonzero profile pair is empty/empty, by its multiplicity one and its verified empty/empty value. For the next three rows, all admissible profiles have the same contribution S(y); the endpoint pair simply supplies its total inversion weight. Since each indicated p is indecomposable, CLÚV Corollary 5.8 identifies this product of the left and right endpoint generating functions with C_p(y). In either factor the empty decoration is the unique weight-zero case (CLÚV use the unique singleton indecomposable at inversion zero). In particular C_2413 is the square of the unrestricted partition series; the other two primary series are explicitly given in CLÚV Theorem 5.10.

For 4231 the same finite menu has the following entrywise form: the coefficient of y² in S(y) equals the number of h among 231,312 such that h is absent on the left **and its inverse is absent on the right**. The accompanying verify_series.py checks every formal pair rather than inferring this from unlabelled multiplicities. For fixed h, avoiding h or its inverse automatically excludes 4231 because 231 and 312 are both its subpatterns. Thus the contribution is the product of the independent generating functions of the empty or nonsingleton indecomposable members of Av(132,h) and Av(213,h⁻¹). All four choices give E(y): inverse fixes 132 and 213 and exchanges 231 and 312; reverse complement exchanges 132 with 213 and 231 with 312, and both operations preserve size, inversion count and indecomposability. The distinct-part enumeration for Av(213,231) is attributed to A. F. Franklín in the proof of CLÚV Theorem 5.10(3); it is used here, not proved anew. Adding the two equal products gives the final row. This appendix does not determine the secondary constants for the six other representatives.
