# The exact signed blocker spectrum of E6

For the 72 signed roots Φ of E6, normalized to squared norm two, let B(x)={r∈Φ : x·r>1}, where x is a **nonroot** of squared norm two. There are **357,444 distinct signed sets** B(x), in **33 orbits** under the full root-system automorphism group. The set's size does not determine its type. All counts include boundary directions on the sphere, and do not count chambers or connected components of the sets of directions.

|Size|Upward ideals in dominant chamber|Ideals modulo diagram|Realizable orbits|Distinct signed sets|Lower-bound exclusions|Upper-bound exclusions|
|--:|--:|--:|--:|--:|--:|--:|
|5|3|2|1|432|0|1|
|6|3|2|2|15,120|0|0|
|7|4|3|3|30,240|0|0|
|8|6|4|4|47,790|0|0|
|9|7|4|4|69,120|0|0|
|10|8|5|5|88,560|0|0|
|11|10|6|6|66,384|0|0|
|12|12|7|3|23,760|4|0|
|13|14|8|2|10,800|6|0|
|14|16|9|1|4,320|8|0|
|15|19|11|1|864|10|0|
|16|22|13|1|54|12|0|

## Why this exhausts the sphere

By the [sharp blocker range and chamber-orbit lemma](KissingE6GlobalMaskCapacity.md), every B(x) has size 5–16. After moving x to a dominant chamber, B(x) is an upward ideal in the coefficientwise order on positive roots. Two such chamber ideals can represent the same full orbit only if they agree up to diagram reversal: the sum of an ideal's roots is dominant and each simple reflection fixing the sum fixes the ideal itself. Successively adding any maximal remaining root generates precisely all upward ideals; taking the diagram quotient leaves 74 candidates.

Let G be the simple-root Gram matrix and w the vector of simple inner products of x. For root coefficients r the scalar product with x is rᵀw and the squared norm of x is wᵀG⁻¹w. We establish realizability or impossibility as follows.

1. **Realizable:** The [verifier](verify-kissing-e6-exact-blocker-spectrum.js) supplies 33 explicit nonnegative integer directions w. Scale each to squared norm two. Comparing 2 det(G)(rᵀw)² with wᵀadj(G)w, including the sign of rᵀw, determines its blockers exactly. The verifier also checks that equality in the root Cauchy–Schwarz bound never makes a witness a root and that all 33 masks are inequivalent.
2. **Forty exclusions with inheritance:** For candidate C, consider closed chamber and lower inequalities Aw≥b, formed by wᵢ≥0 and rᵀw≥1 on the minimal roots of C. A subset of independent rows J gives K=AⱼGAⱼᵀ, c=K⁻¹bⱼ≥0 and bⱼᵀc≥2. Cauchy–Schwarz gives wᵀG⁻¹w≥bⱼᵀc≥2. If the blocker inequalities are strict, shrinking w slightly preserves the closed inequalities, so the original norm must be **larger** than two. In fact a signed copy of such a C cannot even be contained in some larger actual mask; the folding lemma below removes the apparent chamber restriction.
3. **One five-element exclusion:** Close the exact inequalities for C by including rᵀw≤1 for maximal complementary roots. If a coordinate has no upper constraint from these, impose wᵢ≤2, valid for norm-two x. This polytope is bounded. Enumerate all vertices by six independent active hyperplanes, solving by exact determinants. All have norm at most two; every vertex of norm precisely two fails to give C as an exact nonroot mask. Strict convexity of the squared norm excludes any nonvertex as an additional norm-two point. This last exclusion concerns an **exact** mask and does not automatically exclude a strict superset.

**Folding lemma for the forty lower exclusions.** Let C be an upward ideal and suppose x·r>1 for every r∈C, without any chamber assumption on x. If x·αᵢ<0, reflect x in that simple wall. In each two-element orbit of the reflection on roots, either both members belong to C (their inequalities are swapped), neither does, or just the larger member r belongs to C. In the last case r·αᵢ>0, so its product with x *increases* under the reflection. The pair {−αᵢ,αᵢ} obeys the same rule. Thus the inequalities for C persist. Chamber folding terminates in the finite Weyl orbit: each applied reflection strictly increases the product with any fixed strictly dominant vector. The dominant representative now contradicts the lower certificate. Conjugate to get the same conclusion for every signed copy of C.

Finally generate each realized signed orbit using the six simple reflections and the diagram involution, deduplicating signed subsets of the 72 roots. The sum of orbit sizes yields the signed-set count in the table.

**Application to search.** This is an exact catalog of individual shapes, not a sufficiency test for putting several outsiders in a kissing configuration. The forty lower exclusions allow early pruning of entire upward families via the folding lemma; alternatively one can test membership directly in these 357,444 realized sets. No unrestricted kissing bound follows solely from this count.
