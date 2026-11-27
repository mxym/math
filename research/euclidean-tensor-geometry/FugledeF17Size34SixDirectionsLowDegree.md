# Size 34 over F_17³: the six-direction mask, low-degree branches

Assume the [plane cap six and pencil cap seven](FugledeF17Size34PencilCapSeven.md) and, additionally, that every tight pencil has at least twelve positive profiles. The latter is [the tight-pencil result](FugledeF17Size34TightCapTwelve.md). A plane with five or six points must determine at least six directions, by the cap-two planar census. Its normal is nonuniform, so its tangent direction line in the partner's normal space is tight. By the additional prerequisite that line has at most six uniform directions. Thus the plane determines exactly six directions, equal to all the uniform normals in that tangent pencil. The [planar mask certificate](verify-fuglede-f17-size34-six-directions-planar.js) enumerates the nine triangle-normalized five-point sets and three six-point sets determining at most six directions. All their direction complements give the same projective orbit of twelve nonuniform directions,
```
[0,1,2,3,4,5,6,7,8,9,11,15].
```
This narrows the test required for either a five- or six-point affine plane to that one orbit. The corresponding projection of the other member is injective: a difference in the nonuniform normal direction would contradict spectral orthogonality. Hence its projected occupancy f in the Radon formula is Boolean, and
```
Σ_i g_i(x+s_i y) = 22 + 17 f(x,y),    Σ_i 17w_i=255.
```

## Highest degree at most seven

A degree-six profile has weight two, while degree at most five is absent. Twelve positives therefore cannot all have degree six. With maximum at most seven, every positive weight is one or two, from the [verified degree-six and degree-seven univariate catalogue](verify-fuglede-f17-size34-low-profiles.js) restricted to peak six. Thus the weights must be 1^9,2^3. The surviving monic centered septics are
```
[2,1,0,7,0,7,0,1] (weight one),
[3,0,9,3,8,12,0,1], [6,16,0,8,14,6,0,1] (weight two).
```
Orbits under change of argument give these counts at every leading value. Each sextic is of weight two and its unique centered representative at each leading value comes from the two complete degree-six orbits.

For fixed slopes let λ_i=1/∏_{j≠i}(s_i−s_j). The homogeneous relation on degree-r coefficients c_i is equivalent to c_i=λ_i P(s_i) for a polynomial P of degree ≤10−r; this follows from Lagrange moment sums and the dimension of the rectangular Vandermonde kernel. For r=7 use a normalized cubic P (common dilation exhausts all nonzero scales), leaving 5,220 choices. Two genuine septic centers can be made zero by the same affine translation. Then the r=6 kernel polynomial is divisible by both corresponding linear factors, leaving an arbitrary quadratic. All 17³ choices are tried, rejecting only if a putative lower sextic has zero leading coefficient. There are 24,601,160 admissible center assignments.

Among genuine septics, each value of degree six fixes its translation center. Changing its centered profile from weight one to one of the two weight-two choices changes the degree-five coefficient by a known value independent of its center (the common shift contributes the same binomial term). Any lower sextic, in contrast, can contribute an arbitrary degree-five coefficient, setting its center. Thus for fixed degree-seven leading choices, [the verifier](verify-fuglede-f17-size34-six-directions-septic.cpp) eliminates the sextic columns in the degree-five equations and tabulates the possible syndromes of the requisite remaining weight-two septics. The test of all centers leaves 3,088 degree-five-compatible choices, none passing the lower congruences. In particular the low-degree branch contains no physical grid.

## Highest degree eight

A genuine octic requires at least ten genuine degree-eight profiles by Vandermonde independence, allowing at most two lower ones. The [octic verifier](verify-fuglede-f17-size34-six-directions-octic.cpp) enumerates all centered peak-six profiles of degrees six through eight by interpolation. The full counts are 16,48,272. For each leading and penultimate coefficient the bank includes all translated profiles of matching exact degree. The degree-eight leading polynomial is quadratic in the barycentric representation. It uses one projective normalization and each of eight common scales modulo eighth powers, totaling 2,456 choices. Translating to kill two genuine octics' degree-seven coefficients leaves a linear polynomial after factoring out those two points in the degree-seven barycentric relation. There are 709,784 total lead-and-center choices. At a zero degree-eight coefficient, the degree-seven coefficient selects either a translated septic of that leading value, or an arbitrary translated sextic if it is zero.

For each subsequent degree r≤6, use the barycentric interpolation relation to determine all column coefficients from any 11−r of them. The verifier enumerates all free values and retains only compatible coefficient choices in each individual profile list; it never discards a list unless the sum of the lowest remaining weights exceeds 255 in units of 1/17. At degree zero the affine target is 22 modulo 17; this is handled by subtracting 22 in one coordinate before fitting the homogeneous kernel. At a leaf both the total weight and the Boolean grid are checked. There are 971,106 paths after degree six, 338 after degree five, and none after degree four. Thus the true octic case has no physical grid either.

## Highest degree nine

A genuine nonic gives at least eleven genuine degree-nine profiles, with at most one lower profile. The degree-nine homogeneous kernel is represented by a linear barycentric polynomial. After a common dilation (ninth powers permute the field) its projective root parameter has 18 choices, including infinity for the constant polynomial. The [stabilizer verifier](verify-fuglede-f17-size34-six-directions-symmetry.js) checks that projective automorphisms preserving the twelve slopes act on these in two orbits, represented by 0 (a lower profile occurs) and 10 (all nonics). Its verification includes the rescalings of the leading coefficients induced by the change of coordinates; a common dilation normalizes the remaining scalar. Translation then removes two nonic penultimate coefficients, and the degree-eight barycentric polynomial has one free scalar after factoring its two zeros.

The [nonic verifier](verify-fuglede-f17-size34-six-directions-nonic.cpp) generates the same lesser profile banks together with all 3,008 centered cap-six nonics, then builds a trie of translated profiles indexed by coefficient prefixes. It prunes only by the exact minimum remaining total scaled weight, and interpolation checks each homogeneous coefficient. At constant degree the necessary Boolean origin cell restricts the integer sum of constants to 22 or 39; each completed candidate would also be checked at all 289 cells. Compile with `g++ -O3 -std=c++17` and run with arguments `0` and `10`. The degree-seven and degree-six counts are 828,259 and 1,339,025 for 0, and 1,059,551 and 1,047,614 for 10 (two paths reach degree five in the latter case). Both leave zero final candidates.

The sole remaining test for this mask has genuine degree ten. This note alone does not reduce the plane cap.
