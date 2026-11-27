# Proof

Put V = F₂⁸, let W(u)=∑ₓ(−1)^{F(x)+u·x} be the ordinary, unnormalized Walsh transform, and call a function *abnormal* if it is not affine on any affine four-flat. Affine coordinate changes, translations, and adding an affine output preserve this property. Adding a linear output translates the Walsh spectrum; translating the input multiplies the spectrum by a character. Thus the multiset of absolute Walsh coefficients is an extended-affine invariant. The homogeneous degree-four part, or *head*, transforms by the fourth exterior power under invertible linear substitutions (repetition of a variable lowers Boolean degree). Under an affine translation only lower terms change.

Assume for contradiction F is abnormal of degree at most four. Its restrictions to **all 510** affine hyperplanes are abnormal: a four-flat of a restriction would be a four-flat of F. By the seven-variable classification cited in the README no cubic is abnormal, so all these restrictions have degree four. In particular the eight-variable head is nonzero. The global bent case is already known, so suppose F is not bent.

## 1. What the source cover tests

For each of the 39,952 source records form the absolute Walsh histogram of its 128 Boolean evaluations and pair it with its seven-variable head. All source records have their heads in the given form representatives. For a fixed global head, the two parallel hyperplanes with normal a have the same head, namely its restriction to ker(a). Full lower-degree terms are **not** fixed. A necessary condition is only that this head and the absolute Walsh histogram occur together in the seven-variable cover up to equivalence. Overcounting possible lower terms does not exclude genuine cases.

The 12 seven-variable heads are distinguished by the following invariant. Regard a head as an alternating 4-form, volume-dualize to a 3-vector T, and for each of the 128 covectors b count the alternating-matrix rank of the bivector i_b T. The histogram of the ranks 0,2,4,6 is coordinate invariant (the determinant is always one). The direct method substitutes a pivot coordinate from a·x=0, retains just degree-four terms, and computes this invariant. Independently, dualize the ambient eight-variable head to a 4-vector U. The dual of its restriction corresponds to i_a U in ∧³ker(a): verify in any adapted basis with last covector a, then by equivariance. Contract by b modulo span(a) and compute the ranks in the ambient space; extension by an extra zero row/column preserves the rank. The two methods separately reduce the alternating matrices. All 998×255 rank profiles agree; all 12 reference profiles are distinct. Exactly 11 eight-variable leading forms have a zero restriction, and 125 others have a restriction of type 9, both of which are absent from the abnormal seven-variable cover. Hence 862 leading forms remain after this necessary test.

Write the slice histogram as (c₀,…,c₁₀), where cᵢ counts |W_slice|=4i. The complete table is generated as spectrum.txt by direct Boolean substitution plus a fast Walsh transform and, separately, subset summation plus direct multiplication by all 128 character rows. There are 14 types: 39,058 records have all values divisible by eight (E); the other 894 have **every** coefficient 4 mod 8 (O). Each slice has ∑cᵢ=128 and ∑i²cᵢ=1024 by Parseval. Some E histograms have 32 or 40, but every row obeys c₈+c₁₀≤1. The four O rows, displayed in coordinates 1,3,5,7, are precisely
```
(52,58,18,0) + s(8,-12,4,0) + t(3,-3,-1,1),    s,t in {0,1}.
```
Each E row has g=(c₂+c₆+c₁₀)/64 in {0,1}, and c₁₀≤g, c₆≤11g. No type has c₉>0. The numbers of original records per type are not used as multiplicities in any global argument; only which types are possible for each head matters.

## 2. Arithmetic constraints on a complete spectrum

Let p be mod-two parity of the unordered pairs of complementary quartic monomials in the head. Then W(u)≡4p mod 8 for every u. Indeed, the integer inclusion-exclusion formula for the weight of an XOR has coefficient (−2)^{k−1} for an intersection of k monomials. Reduce mod 4: single-monomial weights are divisible by 16; a pair matters only when its support union has size eight, requiring complementary quartics. Constants and linear terms, including u·x, do not change this count. Since W=256−2wt, the claim follows.

A k-fold discrete difference of W in distinct coordinate directions is a factor (−2)^k times a signed sum over a coordinate flat of codimension k (initial base vertex immaterial). For k=2,3 the remaining number of variables is 6,5 respectively. The restriction of F plus a linear form on this flat has even weight because its degree is strictly less than the dimension (each monomial contributes even parity). Therefore the signed sum is divisible by 4. It follows W(u) mod 16 is r+8ℓ(u), ℓ homogeneous linear on the binary coordinates: (W−r)/8 has zero second mixed differences mod 2. Also, whenever the spectrum has been normalized to a single fixed value r mod 16, Q=(W−r)/16 mod 2 has degree ≤2, since all third mixed differences vanish. This applies to r=0 when all W are divisible by 16. For p=1 translate the input by the vector specifying ℓ, and if necessary complement F; W is then 4 mod 16 everywhere. Indeed negating either odd multiple of 4 changes its residue by 8 mod 16. Now the sign of any nonzero W is fixed by its absolute value, and ∑ᵤW(u)=±256.

The weights of degree≤2 Boolean functions on eight variables belong to
```
{0,64,96,112,120,128,136,144,160,192,256}.
```
For completeness, eliminate pairs in the alternating polar form to put a quadratic in coordinates ∑_{i=1}^s x_{2i−1}x_{2i} plus an affine term, 0≤s≤4. A linear term on the radical makes it balanced, while linear terms on the displayed pairs are removed by translation. Otherwise its bias has magnitude 2^{8−s} by factorizing over the pairs, giving weights 128±2^{7−s} (for s=0, 0 or 256).

For a≠0 and a representative u modulo span(a), put A=W(u), B=W(u+a). The slice Walsh coefficients are (A+B)/2 on ker(a), and, on identifying the other coset by translation v with a·v=1, (−1)^{u·v}(A−B)/2. This follows by inserting (1±(−1)^{a·x})/2 in the defining sum. Thus the two slice magnitudes are (|A|+|B|)/2 and ||A|−|B||/2 in some order. Over all 255 directions each unordered pair of *distinct frequency positions* occurs exactly once, including pairs of equal heights.

Write z for the number of O slices. If p=1, each parallel pair gives exactly one O and one E, hence z=255; this also follows immediately after the sign normalization above (which may swap the two sides). If p=0, both sides are O when ℓ(a)=1 and both E when ℓ(a)=0; hence z=256 for nonconstant residue and zero for constant residue. Half-sums and half-differences modulo eight give these claims directly. Thus the exact category counts per head follow from the 255 labelled directions, and when needed we may try all 255 nonzero ℓ, not merely coordinate choices.

## 3. Finite certificate: unsigned spectra and head compatibility

Use units of four for heights, hₖ=#positions with |W|=4k. Parseval gives ∑hₖ=256 and ∑k²hₖ=4096. Occupied k have parity p. Any two distinct positions of heights k,j must have k+j≤20 by the slice height bound 40; in particular k≤20. Thus this is a small bounded integer enumeration, not a search over polynomials. The following conditions are necessary; they need not be sufficient.

* For p=0 the number of values not divisible by 16 is 0,128 or 256 from affine residue; the middle case has z=256. For count zero the number with odd W/16 is an allowed quadratic weight. For p=1 replace each k by signed k′ ≡1 mod 4 with |k′|=k, require |∑k′hₖ|=64, and test that the count with (k′−1)/4 odd is an allowed quadratic weight.
* Compute the exact **aggregate** histogram C₀,…,C₁₀ across all slices. For k>j enter hₖhⱼ counts at bins (k+j)/2 and (k−j)/2; for k=j enter bin k and bin 0 each with multiplicity binomial(hₖ,2). This uses only the proven unordered-pair correspondence, not an independence assumption.
* The odd bins must total z times an O pattern in aggregate: C₇=T and C₅=18z+4S−T for integers 0≤S,T≤z, C₁=52z+8S+3T and C₃=58z−12S−3T; C₉=0. The odd bins have total mass 128z and second moment 1024z. The aggregate generic flag G=(C₂+C₆+C₁₀)/64 is integral in [0,510−z], with C₈+C₁₀≤510−z, C₁₀≤G and C₆≤11G.

Two implementations enumerate the possible h. One recursively gives a count to each successively smaller admissible height; the other fixes and removes one compulsory maximum M, then partitions the remaining count and norm among heights ≤min(M,20−M). In both, at the two smallest admissible heights the remaining count and energy have at most one solution; all loops are bounded by nonnegative count and energy. The two programs compare the actual full sets of accepted 21-coordinate vectors and all aggregate bins, not just the cardinality. There are 28 vectors: p=0 gives 16 with z=0 and 11 with z=256; p=1 gives one with z=255. Only one vector is bent. The only p=1 spectrum has |W|=12,20,44 with multiplicities 150,105,1.

For each nonzero eight-variable leading form of matching p and each permitted slope, obtain the exact number n_{J,t} of t-slices (t=E or O) with seven-variable head J. For each linear functional L on a slice histogram, necessarily
```
  Σ n_{J,t} min_{row of (J,t)} L(row) ≤ L(C) ≤ Σ n_{J,t} max_{row of (J,t)} L(row).
```
Positive n with no permissible row excludes the candidate immediately. Use first the 11 bin counts and the generic flag g. This leaves 21 non-bent triples on five head indices: 130 (1), 134 (15), 168 (1), 358 (1), 563 (3). Now also use L₁(c)=c₀−c₄ and L₂(c)=c₀−2c₄. For the surviving triples on heads 134 and 563 the respective L₁ upper bounds are 210 and 546, whereas the required value is 1081. For heads 168 and 358 the L₂ upper bounds are −21504 and −21120, versus required −19032. Thus **only head 130 survives**, with slope zero, all 255 restrictions of head type 3, and h₀=48, h₄=192, h₈=16. This is an exact integer certificate. Source-order IDs are zero-based. The verifier independently reproduces the test twice; no private optimizer or trusted feasibility oracle is required.

## 4. No Boolean function realizes the final candidate with abnormal slices

Here W is divisible by 16 and Q=W/16 mod 2 has weight 192. Its zero set B has size 64 and is an affine six-flat: by the preceding quadratic normal form only s=1 without radical linear term gives 192; the size-64 level set fixes both of those two coordinates. Translating frequency space (adding a linear output) makes B a vector space. Let S⊂B be the 16 points with |W|=32. All other points of B are zeros. For any a∈B minus zero let mₐ be the number of unordered S-pairs differing by a. Each such pair gives a peak of height 32 on exactly one of the two slices normal to a, on the zero side for like signs and the other side for unlike signs. Distinct pairs give distinct slice frequencies. Each slice allows at most one such peak, so 0≤mₐ≤2 and ∑mₐ=120.

Let z₀ be the number of directions with m=0. Counting directions and pairs gives respectively 6−2z₀ and 57+z₀ directions with m=1 and 2; hence 0≤z₀≤3. Set δ(0)=0, δ(a)=2−mₐ for a≠0. Then ∑δ=6 and ∑δ²=6+2z₀. For each nontrivial character χ of B, the Fourier square of the indicator of S is
```
  (Σ_{x∈S} χ(x))² = 16 + 2 Σ_{a≠0} mₐχ(a) = 12−2δ̂(χ).
```
The character sum is even. With δ̂ even between −6 and 6, the square constraint forces δ̂∈{6,4,−2}. Write A₆,A₄ for the numbers of 6 and 4 among the 63 nontrivial coefficients. The first moment (δ(0)=0) and Parseval respectively give
```
  4A₆+3A₄=60,       8A₆+3A₄=24+32z₀.
```
Consequently A₆=8z₀−9. The only integral nonnegative solution has z₀=3, A₆=15, A₄=0. For the three missing directions M one has δ=2 on M and 0 elsewhere. Exactly 16 characters (including the trivial one) attain the maximum 6, i.e. vanish as additive linear forms on M. Their annihilator A=span(M) therefore has dimension two and M=A minus zero. All other nonzero directions occur with m=2.

No distinct points of S differ by an element of A, so S meets each of its 16 cosets exactly once. Choose a linear complement of A. Then S is the graph (x,P(x)) of a map F₂⁴→F₂². For each d≠0 in the domain and e in the codomain, difference (d,e) has precisely two unordered graph pairs, so P(x+d)+P(x)=e has four solutions. It follows every nonzero scalar component of P has all nontrivial autocorrelations zero, and hence is bent (the transform of the autocorrelation is the squared Walsh transform).

On S give a point its Walsh sign τ and put H=τ·1_S, viewed as a real function on B. For difference a outside A the two unordered peak pairs must have **opposite** sign products; otherwise both peaks would land on the same slice, forbidden. The outer slice phase changes the sign of its coefficient but not which side gets the peak. Thus the autocorrelation of H is zero on these differences, zero on A minus zero because there are no pairs, and 16 at zero. Hence |Ĥ| is identically 4 on B*. Write τ(x,P(x))=(−1)^{g(x)}. The transform on graph characters is exactly the Walsh transform of each of the four functions g+λ·P. So all four are bent, as are the three nonzero scalar components of P.

This is impossible: the map G=(g,P):F₂⁴→F₂³ would have all seven nonzero scalar components bent. For the output counts n_y its Fourier transform has n̂(0)=16 and its seven other entries are ±4 by evaluating those Walsh transforms at zero. Fourier inversion gives n_y=(16+4 times a sum of seven signs)/8, a half-integer, contradicting integrality. This eliminates the last non-bent case. Together with the bent case and the source covers this proves the theorem.
