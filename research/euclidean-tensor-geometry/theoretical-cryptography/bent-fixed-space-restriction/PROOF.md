# Sharp degree-four failure and an exact period-four fold test

All vector spaces are binary unless indicated otherwise. We use the unnormalized Walsh transform
`W_f(ξ)=Σ_x (−1)^(f(x)+ξ(x))`, indexed by linear functionals. A Boolean function on dimension N is bent when N is even and every |W_f(ξ)|=2^(N/2); the zero-dimensional convention is allowed. Degree means square-free algebraic normal form (ANF), with products and function values over F₂. Write D_a f(x)=f(x+a)+f(x).

## 1. The known cubic transfer, and a sharp quartic failure

For orientation we give the short transfer proof from Vono, ePrint 2026/2844, Lemma 3.2 and Corollary 3.3. If T has odd order m, the linear map Σ_{i=0}^{m−1} T^i is the projection to U=Fix(T) along T-invariant E=im(T−I). In fact its image is fixed, its value on U is the identity, and it annihilates im(T−I); rank-nullity gives the decomposition. In particular T−I is invertible on E.

For a T-invariant quadratic q (degree at most two), subtract q(0) so that its polar identity is q(u+e)=q(u)+q(e)+B(u,e), with alternating B. The invariance of B gives B(U,(T−I)E)=0. Thus q splits across U⊕E. On the radical of B|_E, q is linear and T-invariant; the radical is T-invariant and T−I is invertible there, so this linear restriction vanishes. The squared character sum on E is therefore |E| times the size of the radical: expand its square, put the difference of the two points in the outer sum, and use character orthogonality. In particular, the sum on E is nonzero. The character sum on U⊕E factors, so q is balanced iff its restriction to U is balanced.

For invariant bent f of degree at most three, D_a f is balanced and quadratic for each nonzero a∈U and is T-invariant. Hence every nonzero derivative of f|_U is balanced. These derivative tests characterize bentness by Fourier transform of the autocorrelations (equivalently |W|² is the transform of the derivative character sums). This is the credited cubic transfer.

**Theorem 1 (sharp boundary).** There is an eight-variable degree-four bent f, invariant under a linear map T of order three, with nonbent restriction to Fix(T). It remains possible for odd T when T is the coordinate permutation taking a repeated-block fixed space in n=3d variables, for every even d≥4. In this latter assertion f is invariant under that permutation, not asserted invariant under the full n-cycle. Degree four and ambient dimension eight are minimal for failure of odd-order fixed-space bentness.

**Construction.** Let U and V both be the additive four-dimensional spaces F₄². Use the five F₄-lines L_0,…,L_4 of U and K_0,…,K_4 of V, with indices read modulo 5 and any fixed labeling. They each partition the nonzero vectors into triples. Write Δ_U,Δ_V for indicators of zero on these spaces, and set
`s_j=1_{L_j}+1_{L_(j+1)}`. This is the indicator of the nonzero vectors in the two indicated lines (at zero the two indicators cancel). Take
```text
 f(u,v)=Δ_U(u)+Δ_V(v)+Σ_{j=0}^{4} s_j(u)1_{K_j}(v).        (1)
```
Line indicators have degree at most two, being indicators of subspaces of codimension two; zero indicators have degree four. At v=0 the sum of the s_j is zero, so f(u,0)=1+Δ_U(u), of degree four. Thus f has degree exactly four. Let T(u,v)=(u,ωv) for an element ω of order three in F₄. Every K_j is stable under scalar multiplication, and Fix(T)=U×{0}. Its restriction 1+Δ_U has Walsh value −14 at zero and value 2 at each nonzero frequency, so is not bent.

**Bentness.** The character sum over the nonzero vectors of a four-space line is 3 if the character is trivial on that line, and −1 otherwise. For a nonzero functional on a four-space exactly one of the five lines has trivial character there: the five orthogonal dual lines have dimension two each, intersect pairwise only at zero, and partition the 15 nonzero functionals. For each j put S_j=s_j⁻¹(1). The character sum on S_j at a nonzero functional is ±2 (sum of either 3 and −1, or −1 and −1), and at zero is 6.

At u=0 the function of v in (1) is 1+Δ_V. At u≠0 its value is 1 at v=0, and at v∈K_j∖{0} it equals s_j(u). Exactly two of the s_j are one for any given nonzero u. Summing over v first, the partial transform at frequency zero is −14 at u=0 and 2 at other u, namely 2−16Δ_U. At a nonzero frequency λ on V, with λ trivial on K_j, the partial transform is 2 at u=0, and at u≠0 it is 2−8s_j(u): the v=0 sign is −1, the five nonzero-line signs sum to 1, and the exceptional line contributes a correction of four times its sign. Thus the partial transform is 2−8s_j on all U. Its Walsh transform over U has magnitude 16 at zero (32−8·6) and at nonzero functionals (the S_j character sum is ±2). The transform of 2−16Δ_U likewise has magnitude 16 everywhere. This proves bentness with no search.

For the repeated-block assertion, add a separate nondegenerate quadratic on d−4 extra fixed binary coordinates, and add d−2 extra F₄ coordinates, each with T acting by multiplication by ω and quadratic q(z)=1_{z≠0}. The fixed quadratic can be a sum of products of disjoint pairs; the other quadratic is nonsingular since its 4-point character sums are ±2. Direct sums multiply Walsh transforms, preserve the maximum degree, and preserve failure on the fixed space (its transform multiplies the nonflat |14|,|2| values by the same positive factor). The enlarged T has d fixed binary directions and d moving irreducible two-dimensional spaces with minimal polynomial x²+x+1. This is the module of d disjoint coordinate 3-cycles: each triple splits into its fixed line and its sum-zero plane where the same polynomial acts. Choosing equivariant linear bases conjugates it to the d-step cyclic coordinate rotation on 3d coordinates. Its fixed space consists exactly of three repetitions of a d-bit block.

For minimality of ambient dimension, a bent function on 2h≥4 variables has degree at most h. Indeed, on any coordinate subspace of dimension j>h its sign sum is 2^(j−h) times a sum of 2^(2h−j) signs, by character orthogonality. This integer is a multiple of 4, even when j=h+1 as then the number of signs is even. The weight on that subspace is therefore even, so its corresponding ANF coefficient vanishes. Dimension two trivially has degree at most two. Thus no failure can occur in fewer than eight variables by the known cubic transfer.

## 2. Period-four folds under a full cyclic symmetry

We first isolate the elementary orbit congruence used here. Let T have order ℓ^a for ℓ odd prime, a≥1, on dimension N even, and let d=dim Fix(T) be even. Put U=Fix(T) and E=im(T−I) as above. For g=f|_U and a functional ξ on U, extend ξ to ξ̃ vanishing on E, which is then T-invariant. If f is T-invariant, every nontrivial T-orbit contributes a multiple of ℓ to W_f(ξ̃). Therefore
```text
 W_g(ξ) ≡ W_f(ξ̃)   (mod ℓ).                              (2)
```
All nonzero vectors of E lie in orbits divisible by ℓ so 2^(N−d)≡1 modulo ℓ. If f is bent, this means W_g(ξ)≡±2^(d/2) modulo ℓ: the factor 2^((N−d)/2) has square 1 modulo ℓ, and hence is ±1. If every Walsh coefficient is divisible by 2^s for an integer 0≤s≤d/2, divide by 2^s modulo ℓ. If ℓ>2·2^(d/2−s), all admissible integer representatives have absolute value at least 2^(d/2−s); Parseval gives equality at every frequency and g is bent. This simple sufficient condition is not a replacement for sharper large-dimension modular rigidity theorems.

**Theorem 2 (four-variable fold).** Let f be rotation-symmetric and bent on n=4m coordinates, m=ℓ^a for ℓ an odd prime and a≥1. Let g(u)=f(u,u,…,u) where the four-bit block u is repeated m times. Then:
- If ℓ≥5, g is bent.
- If ℓ=3, g is either bent, or differs at one point from a rotation-invariant affine function on the four bits. In the second case the exceptional point is 0⁴ or 1⁴ and |W_g| is 14 at a single frequency and 2 elsewhere.

The fold g is invariant under the cyclic shift of its four coordinates. Apply (2) to the fourth power of the original n-cycle, which fixes exactly the period-four subspace. If ℓ≥5, all Walsh coefficients on four bits are even, so s=1 gives ℓ>4 and bentness. If ℓ=3, first note that on four bits each Walsh coefficient is congruent to −2 wt(g) modulo 4 (adding a nonzero linear function flips eight truth-table positions, preserving parity of the weight). If the weight is even use s=2; then ℓ>2 suffices. Otherwise all Walsh coefficients are 2 modulo 4, and (2) excludes multiples of 3. Possible magnitudes ≤16 are consequently 2, 10 and 14.

Parseval gives Σ|W_g|²=16². Relative to sixteen magnitudes 2, the excess energy is 192. Magnitudes 10 and 14 cost 96 and 192, respectively. There can be two magnitudes 10 or one 14. The first is impossible: for distinct frequencies ξ,η,
`|W_g(ξ)|+|W_g(η)|≤16`. To see this, add the transforms with the signs that make both nonnegative; the signed characters agree at eight points and cancel at eight others. Thus one Walsh coefficient has magnitude 14, meaning that g has Hamming distance one from the corresponding affine function with the indicated sign. This affine function is unique (distinct affine functions on four bits differ in at least eight places). By rotational symmetry the affine function and the exceptional point must each be rotation-invariant. The invariant affine functions have constant or total parity as their linear part, and the only fixed points of the four-cycle are 0⁴ and 1⁴. Conversely, either any bent function or any single-point modification of an affine function on four bits has the requisite mod-3 residues. This converse is a statement about the possible modular spectra on four bits, not attainability as folds of fully cyclic bent parents.

### 2.1 Exact ANF orbit coefficients

For any rotation-symmetric f on n=4m, m odd, let an ANF support orbit mean the cyclic shift orbit of a nonempty monomial support, included when its coefficient is one. Define Q as the parity of the number of included odd-length support orbits. Define B as the parity of the number of included support orbits with length 2 modulo 4 and whose supports lie entirely in one parity of indices (all even or all odd, possibly swapped by rotation).

Let [0123] denote the coefficient of the four-variable product in g, and [02] the coefficient of the monomial u₀u₂ (equal by rotation to that of u₁u₃). Then
```text
 [0123]=Q,   [02]=B.                                        (3)
```
To see this, for a support S let π(S) be its nonempty set of residues mod 4. The cyclic action maps the original orbit onto the four-coordinate orbit of π(S). Every image support occurs |orb(S)|/|orb(π(S))| times. In restriction powers of a Boolean variable reduce to that variable, so this multiplicity is reduced modulo 2. If the original orbit length is odd, shifting by that length preserves S and acts transitively on residues mod 4, forcing π(S) to contain all residues. The image orbit then has length one. Conversely, a full-residue image contributes to [0123] exactly if the original length is odd. For [02], its image orbit has length two. Thus the original length must be 2 mod 4 to contribute, and S must use one parity only; when these conditions hold translation by the original orbit length shifts residues by 2, so both residues of that parity do occur. This proves (3).

A four-variable cyclic bent function is quadratic by the degree bound, with [02]=1. To check the latter, if R is the cyclic shift matrix, its quadratic polar matrix has the form α(R+R⁻¹)+βR², where β=[02]. When β=0 the all-ones vector is in the kernel. When β=1 the matrix is invertible: factor R², and the remaining correction to I squares to zero in characteristic two. A quadratic is bent iff its polar has trivial radical by the balanced derivative criterion. In the other case from Theorem 2, a one-point flip of an affine function has [0123]=1, by its odd weight. The coefficient [02] depends on which fixed point is flipped: 1_{u=0} has every ANF coefficient one, including [02], whereas 1_{u=1} is just the fourfold product. More precisely,
| Fold | [0123] | [02] |
|---|---:|---:|
| Bent | 0 | 1 |
| Flip at 0⁴ | 1 | 1 |
| Flip at 1⁴ | 1 | 0 |

(4)
Here affine terms do not affect the two displayed coefficients.

**Homogeneous quartic specialization.** For degree-four supports, stabilizer size divides four, since each orbit of a stabilizer acting by translations on a nonempty support has size exactly that stabilizer. The odd orbit length case therefore means a quarter-turn-stable support, exactly {i,i+m,i+2m,i+3m}. These form one monomial orbit, and Q is its coefficient. The length-2-mod-4 case means stabilizer size two, so the support is a union of two antipodal pairs, but not a quarter-turn support. B counts the included such orbits whose two bases have the same parity; parity is well-defined because the antipodal shift is 2m, even. Thus for ℓ≥5 any hypothetical homogeneous quartic bent f has Q=0 and B=1. For ℓ=3 a hypothetical such f either has these same parities and a bent fold, or has Q=1 and the exactly described exceptional near-affine fold with B as in (4). These are necessary tests, not nonexistence or attainability for general n.

## 3. A balanced derivative with fully cyclic symmetry

Here is a separate obstruction to route-by-route generalization of Vono Lemma 3.2. Unlike Theorem 1's bent example, the quartic here is invariant under the entire coordinate cycle; it is not bent.

For x∈F₂^12, form u_i=x_i+x_(i+4)+x_(i+8) for i=0,…,3, and w_j=Σ_{i≡j (mod 3)}x_i for j=0,1,2. Put v=(w₀+w₁,w₁+w₂) and H(v)=1_{v≠0}. Under cyclic shift, u is cyclically permuted, and v is transformed by an invertible linear map induced by the cyclic permutation of w (the kernel of the difference map is the constant triples). Thus H is invariant. The map x↦(u,v) is surjective: on repeated four-block inputs it gives all u and v=0, and weight-two vectors with two nonzero coordinates in the same residue class mod 4 give u=0 and generate both v coordinates. On the period-four subspace, v=0 because all three residue classes mod 3 see all four positions of the block.

Let P(u)=u₀u₂+u₁u₃ and define F(x)=1_{u=0}+P(u)H(v). It is fully rotation-invariant of degree exactly four (restriction to v=0 is the degree-four zero indicator). For the all-ones direction J, u↦u+1⁴ and v is unchanged. Therefore
```text
 D_JF(x)=1{u∈{0⁴,1⁴}} + (u₀+u₁+u₂+u₃)H(v).              (5)
```
On the 8 even-parity u, the sign sum over u of the first term is 4; there are 4 choices of v. On the 8 odd-parity u, the first term vanishes and the sign sum of H across v is −2. Total sign sum is 4·4+8·(−2)=0, and surjectivity gives equal fiber weights. Thus this invariant cubic derivative is globally balanced. On the period-four subspace it is an indicator of two of the sixteen inputs, not balanced. The other coordinates unused by F after the rank-six map give nonzero constant-zero derivatives, so F is not bent. This example concerns only the balance-transfer step, not a homogeneous quartic bent counterexample.
