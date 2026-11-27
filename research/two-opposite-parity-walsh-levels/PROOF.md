# Two spectral levels of opposite parity

## 1. Conventions and theorem

Write z∈{−1,1}^n and χ_T(z)=∏_(a∈T)z_a. The real character expansion is unique; a function has level ℓ if at least one coefficient of a χ_T with |T|=ℓ is nonzero. Spec(f) is the set of such levels, not a set of individual frequency vectors. The adjacency eigenvalue for level ℓ is n−2ℓ, so this is Valyuzhenich's indexing of eigenspaces U_ℓ(n). Write |supp f| for the number of nonzero truth values.

Let n≥1 and 0≤i<j≤n with j−i odd. Then the minimum of |supp f| over real f with Spec(f)={i,j} is
```
     2^(max(n−i,j)−1) = 2^(n−min(i,n−j)−1).                   (1)
```
If i+j≤n, all extremizers have the form
```
     f(z) = c ∏_(a=1)^i (z_(u_a)+ε_a z_(v_a)) [1+g(z_F)],    (2)
```
where c is a nonzero real number, the coordinate pairs (u_a,v_a) are disjoint, ε_a∈{−1,1}, F consists of all unpaired coordinates, and g:{−1,1}^F→{−1,1} has pure real Walsh degree j−i. Empty products are allowed. If i+j>n, the extremizers are the full-parity multiples of (2) for (n−j,n−i). The formulas also agree at i+j=n; see Section 4.

Valyuzhenich's §6 Problem 5 asks for the answer at (i,j)=(0,3), for every n≥3. There (1) says 2^(n−1). Indeed, in that case f=c+f_3, so f(z)+f(−z)=2c≠0, and f=1+z_1 z_2 z_3 attains half the cube. Formula (2) states exactly that every minimizing function in this case is c(1+g) for a pure degree-three sign function. We do not assume g is a single character.

## 2. Known single-level equality case, with an elementary derivation

The fact needed below is: for 0≤d≤n/2, nonzero f of pure level d has support at least 2^(n−d), with equality exactly for a nonzero scalar times d disjoint signed coordinate pair factors and no other factors. This is Valyuzhenich [2023], Corollary 1(2), including d=0. We record an elementary proof via the broader minimal support case of his Theorem 2(2) at i=0; it is a proof ingredient, not claimed as new.

A nonzero f of real Fourier degree at most d, for 0≤d≤n, has at least 2^(n−d) nonzero values. For induction on n, the two slices f_- and f_+ across the last variable have degree at most d; their difference h=f_+−f_- has degree at most d−1. If both are nonzero and d≤n−1, individually they have at least 2^(n−1−d) nonzero values. If just one is nonzero, it equals ±h and the induction bound at degree d−1 is 2^(n−d). The cases d=0 and d=n are immediate (constant and nonempty support, respectively).

For the equality analysis of this degree bound, call a signed block a set B of b coordinates constrained to z_a=η_a u for a common parameter u∈{−1,1}. Define P_B on those coordinates to be u^(b−1) when the block constraints hold and 0 elsewhere. If b=1 this factor is 1 everywhere. Direct character sums give its nonzero Fourier coefficients on precisely the subsets of B whose cardinality has parity b−1, with maximum level b−1; all such coefficients are nonzero. Multiplying on its support by u instead gives maximum level b and the other parity of levels. These statements follow by evaluating a character at the two nonzero points: its coefficient is 2^(−b)∏_(a∈T)η_a times Σ_(u=±1)u^(b−1+|T|), or the same sum with one more power of u. Also, a single prescribed-coordinate indicator has nonzero levels 0 and 1.

Every minimum-support f of degree at most d is a scalar product of such signed block functions and indicators of prescribed coordinate values, partitioning the coordinates into those blocks and fixed coordinates. Here is the equality induction. For d=0 use singleton free blocks; for d=n use one fixed-coordinate indicator per coordinate of the sole support point. If one slice vanishes, apply induction to the other at degree d−1 and include the new fixed-coordinate indicator. If both slices are nonzero and equal, apply induction to either at degree d in n−1 coordinates and add a singleton free block. Otherwise h is nonzero and
```
  2^(n−d) ≤ |supp h| ≤ |supp f_- ∪ supp f_+|
            ≤ |supp f_-|+|supp f_+| = 2^(n−d).
```
All inequalities are equalities. In particular the slices have disjoint supports, h is minimum-support at degree d−1, and induction writes it as the specified scalar product. On its support let b(u)∈{0,1} indicate that f_+ is the nonzero slice, in the independent block parameters u. Thus f_+=h b, with the product defined as 0 outside support.

For such an h of degree d−1, multiplying by any nonzero function b of the block parameters increases the degree by exactly deg(b). To see this, expand b in characters of those parameters. A chosen block factor is either P_B or uP_B, with opposite Fourier parities, and the fixed-coordinate factors do not change. Distinct block character indices therefore yield disjoint Fourier frequency sets, with highest degree d−1 plus the chosen character's size, so those top levels cannot cancel. It follows that b has degree at most one. A nonconstant real affine function with values in {0,1} is (1+η u_a)/2 for one coordinate: in b²=b, every degree-two coefficient is twice a product of two distinct affine coefficients, so at most one is nonzero. Both slices are nonzero, so this is the nonconstant case. The new last variable is η u_a on support and hence joins that block. The value of f there is h times the new variable's sign, which increases the block's prescribed exponent by one, up to scalar sign. This proves the form.

For a pure level-d function attaining the minimum, there are no prescribed-coordinate indicators, since a nonempty such group gives at least two total levels. Nor can any signed block have size at least three: both the maximum level b−1 and the level b−3 would appear (tensor the unchanged maximum in each other block), so the Fourier function would not be pure. Thus the blocks have size 1 or 2, with exactly d pairs by the degree. Up to scalar sign a size-two factor is z_u+ε z_v. This proves the single-level fact used below.

## 3. Antipodal support and full equality classification

Write f=f_i+f_j with nonzero pure level components. The antipodal map z→−z changes f_i by (−1)^i and f_j by (−1)^j, and the signs are opposite. Consequently, on any antipodal pair where f_i is nonzero, f cannot vanish at both points. The same holds for f_j. The components' supports themselves are antipodally invariant.

First assume i+j≤n. Then i≤n/2, so the single-level theorem gives
```
   |supp f| ≥ |supp f_i|/2 ≥ 2^(n−i−1).                       (3)
```
If equality holds then f_i=cP, where P is the product of signed coordinate pairs in (2). Outside its support, any nonzero f_j would contribute additional supported points to f, contradicting equality. On its support, exactly one of f(z), f(−z) is nonzero in each antipodal pair. The other value being zero implies f_j(z)/f_i(z)∈{−1,1} everywhere on this support, including the other point of each pair. Write that ratio as h(u,z_F), a sign function on one representative u from each constrained pair and all remaining free coordinates. Then f_j=cP h, with h defined arbitrarily outside that parameterization (which is not needed for the product).

Expand h in characters in u and z_F. For a pair B=(u_a,v_a), taking u=z_(u_a) as free parameter on its support, multiplication by u replaces its pair factor z_(u_a)+ε z_(v_a) with 1+ε z_(u_a)z_(v_a), which has both pair levels 0 and 2 instead of pure level 1. Products involving distinct sets of chosen pair reps and free-coordinate indices have disjoint Fourier support: each pair block is odd or even according to its choice, and the free-coordinate character records its exact subset. Thus any nonzero term in h using a pair rep contributes frequencies of at least two total levels, not subject to cancellation from other terms. As f_j is pure level j, h uses no paired rep. Its remaining terms each have degree j−i, because P has level i. Therefore h=g as in (2) and necessity follows.

Conversely every (2) has the two prescribed nonzero levels: the first factor has pure level i, and multiplication by g on disjoint coordinates gives pure level j. Since j−i is odd, g(−z_F)=−g(z_F), hence it is 1 on exactly half its domain. The pair restrictions cut the support fraction by 2^(−i), independently of g. This gives precisely 2^(n−i−1). A single parity character of length j−i is always available, as j−i≤n−2i by i+j≤n. Thus the family is nonempty.

If i+j>n, multiply f by full parity χ_[n]. A Fourier index T then goes to its complement, taking (i,j) to (n−j,n−i), and no support point changes. Their sum is less than n, and their difference is still odd, so the previous case gives the value 2^(j−1) and all equality cases by that bijection. This proves (1).

## 4. Boundaries and a non-character example

If i=0 in the lower-half formula, P is the empty product and the antipodal bound simply counts at least one supported point per pair. If j=n, multiplication by full parity maps the problem to i'=0, giving 2^(n−1). If i+j=n, the free-coordinate pure degree j−i equals |F|, so g=σχ_F for σ∈{−1,1}. Multiplying each pair factor by its pair parity preserves it up to its ε sign, and multiplying 1+σχ_F by χ_F also preserves it up to σ. Thus duality and the direct form describe the same class at the boundary. The theorem covers n=1 with its unique pair (0,1).

The allowed g need not be a parity character. For instance on five free coordinates,
```
   g(z)= z_5 (z_1 z_2 + z_2 z_3 + z_3 z_4 − z_1 z_4)/2
```
takes values ±1: either z_1=z_3 or z_1=−z_3 reduces the bracket divided by 2 to a single signed pair product. It has four distinct cubic characters. It accordingly gives a non-character extremizer for {0,3}, and by (2) for any pair with j−i=3 and at least five free coordinates.

Nothing here extends the conclusion to same-parity level pairs. For example 1+z_1 z_2+z_1 z_3+z_2 z_3 has exact levels {0,2}, and on three coordinates it is nonzero only where all three agree, below the analogous 2^(3−1) opposite-parity expression.
