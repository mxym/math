# Each chosen saturated rooted dual has a field of squared norm at most 136

Fix any vertex o of a prospective srg(99,14,1,2). Apply the [rooted rank-32 construction](rooted-rank32.md), with T of rank 30 and determinant 392, K=<14> perpendicular <28>, and each anti-isometric gluing U of T and K even unimodular of rank 32. Keep T fixed; varying only its gluing does not change the field set. A vector x in the full dual of T gives a genuine integral minus-four eigenfield, zero on the closed neighborhood of o, of squared norm 56(x,x). The evaluation is injective. There is such a nonzero field of squared norm at most 136. More sharply, if T-dual has no such field of positive squared norm below 136, its norm-136 field count is **exactly 240 oriented fields**, not 240 auxiliary lifts.

## Discriminant orbits and the marked coefficients

Index the T-dual shell by n=28(x,x), so field norm is 2n. For (x,p e/14+q f/28) in the U-shell of norm 2j, one has n=56j-2p²-q², p and q integers. Every dual class occurs in every gluing and has some representative in the indicated K coordinates, so n is integral and never 1 or 3 modulo 8. The O(A_K)-orbits of allowable classes are determined by n modulo 56. At two the class is given by p mod 2 and q mod 4 up to sign, determined by n mod 8: the six possible values of -2p²-q² for (p mod2, |q mod4|) are 0,7,4,6,5,2 respectively (q values in order 0,1,2 for each p). These are distinct, and changing q to -q locally respects the discriminant form. At seven the anisotropic plane has just the zero class at norm zero; the norm-one torus in F49 acts transitively on each nonzero norm value, of size eight. The two local actions can be chosen independently on the discriminant group, even when they do not lift to automorphisms of K. All anti-isometries define legitimate separate gluings, which is sufficient for averaging.

Let W_n be the total number of x with this n divided by the size of the indicated orbit. Averaging U's theta series over all anti-isometries, for every fixed p,q at j the expected number of x is exactly W_(56j-2p²-q²). In particular W_0=1. At n=68, the 2-class has p even and q=2 modulo 4, an orbit of size one; the seven class is nonzero, an orbit of size eight.

## Exact finite identity

For j=0,1,2,3,4 evaluate the harmonic projection of each monomial p^(2a) q^(2b), 0≤a+b≤9, on the full 32-dimensional sphere |v|²=2j. If P has degree l=2a+2b, the harmonic projection is

    sum_i (-1)^i |v|^(2i) Delta^i P / [4^i i! (16+l-2) falling i].

Here the Laplacian on functions of p,q is 14 partial_p²+28 partial_q² since the axes are orthogonal and have these squared norms. In each j its total is found by summing this polynomial times W_n over every integer pair p,q with n≥0. The averaged harmonic theta series is a full-level modular form of weight 16+l, cuspidal for l>0. Full-level forms have the usual basis of monomials in E4 and E6, and differences with a chosen monomial span the cusp subspace. Thus its first five coefficients satisfy every ordinary rational nullspace relation on the truncated basis. No claim about individual orbit uniformity is used.

Under W_n=0 for 0<n<68, substitute zero in these relations. The [exact checker](rooted-rank32-norm136.py) generates 126 integer rows on 120 still-possible indices from n=0 through 224; their exact rank is 102, unchanged on appending W68-30W0. Thus W68=30: eight eligible residue classes times thirty gives exactly 240 nonzero graph fields in this dual. This is a rank statement with exact integers and rationals; no numerical optimizer, modular-rank lower bound, quadratic cone, or positivity certificate is needed.

Run with Python 3 and SymPy: `python rooted-rank32-norm136.py`. Its sole line is `PASS: rank 102 on 120 columns; W68=30 W0 under the gap`. This sharpens the previous harmonic bound in the chosen dyadically saturated dual. The [graph-only rectangle fields](rooted-rectangle-fields.md) give smaller norms for the unrestricted real residual space, but their norm-70 fields are excluded from every such saturated dual by its dyadic norm residue. It is not a rank exclusion.
