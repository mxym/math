# The original graph-site harmonic quartic, at both cusps

Suppose an arbitrary SRG(99,14,1,2) exists. Let its Seidel rank over the field of seven elements be r ∈ {36,38,40,42}, and put h = 7^((r−36)/2). No automorphism or shortest-spectrum assumption is made. This note derives two exact necessary identities of weight 26 and a geometric inequality from the first one. No rank is eliminated here.

## Which lattice and which counts?

Use the rank-44 lattice L of determinant 7^(44−r) in [maximal-marked-lattice](../../maximal-marked-lattice/README.md), and K = √7 L*. In Euclidean site coordinates, the relevant eigenprojection is P=(3I−A+J/9)/7, with diagonal 4/9. Write d_i=(3I−A)e_i. The graph chart has A b=−4b−2a·1, sum b=−11a and t=b·b; its centered vector is v=b+(a/9)·1 and v·v=t−11a²/9. The charge is folded to the interval [−4,4]. On K the charges are 0 and ±3. A point of L, scaled by √7, is exactly an original zero seven-class point of that chart. This zero class is not a mean over the maximal determinant-49 extensions.

Let N_t count all neutral chart points of squared norm t (both signs; not just signed unit fields), and G_at all positive-charge a fields of squared norm t. A superscript (0) restricts to the original zero seven-class. Write Y_j for the ordinary number of norm-2j points in L. Put M_0=G_2,22^(0), the number of original-compatible 22-cocliques. Define the quartic
```
H(v) = 69 Σ_i v_i^4 − 2(v·v)^2.
```
It is harmonic on the 44-dimensional eigenspace: ΔΣ v_i^4=12(4/9)(v·v), and Δ(v·v)^2=4(44+2)(v·v). Write X_j for the sum of H over K at squared norm 2j. Write Z_j for the sum of H in the **scaled original** zero seven-class at squared norm 14j; this is 49 times the sum over L at squared norm 2j.

## Two Fourier identities

```
h(574 X7 +252 X8 +105 X9 +40 X10 +14 X11 +4 X12 +X13)
 = 7(1034 Z1 +44 Z2 +Z3).

h(97776 X7 +25494 X8 +5208 X9 +556 X10 −168 X11 −111 X12 −40 X13)
 = 7(−28240 Z1 −900 Z2 +Z4).
```

The harmonic theta series of K has weight 22+4=26 on Γ₀(7) and trivial character (the determinant is a square). If x is this weighted series, the weighted series of L is −7^(11−(44−r)/2) x|W₇. This is the usual Poisson transformation for harmonic theta; the degree-four Fourier phase is +1 and the graph-scale 49 factor belongs in Z only. In particular, for the negatively Fricke-transformed Eisenstein-product companion y, the graph-scale Z-series has coefficients 7^(r/2−11+2) y. Compare the odd-character Eisenstein product normalization in [rank-34-short-support](../../rank-34-short-support/README.md). The level has index 8, genus zero, two cusps, no order-two elliptic point and two order-three elliptic points, giving dim M_26=1+2⌊26/3⌋=17. The checker spans this space by products of complementary odd weights, with independent first 17 coefficient columns, and checks both relations on the full subspace X0=…=X6=0, Z0=0. These vanish by harmonicity at zero and the K minimum 14. No extrapolation from sample coefficients is used.

## Reading the left side

Set
```
S = 574² N14 +252·592 N16 +105·594 N18 +40·580 N20
  +14(550 N22 −924 G3,33) +4(504 N24 −832 G3,35)
  +442 N26 +8280 G1,21 −772 G3,37.
```
The first left side is h S. For a neutral unit field H=69t−2t²; each nonunit contributes excess 69 Σ(b_i⁴−b_i²). For a charge-three unit field H=115t−3289−2(t−11)²; the excess for any other field is the sum of
```
E(n) = 69(n⁴−n²)+92(n³−n) = 23 n(n−1)(n+1)(3n+4).
```
This is nonnegative at every integer, with E(2)=1380, E(−2)=276.

The elementary translation by d_i changes (a,t) to (a+1,t+23+2(7b_i+2a)), and changes b_i by +3; reverse signs give the inverse. Use the minima |sum b|≤t and G1,t=0 for t<21 from the [short-spectrum dictionary](exclusion.md). A neutral field at t≤24 is unit: subtract or add d_i at an entry of magnitude ≥2 and obtain charge ±1 of norm ≤19. For t=26 an exceptional site of value −2 corresponds bijectively under addition of d_i to a +1 site in G1,21; larger magnitudes are impossible. Charge-one norm-21 fields are unit: at +2 subtraction gives neutral norm ≤12 (and not zero, by the adjusted coordinate); at −2 addition gives charge two of norm ≤20; either is impossible. Each such field has exactly five positives. Negation doubles the incidence count, giving 10 G1,21 exceptional sites counted with multiplicity and 69·12·10 G1,21 in S. N26 in this formula is the **raw** shell, not its unit subpopulation. A charge-three field of norm t≤37 has no +2 (t+sum b=t−33≤4), and at any entry ≤−2 addition gives charge four of norm ≤44. At equality the old value is −2, so the new site is +1, impossible at t=44=|sum b|, where all nonzero entries must be −1. This verifies the small-shell decomposition.

## Original-class marks on the right

The following inequality, including the neutral norm-28 correction, holds:
```
h S ≥ 7[ 1034·574 Y1 −44·372 Y2 −722 Y3
         +44·736 N28^(0) +44·60720 M_0 +151961184 ].
```
Indeed Z1=574Y1, as the charge-three shell cannot occur there. In Z2 the charge-three norm-39 unit baseline is −372 and the neutral norm-28 baseline is 364. Each original-compatible Hoffman coclique c (the negative indicator of 22 sites) and site i in c yield c+d_i at charge three, norm 39. This has a unique +2 at i and no other positive nonunit, so it recovers (c,i). The mark stays in the original zero seven-class because d_i is the chart shift of u_i and 3u_i∈L. Including opposite orientations gives an extra 2·22·1380 M_0. Thus Z2≥−372Y2+736N28^(0)+60720M_0.

In Z3 the neutral baseline is −630 and the charge-three baseline is −722. Each oriented nonedge (8316 of them) gives the original neutral norm-42 label d_i−d_j. Its +3,−3 recover the endpoints; others are unit or zero. Each gives 92+2·69(3⁴−3²)=10028 above the common baseline. Each induced three-vertex path (8316 choices) gives the positive charge-three norm-53 label d_i+d_j+d_k. Its leaves carry +2, its center +1, and three exterior sites carry −2 (the two distinct edge caps and the second common neighbor of the leaves). All others are zero or −1. Indeed an exterior site adjacent to all three would violate the adjacent-pair common-neighbor bound at an edge. The full positive support is therefore exactly the path, making the map injective. The surplus is 2·1380+3·276=3588; count both orientations. These two families alone contribute 143068464.

Finally [rank-34-short-support, counting and collision lemmas](../../rank-34-short-support/README.md) gives at least 20790−9P_prism−36G_grid≥8055 additional distinct one-sign norm-six marks of six-site/eight-edge type, after subtracting collisions with the previous marks; P_prism≤851, G_grid≤⌊P_prism/6⌋. In the charge-three direction the folded evaluation of such a set F is −Σ_{i∈F}d_i−1, equal to deg_F(i)−4 on F. Its internal degrees sum to 16. Even over all six-tuples in {0,…,5} with sum 16 the minimum of Σ E(deg_F(i)−4) is 552, by the tiny exhaustive check supplied. Counting both signs adds 2·8055·552=8892720. This proves Z3≥−722Y3+151961184. All these graph marks belong to L before scaling, because their literal coefficient sums are divisible by three.

Run `python3 original_site_quartic.py` in this directory. The standard-library checker rebuilds the full weight-26 basis, tests both identities at all four ranks, and recomputes the mark constants. It does not assume that any extremal signed-shell population is attained.
