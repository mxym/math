# A ternary affine-coset minimum and marked code coefficients

This note continues the [ternary adjacency code](ternary-adjacency-code.md). Take B=A+I over F3, C=ker B, D0=ker A, and E=D0^⊥={t:Bt is constant}. Write E1={t:Bt=1}; E2 is its negative. The full E is the dimension-45 generalized zero eigenspace of B, since B²=B−J and BJ=0. Its orthogonal complement D0 is the 54-dimensional B-eigenvalue-one eigenspace. This note proves minimum Hamming weight at least eleven for E1 and E2. Combined with C and D0 from the previous note, E and its dual both have minimum at least eleven; equality is not claimed.

## Closed-neighborhood counts on a coset word

For t represented by ±1/0, let s be its support size, n its negative count, and σ=s−2n its ordinary sum. If Bt=1 mod3, the identity B²=B−J modulo 3 applied to t shows σ≡1. At any graph vertex consider its *closed* neighborhood; its positive and negative support contacts r,q satisfy r−q≡1. Therefore it always contains at least one support site and s≥7. The total excess over one of its support incidences is L=15s−99. A vertex with a negative support contact cannot have only one support contact; the incidences into vertices with ≥2 contacts total at most 2L, so 15n≤2L. Pointwise the excess is at least 2q−3 choose(q,2) (q=0,1,2 as in the open-neighborhood argument; for q≥3 the right side is nonpositive). Every pair is counted by at most three closed-neighborhood witnesses: two for a nonedge, and endpoints plus the triangle cap for an edge. Thus L≥30n−9 choose(n,2). Also n≡1−s mod3.

The integral vector z=(Bt−1)/3 satisfies Az=4t+((2σ−14)/3)·1, by B²=B+12I+2J over the integers. At s7 we have L6, n0, σ7 and z≥0 of sum2. This is incompatible with Az=4t. At s8 we have L21 and n2; the excess bound is ≥51. At s9, L36 permits n1 or4, and n4 gives ≥66. If n1, then σ7 and each Bt≥−1; the residue forces Bt≥1, so z≥0, yet Az=4t has a negative coordinate.

## Weight ten

Now L51, and n∈{0,3,6}. The general bound rejects n3.

For n6, there are four positives. Let H_j count vertices with j closed contacts to the positive set (j=0,…,4). Negative closed contact minima at those levels are 2,0,1,2,0. The positive incidence count is 60 and gives H0=39+H2+2H3+3H4. The negative incidence count is 90, hence 78+3H2+6H3+6H4≤90. Counting closed witnesses of positive pairs gives H2+3H3+6H4=12+e_P, where e_P is the number of literal positive edges. Therefore H3+4H4≥8+e_P, while H2+2H3+2H4≤4 gives H3+4H4≤8, with equality only at H4=2 and H2=H3=0. Thus e_P=0. Both vertices at closed height four must lie outside the independent positive set (each inside site has closed height one), so they share four actual neighbors, impossible.

For n0, t=1_S with |S|=10. Then z=(B1_S−1)/3≥0, sum17, and Az=4·1_S+2. If a z-entry were ≥3, its 14 neighbors could not lie outside S, where Az=2; since |S|=10 this is impossible. Thus z∈{0,1,2}. If H2 denotes the number of 2 entries, counting all closed pair witnesses gives 90+e_S=102+9H2 and e_S=12+9H2. Specifically, a closed level is 1+3z, so its pair count is (9z²+3z)/2; ∑z²=17+2H2. The internal degree of an S site is 3z, so ∑_S z=8+6H2. H2≥2 would exceed the total sum17, and H2=1 would require sum14 over just ten sites with at most one site of value2. Thus H2=0, z=1_T with |T|=17, I=S∩T has size8 and induces a cubic graph, and the two S∖T sites are isolated in S. Each of the nine T∖S sites sees four actual S sites and exactly two T sites by the equations. Hence it sees exactly two in I and both sites in S∖T. Those two distinct sites would have nine common neighbors, impossible.

Thus E1 and E2 have no words of Hamming weight ten or less. No rank or symmetry restriction was imposed.

## Additional exact composition facts

Every all-negative word in E1 has weight at least 14: its closed incidence count is 2 modulo 3 everywhere, so 15s≥198. At s14, for the support S set z=(B1_S−2)/3≥0 with sum4 and Az=4·1_S. Any positive z coordinate lies outside S (no self-loop allows it to realize 4 at itself), and must have its full open neighborhood equal to S: all S sites see all z mass, and no other vertex does. More than one positive z vertex would have 14 common neighbors, impossible. Thus z=4e_i and S=N(i). Conversely −1_{N(i)} lies in E1 because B A e_i≡−1; the 99 such words are distinct. Therefore this lowest monocolor profile is exactly counted, not merely bounded.

The literal vectors A(e_i−e_j), i≠j, lie in C and are signed-unit. They are distinct over F3 because a collision is a nonzero D0 word of support at most four. Actual adjacent pairs give Hamming weight26 (one common open neighbor), with 13 of each sign; nonadjacent pairs give weight24 (two common open neighbors), with 12 of each. These are disjoint from actual unit −4 eigenvectors of the same signed compositions: an equality modulo3 of two signed-unit words is literal equality, and if A(e_i−e_j) were a −4 eigenvector, invertibility of A over the reals would make e_i−e_j a forbidden norm-two neutral −4 eigenvector. Consequently the balanced weight24 complete coefficient of C is at least 8316+N24, and its balanced weight26 coefficient is at least 1386+U026.

The exact trivariate transforms and corresponding lower coefficients of D0 are in the prior note. No upper on the U026 shell or new palette exclusion is claimed.
