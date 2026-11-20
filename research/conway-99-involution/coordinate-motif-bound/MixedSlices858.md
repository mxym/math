**Historical endpoint:** [the edge-transport theorem](edge-transport/README.md) rules out all-minimum vertices and gives n₃≥864, so the conditional 858/861 endpoint analysis below is now vacuous.

# Mixed vertex tensors near the 858 motif bound (research note)

Use [the coordinate lower bound](README.md), writing g=7E, g_i=g e_i, Z=(w_U)_U, u_U=w_U/√7, s_U(i)=w_U(i)−1/3, and q(T)=a₂(T)/3=12−a₃(T). Define q_ij=Σ_U w_U(i)w_U(j)w_U, and K_i to have columns q_ij. The self-adjoint endomorphism D_i=K_i/7 on the 44D −4 eigenspace obeys D_i g_j=q_ij. In particular q_ii=−g_i: coordinatewise s_U(i)²=2N_iU−s_U(i), so q_ii=2(ZNᵀ)e_i−(ZZᵀ)e_i/3=(42−49)Ee_i. Hence D_i g_i=−g_i. The trace vanishes by Σ w_U(i)=0 and ||w_U||²=28.

## Universal mixed minimum, divisibility, and equality rows

Expand q_ij in w coordinates:
```
q_ij=Σ_U s_U(i)s_U(j)w_U +7(g_i+g_j) = g z,
z = Σ_U s_U(i)s_U(j)n_U+7(e_i+e_j).
```
Indeed Σ s_U(i)w_U=147Ee_i. The Gram sum of s-rows is
Σ s_U(i)s_U(j)=147E_ij+231/9=21(3δ_ij−A_ij)+28. Therefore the sum t of the integer z equals 98+63(3δ_ij−A_ij)≡−1 mod9. Hence q_ij has zero sum, all coordinates in −1/9+ℤ, and has squared norm ≥88/9 by integral balancing. On the other hand
```
9||q_ij||² =7(27||z||²−9zᵀAz+t²) ≡70 mod126.
```
The quadratic zᵀAz is even; ||z||²≡t mod2; t≡8 or 17 mod18 gives 9t+t²≡10 mod18. Thus ||q_ij||²=196/9+14 d_ij with d_ij a nonnegative integer and d_ii=0. Summing gives tr(D_i²)≥44.

D_i=7I+Σ_U s_U(i)u_Uu_Uᵀ, integral on Λ=Σℤu_U. Expanding tr D_i² modulo four, the scalar and mixed terms are divisible by four (rank44, u_U²=4). The last term is sᵀWs for s=(s_U(i))_U, W=M∘M, and is congruent to sᵀMs mod4 because W,M agree mod2 off diagonal and their diagonal difference is 12. We have sᵀMs=||Σs_U(i)u_U||²=||21g_i/√7||²=1372. Thus tr D_i²≡0 mod4.

Finally Σ_i tr(D_i²)=Σ_ijk K_ijk²/49=7Σ_TU M_TU³=28(n₃−693). At n₃=858 the sum is 4620, excess 264 over 99·44; hence at least 33 vertices i have tr(D_i²)=44, equivalently every one of their 99 mixed slices has its minimum norm. At n₃=861 at least 12 such vertices are needed.

## Rank obstruction at a minimum vertex

In any ℤ-basis of Λ with Gram P and triangle columns U, D_i=7I+U diag(s) UᵀP. Thus rank₇ D_i ≤ rank₇ P =rank₇ M. The equality uses that U is surjective over ℤ and hence over every residue field. Rank transport N M Nᵀ=27I−9A+J≡−(2A−J+I) mod7, (NᵀN)M=3M, together with [Wave 66](https://github.com/YesterdaysLemon/conway-99-research/blob/5f497b545c536de90a1a557c51b53f041fecf7db/verification/wave66-spherical-code-shift/audit.md) imply rank₇ M≤42 globally.

If D_i has ordinary rank r, the product of its r nonzero real eigenvalues is the last nonzero characteristic coefficient up to sign. It is a nonzero integer and divisible by 7^(max(0,r−rank₇ M)), because each r-minor has that divisibility by Smith decomposition (its coefficient is a sum of principal r-minors). At a minimum vertex its absolute value is ≤(44/r)^(r/2) by AM–GM of the r squared eigenvalues. Ranks44 and 43 are consequently impossible: the respective upper bounds are 1 and <2.

## If no Hoffman 22-coclique exists

At a minimum vertex write y_j=q_ij. Each y_j has norm squared 196/9, with every coordinate in −1/9+ℤ. If j≠k, y_j+y_k=g z' has zero sum and coordinates in −2/9+ℤ. Binary balancing gives squared norm ≥154/9; equality gives the indicator of 22 vertices minus (2/9)1, an eigenvector of eigenvalue −4. Its indicator x satisfies (A+4I)x=4·1, so the 22 vertices are independent. Without such a coclique, lattice quantization lifts the norm floor by 14 (replace t≡−1 mod9 above by t'≡−2 mod9). Therefore (y_j,y_k)≥−56/9. Summing over ordered graph edges, A K_i=−4K_i forces the average exactly −56/9. Thus all edge inner products are −56/9, and for every triangle T, ||Σ_{j∈T}y_j||²=28. This is the column p_{T,i} of P_T. In particular every triangle through i has q(T)=0 or 2: q=1 is excluded by the graph-local perfect-matching argument of [Lou and Murin, §5, p. 8](https://math.mit.edu/research/highschool/primes/materials/2014/Lou-Murin.pdf) (their γ=a₃=12−q cannot equal 11, since the three perfect matchings on the three 12-element exterior neighborhoods compose to a permutation, which cannot have exactly 11 fixed points); and q≥3 gives a marked row with diagonal −1 and two within-T off-diagonal entries q−1≥2, requiring more than three exceptional units (two positive 2s cannot be balanced around either 2 by the single −1). This is a scoped extra implication, not an exclusion of n₃=858.

These mixed-slice and equality statements have no effect on the established unconditional bound n₃≥858 unless an additional equality obstruction is proved.

## The integral vertex-coordinate lattice; excluding ranks 42 and 41

Let L be the integer span of the g_j. The positive bilinear form H=(9/7) times the usual dot product is integral and even on L (generator Gram 27I−9A+J). The vector g z has coordinate class deg/9 modulo integers, where deg=Σ z modulo 9. This class is intrinsic and defines a homomorphism L→ℤ/9, reversed by D_i since D_i g_j=q_ij. In particular every integral-lattice vector in ker D_i has integer coordinates, sum zero, and squared norm divisible by 14. Indeed for deg=0 the identity earlier for 9||g z||² shows divisibility by 7, and the norm is even by zero-sum integer coordinates. Every nonzero vector in L has squared norm at least 14: for residue ±1 the minimum is 196/9 as above; for any other nonzero residue, coordinate balancing already gives at least 154/9. As all 99 generators have norm squared 196/9<28, in an orthogonal integral decomposition each would lie entirely in one summand. No two generators are perpendicular. Thus L is integrally indecomposable.

Set d equal to the positive absolute pseudodeterminant of D_i. In a singular case write K and I for the rational kernel and image, respectively, with K_L=K∩L and I_L=I∩L. The glue L/(K_L⊕I_L) injects into I_L/D_i(I_L), a group of order d: the map is induced by D_i, and if D_i x=D_i y for y∈I_L then x−y∈K_L. It follows that d=1 is impossible. Also dπ_K L⊂K_L for ordinary orthogonal projection π_K. These statements do not presume that either rational summand is a direct summand integrally.

For comparison at 7, D_i=7I+(1/9)Σ_U s_U(i)w_U H(w_U,·), with w_U∈L. Therefore rank₇ D_i ≤ rank₇ H =rank₇ M≤42 in this vertex lattice as well. If r=42 then AM–GM gives d≤2, so d=2. Its unit last characteristic coefficient forces rank₇ D_i=42, and hence ker(D_i mod7)=rad(H mod7). Every x∈K_L therefore has H(x,x)≡0 mod7. Its real squared norm is a multiple of 14 by the degree observation; since H(x,x)=(9/7)||x||² this multiple must be divisible by seven, so nonzero kernel vectors have norm squared ≥98. Some π_K g_j is nonzero, but its double is in K_L and has squared norm ≤4·196/9<98, a contradiction.

For a convenient sharper pseudodeterminant inequality, let t run over the nonzero squared eigenvalues at a minimum vertex. They are totally positive algebraic integers with a monic integral polynomial, Σt=44. Ignore roots t=1. Then ∏|t−1|≥1, since its product (up to sign) is a nonzero integer. For t>0, t≠1,
```
log t ≤ (log 2)(t−1)−(log 2−1/2)log|t−1|.
```
For t<1 this follows from log t≤t−1; for t>1 the difference right minus left has positive second derivative and vanishes with derivative zero at 2. Summation gives d≤2^((44−r)/2); equality requires that every nonunit t be 2.

If r=41, d≤2 by this inequality, so d=2. The glue group then has order two. Let V=14π_K on the 99 vertex coordinates (zero outside the eigenspace is understood). Each column is 2π_K g_j∈K_L, so V is integral symmetric, V²=14V, rank 3, tr V=42. Since π_K≤E, its diagonal entries s_j are integers between 0 and floor(14·4/9)=6. The squared column norm is 14s_j. The columns modulo two take at most two values: their classes (2π_K g_j modulo 2K_L) factor through the two-element glue. Hence rank_F₂ V≤1. If it is one, there is a binary vector b such that V≡bbᵀ mod2. This uses symmetry and the fact that the only nonzero scalar is 1.

A nonzero column with even s_j would be even entrywise (also if the binary rank is zero). Its half is an integral, zero-sum −4 eigenvector with even squared norm (7/2)s_j; hence s_j=4. The half-column would then have norm squared 14 and coordinate 2 at j. No integral −4 eigenvector x of squared norm 14 can have a coordinate of magnitude at least 2: positive and negative masses are each at most 7 since Σ|x|≤Σx²=14, whereas its signed neighbor sum would have magnitude ≥8. Thus all nonzero diagonal entries of V are odd. Write O for their support; all entries on O×O are odd and all other entries vanish (zero diagonal in a positive semidefinite matrix forces zero row). If some s_j=1, column j has squared norm 14, hence entries in {0,±1} by the same mass argument; so |O|=14. If all nonzero s_j≥3, then |O|≤42/3=14. Consequently the 3D rational kernel is supported on at most 14 vertices and the induced subgraph has eigenvalue −4 with multiplicity at least three.

This is impossible. Pad the induced subgraph with isolated vertices to 14 vertices; its adjacent/nonadjacent pairs still have at most one/two common neighbors. Its degrees satisfy Σ_v binom(d_v,2)≤2 binom(14,2)−|E|, hence Σ_v d_v²≤364 and the even trace tr(A²)=Σ_v d_v≤70 by Cauchy. Its Perron radius ρ≥4, and three eigenvalues −4 together with trace zero force
```
tr(A²)≥48+ρ²+(12−ρ)²/10≥70.4.
```
The last quadratic increases for ρ≥4. This contradiction excludes rank 41. In summary every all-min vertex has rational rank at most 40; in particular at least 33 such singular operators of rank at most 40 are necessary at n₃=858. This is not a contradiction for ranks≤40.
