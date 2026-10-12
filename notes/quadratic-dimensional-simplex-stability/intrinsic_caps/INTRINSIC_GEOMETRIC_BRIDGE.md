# Relative projection caps and retention of every maximum simplex

Date: 7 October 2026. This is a written mathematical proof included in the independent analytic model audit. It changes no earlier source and is not a proof-assistant verification or priority claim.

## Result

Let d≥3, n=d+1, m=d−1. Let K⊂P be full-dimensional compact convex bodies, where P is a simplex. Define

    δ = sup_{u∈S^(d−1)} [π_P(u)−π_K(u)]/π_P(u),
    ρ = δ^(1/m).

Here π denotes Euclidean (d−1)-dimensional orthogonal projection volume. The ratio and its supremum are unchanged by invertible affine maps (directions transform through the induced quotient map).

For EVERY maximum-volume simplex S inscribed in K, with centroid z_S,

    K ⊂ z_S + [1+16(d+1)² ρ](S−z_S).

The stronger local conclusion is

    K ⊂ z_S + [1+8(d+1)ρ](S−z_S)

whenever ρ≤1/[16(d+1)]. All statements include δ=0. No inradius, circumradius, Euclidean cap-volume constant, or dimension-dependent normalization enters the geometric argument.

The uniform quadratic conclusion is the established result here. The local linear coefficient does not, by itself, yield a uniform linear coefficient: its admissibility threshold still depends on dimension.

## 1. Exact barycentric projection cap

Write the vertices of P as p_1,…,p_n and its affine barycentric coordinate functions as λ_1,…,λ_n. For every i there exists k_i∈K with

    λ_i(k_i)≥1−ρ.

Indeed, set t=1−max_K λ_i, which lies in [0,1]. Choose any unit projection direction u parallel to the opposite facet F_i, so λ_i is constant on lines parallel to u. It therefore descends to an affine function on u^⊥. The projection P|u^⊥ is a pyramid whose apex is the projected p_i and whose base lies in the descended hyperplane λ_i=0. Its cap λ_i>1−t is a homothetic copy, of ratio t, of the entire projection (up to its boundary). This cap is disjoint from K|u^⊥ because λ_i≤1−t on K. Consequently

    π_P(u)−π_K(u) ≥ t^m π_P(u),

and t≤ρ. The maximizing point k_i exists by compactness.

The projected opposite facet can be a general (d−2)-polytope; it need not be a simplex. The exact homothety statement remains valid, since the entire projected body is the convex hull of that base and the apex.

## 2. A comparison simplex and a determinant lower bound

Let Q be the n×n matrix whose ith column consists of the P-barycentric coordinates of k_i. It is nonnegative and column-stochastic, with Q_ii≥1−ρ. If ρ≤1/(16n), then

    det Q ≥ 1−2nρ > 0.

To prove this directly, independently sample row indices R_i from the ith column of Q. The determinant is the probability of an even permutation minus the probability of an odd permutation. The identity permutation has probability p=∏_i Q_ii≥1−nρ. Every negative term is among the complementary outcomes, so

    det Q ≥ p−(1−p) ≥ 1−2nρ.

In particular conv(k_i) is a simplex and its volume is det Q times the volume of P.

## 3. Initial matching for an arbitrary prescribed maximum S

Fix ANY maximum S and let W be the nonnegative column-stochastic matrix of its vertices in P-barycentric coordinates. Since conv(k_i)⊂K,

    |det W|=|S|/|P|≥det Q≥1−η,
    η=2nρ≤1/8.

Every column of W has Euclidean norm at most 1. Hadamard's inequality therefore implies that every column has norm at least 1−η. Since the squared norm of a probability vector is at most its largest coordinate, every column has an entry at least

    (1−η)²≥1−2η.

These dominant entries occur in distinct rows. Otherwise two independent columns would choose the same row with probability at least (1−2η)². The permanent is the probability that all selected rows are distinct, and hence

    |det W|≤per(W)≤1−(1−2η)²≤4η<1−η,

contradicting the determinant bound. Relabel the vertices of S so that

    W_ii≥1−2η≥1−4nρ.

For the induced column-sum matrix norm,

    ||W−I||_1 = max_i 2(1−W_ii) ≤8nρ≤1/2.

Thus B=W^(-1) exists and

    ||B−I||_1≤8nρ/(1−8nρ).

Both W and B have column sums 1. Consequently each column of B−I sums to zero, and each individual entry has absolute value at most half the absolute column sum. Therefore

    β:=max_{ij}|B_ij−1_{i=j}|≤4nρ/(1−8nρ)≤1/2.

This matching is proved for the prescribed maximum S; no replacement maximum is chosen.

## 4. Maximality bootstrap: a local linear conclusion

Set r_i=1−W_ii. The ii entry of BW=I gives

    B_ii(1−r_i)+Σ_{j≠i}B_ij W_ji=1.

As |B_ij|≤β off the diagonal, this implies

    B_ii−1≥(1−β)r_i/(1−r_i)≥r_i/2.

On the other hand, replacing the ith vertex of S by k_i cannot increase its volume. The ith S-barycentric coordinate of k_i is (BQ)_ii and thus |(BQ)_ii|≤1. Its lower bound is

    (BQ)_ii≥(1−ρ)B_ii−ρβ,

because Q_ii≥1−ρ, B_ii≥1/2, and all other entries in row i of B are ≥−β. It follows that

    B_ii−1≤ρ(B_ii+β)≤ρ(1+2β)≤2ρ.

Combining the inequalities gives r_i≤4ρ for EVERY column. Hence

    ||W−I||_1≤8ρ,
    ||B−I||_1≤8ρ/(1−8ρ).

Again using the zero column sums of B−I, every negative entry of B has magnitude at most

    4ρ/(1−8ρ)≤8ρ.

The last inequality holds because ρ≤1/(16n)≤1/16.

The columns of B are exactly the S-barycentric coordinates of the vertices of P. A homothety of ratio 1+t about the centroid of S is characterized by all S-barycentric coordinates being at least −t/n. Therefore

    P⊂z_S+[1+8nρ](S−z_S),

which gives the claimed local conclusion for K⊂P.

## 5. Global quadratic conclusion

Every maximum S⊂K satisfies the elementary universal bound E(K,S)≤n. Indeed, for each x∈K and each S-barycentric coordinate α_i(x), replacement maximality gives |α_i(x)|≤1. In particular α_i(x)≥−1, precisely the centroid dilation bound E≤n.

If ρ>1/(16n), then

    E(K,S)≤n<16n²ρ.

If ρ≤1/(16n), Section 4 gives E≤8nρ≤16n²ρ. This proves the uniform theorem.

## 6. How to combine the bridge with an invariant deficit

Suppose an independent, correctly normalized argument produces an enclosing simplex P and

    δ ≤ A_d e

on a smallness branch that includes e≤1/A_d. The bridge gives

    E(K,S)≤16n² A_d^(1/m) e^(1/m)

on that branch, for every maximum S. The usual universal E≤n bound handles any omitted larger-e branch as long as the displayed coefficient dominates n e_gate^(−1/m).

In particular, when A_d is polynomial and the construction's smallness gate is reciprocal-polynomial in d, this bridge yields a uniform O(d²) coefficient. The local linear estimate only applies when (A_d e)^(1/m)≤1/(16n), an exponentially smaller deficit gate; using it alone in a two-branch proof restores a quadratic coefficient.

## 7. A more general support-width cap

For any K⊂P, without assuming P is a simplex, the same relative projection deficit implies, for every unit n,

    h_P(n)−h_K(n)≤ρ [h_P(n)+h_P(−n)].

Let s=h_P(n)−h_K(n), w=h_P(n)+h_P(−n)>0, and q∈P maximize n·q. The homothetic copy q+t(P−q), where t=s/w, lies in the closed cap n·x≥h_K(n). Its interior relative to P lies strictly above that hyperplane when s>0. For any projection direction u perpendicular to n, the projected copy has volume t^mπ_P(u), and its interior misses the projection of K. Thus δ≥t^m. The cases s=0 or δ=0 follow directly or by the same inequality.

For a simplex this support-width bound also yields the vertex-coordinate cap in Section 1. Section 1 provides the convenient exact choice of near-vertex points required by the determinant comparison.
