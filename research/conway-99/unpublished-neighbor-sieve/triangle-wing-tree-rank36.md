# Triangle wings: a rank-eight residual and a rank-36 spanning-tree obstruction

Fix a triangle T in a Conway SRG. The 36 vertices with a neighbor in T split into three wings of 12 according to that unique neighbor. Let W denote their induced cubic graph, let c be its number of connected components, and let X be the 60 remaining sites. No symmetry or Hoffman coclique is assumed. The three matching wings and their cubic induced graph are already described by [Lou and Murin (2014), proof of Lemma 5.1](https://math.mit.edu/research/highschool/primes/materials/2014/Lou-Murin.pdf). The lattice projection and mod-seven spanning-tree test below are separate from that decomposition.

Inside each wing the edges are a perfect matching, since the 14 neighbors of the corresponding triangle vertex induce a matching and the other two triangle vertices are already mates. From a wing vertex to either of the other triangle roots there are exactly two common neighbors, one being its own root. An exterior site cannot meet two of the three roots. The remaining common neighbor therefore lies in the other root's wing and is unique. Hence each pair of wings also links by a perfect matching. A site of X has exactly two neighbors in each wing by the same common-neighbor count; they are nonmates. Conversely each nonmate pair in any one wing already has its root as one common neighbor and requires exactly one site in X, because the matchings to each of the other two wings give no common wing neighbor. Thus the 60 X sites are in bijection with the 60 nonmate pairs in each of the three wings.

Use minus-four marks u_i with Gram 3I-A+J/9 and frame constant 7 as in the [rank-44 construction](../maximal-marked-lattice/README.md). On W the Gram is G=L+J/9, where L=3I-A_W is its ordinary Laplacian. Its kernel consists of vectors constant on components with total sum zero, so its rank is 37-c. The three T marks belong to its rational span: the eigen-relations at T have coefficient matrix -3I-J on those three marks, invertible. Consequently the space of minus-four fields vanishing on the entire closed triangle-neighborhood has dimension exactly **7+c**, in particular eight when W is connected. It is rational and spanned by integral fields. Each component of W meets all wing classes in equal sizes by the matchings; more strongly every X-site has precisely |component|/6 neighbors in that component, since the corresponding component-indicator difference with mean zero is in the marking kernel.

If W is connected, the matrix-tree theorem gives
```
det G = (36/9) · (36 τ(W)) = 144τ(W),
```
where τ is the ordinary number of spanning trees. Suppose now that the mod-seven Seidel rank is 36. Then **τ(W) must be zero or a quadratic nonresidue modulo seven**. (For a disconnected graph take τ=0.) In particular a single triangle with τ≡1,2,4 rules out rank 36 for that graph.

To see this, work over Z7; the original graph marks generate the rank-44 lattice there (the charge-index has only prime three). Its determinant is 7^8 up to a square and its discriminant is elementary of dimension eight and minus type. If τ is a seven-unit, the 36 wing marks form a unimodular summand. The complementary rank-eight lattice has all eight elementary divisors equal to seven, so its Gram is 7J0 with J0 unimodular. The discriminant form has unit Gram equivalent to J0^-1 up to a scalar; in dimension eight a scalar has no effect on determinant square class. Minus type means the determinant of J0 modulo seven is a nonsquare: in dimension eight the hyperbolic determinant is (-1)^4=1. Therefore det(G) det(J0) is a square in Z7^× (divide the original determinant by 7^8). As 144 is a square, τ too must be a nonsquare.

There is a stronger array condition if τ is a unit. For each X site b write d_b for its six contacts and p_b=1/9·1-d_b in the 36 wing coordinates. At rank 36 the entire seven-class mod-seven Gram has rank 36 and its W block G is invertible. Consequently for ALL b,d in X one has
```
3·[b=d] − A_X[b,d] + 1/9 = p_b^T G^-1 p_d   modulo 7.
```
In particular a candidate set of 60 triples of nonmate pairs must make every diagonal right-hand side zero and every off-diagonal lie in {3,4} mod7. This is a necessary constraint, not an assumption about W, an exhaustive graph search, or a proof that any actual triangle violates it. At larger Seidel rank r the same Schur complement has rank at most r−36, not zero.

The [exact determinant and short-vector bound](triangle-wing-short-field.md) applies whether or not the wing tree number is divisible by seven.

[The disconnected twelve-site case](triangle-wing-twelve-currents.md) uses actual far-contact evaluations of mod-seven harmonic currents. In rank 36 it rules out 58 of the 455 three-component multisets and gives further restrictions for the split 12+24.
