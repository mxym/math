# Optimal integral Gaussian coordinates for cyclotomic conductors with two odd primes

[Peikert–Pepin, *Algebraically Structured LWE, Revisited*, §5.3 and Corollary 5.5](https://web.eecs.umich.edu/~cpeikert/pubs/structured-lwe.pdf) transport canonical Gaussian error by a dual trace coordinate map. If the coordinate tests form an integral basis B of an order, spherical input of width s acquires a width-squared matrix s² BᵀB, in canonical orthonormal coordinates. Padding with an independent Gaussian to a spherical output requires width at least s ||B||₂, and that bound is attainable as a covariance statement. Their full middle-product reduction uses a power basis and imposes additional tensor conditions; this note only optimizes the statistical basis step over the larger class of **all** integral bases. [LPR's toolkit, §4](https://sites.cc.gatech.edu/fac/cpeikert/pubs/toolkit.pdf) analyzes the known powerful basis. The result here gives its exact optimality and characterizes the optimizers, including non-product bases, in the stated conductor family. The spanning-tree description of the cyclotomic root configurations belongs to the known [Martin–Reiner cyclotomic matroid](https://arxiv.org/abs/math/0402206) and [Beck–Hoşten integral polytope theory](https://arxiv.org/abs/math/0508136); what requires proof here is that the analytic optimum over arbitrary lattice bases forces those configurations.

## Theorem

Write m for the normalized conductor of a cyclotomic field and R for its full ring of integers. Put mhat=m for odd m, and mhat=m/2 for even m. Use the unscaled canonical inner product, counting both complex conjugates. If m has at most two distinct odd prime factors, then

    min_{B a Z-basis of R} ||B||₂ = sqrt(mhat).

Every minimizing basis consists entirely of shortest vectors. More explicitly, work after dividing lengths by sqrt(mhat). The lattice is an orthogonal sum of identical blocks depending on the distinct odd primes only. All optimal bases are, up to permutation and independent column signs, unions of the following optimal block bases:

* No odd prime: each block is Z, with one unit vector.
* One odd prime p: each block is A*_{p-1}, in its usual normalization. A basis is obtained by omitting one vector from the p projected coordinate unit vectors.
* Two different odd primes p,q: each block is A*_{p-1} tensor A*_{q-1}. Take the p×q projected coordinate unit vectors indexed by edges of the complete bipartite graph. The optimal bases are exactly the complements of spanning trees, giving p^(q-1) q^(p-1) unsigned unordered bases per block.

Prime powers, including any 2-power factor, affect the common scale and the number of independent blocks, not the classification inside them. The theorem does not cover three or more odd prime factors, arbitrary covariance, or independent nonlinear coordinate changes.

### The normalized blocks

Let P_p=I-J/p be orthogonal projection in R^p onto the zero-sum hyperplane H_p. Its image of Z^p is A*_{p-1}, with projected roots u_i=P_pe_i (these are projected coordinate vectors, not roots of the primal A lattice). For conductor p^a, put h=p^{a-1} and group the monomial basis into blocks of powers x^j ζ_p^k, 0≤j<h, 0≤k<p-1, for x=ζ_{p^a}. The Ramanujan sum formula for the trace gives zero between distinct j blocks and gives h(p I-J) as the Gram matrix within a block. Hence division by sqrt(p^a) gives h orthogonal copies of A*_{p-1}. For a 2-power conductor, the Gram matrix is (m/2)I. The canonical embedding of the compositum of coprime prime-power cyclotomics identifies the integral lattice with the tensor product of those factors: the monomial powerful basis is the tensor product of the prime-power power bases, and all combinations of field embeddings occur. Thus Gram factors multiply with the announced normalization. The one-dimensional field Q is immediate.

### A short-vector test and a tensor rank bound

For x∈Z^p, the norm of P_p x squared is p^{-1} sum_{i<j}(x_i-x_j)^2. If some coordinates differ by at least two, the pairs through these two coordinates already contribute at least 2p to the numerator: the pair itself gives at least 4 and each other integer contributes at least 2. Otherwise subtract a constant to write x as the indicator of a subset of size k, giving norm squared k(p-k)/p. In particular the shortest vectors are ±u_i, of norm squared (p-1)/p. The next value is 2(p-2)/p for p≥5, and at least 2 for p=3.

For r linearly independent integer projections X=(P_px_1,...,P_px_r), there is the stronger dimension-r volume bound

    det(XᵀX) ≥ (p-r)/p.

Indeed this determinant is 1/p times the sum of squares of the (r+1)×(r+1) minors of the integer matrix [1,x_1,...,x_r], by Cauchy–Binet and taking the Schur complement of the first column. Choose a nonsingular set of r+1 rows. Every additional row is nonzero (first entry 1), so it can replace at least one of these chosen rows with a nonzero determinant. Those replacements give distinct minors; including the first gives at least p-r. Equality is achieved using r distinct projected coordinate vectors.

Any rank-r tensor v in the integral product of two blocks can be written as sum_{i=1}^r x_i⊗y_i with integral projected factors, each list independent. For example write its coefficient matrix in integral bases, choose a Z-basis of its column module and take the coordinates of the columns in that basis. If the Gram matrices for these two lists are H,J, the squared tensor norm is tr(HJ). By AM–GM on the eigenvalues of H^{1/2} J H^{1/2},

    ||v||² ≥ r ((p-r)(q-r)/(pq))^(1/r).

For 5≤p<q this is >1 for r≥2: for r=2 use 2(1-2/p)≥6/5, and for r≥3 use r/(r+1)^(2/r)>1. Its rank-one tensors that are not products of shortest vectors also have squared norm at least 2(p-2)(q-1)/(pq)>1, using p≥5 and q≥7. For p=3,q≥11 the same conclusions follow from 2 sqrt((q-2)/(3q))>1 for rank two, and (2/3)2(q-2)/q>1 for the longer rank-one case. Thus in these ranges every nonzero vector with squared norm ≤1 is a shortest projected product.

### The two exceptional blocks

For p=3 a tensor can be written u_1⊗y_1+u_2⊗y_2, with
3||v||²=||y_1||²+||y_2||²+||y_1-y_2||². If it has rank two, the three summands are nonzero and cannot all be shortest when q≥5: two linearly independent shortest vectors of A*_{q-1} have a difference of squared norm 2 or 2(q-2)/q. With q=7, any rank-two vector thus has squared norm at least (6+6+10)/21>1. In rank one the only non-shortest vectors at ≤1 are ±u_i⊗(w_j+w_k), j≠k, of squared norm 20/21, where w_j=P_q e_j. If a basis has norm ≤1, for any columns v,w, the positive semidefinite condition on I-BᵀB implies

    |<v,w>|² ≤ (1-||v||²)(1-||w||²).

Two of the longer vectors cannot coexist: their scaled absolute inner product is at least 3/21, larger than the allowed 1/21. A long vector u_i⊗(w_j+w_k) is compatible among shorts only with u_l⊗w_m for l≠i and m outside {j,k}; this follows substituting 3<u_i,u_l>=3·1_{i=l}-1 and 7<w_j,w_m>=7·1_{j=m}-1. There are only 2·5=10 candidates up to sign, so even with the long vector there are not 12 columns. Hence every optimal basis uses only short products also for (3,7).

For (3,5), the length formula and the short-vector test give the following **complete** list up to sign of nonzero vectors with squared norm at most one:

    15 short: u_i ⊗ w_j,                                 norm² =  8/15
    30 medium: u_i ⊗ (w_j+w_k), j≠k,                     norm² = 12/15
    60 long: u_i ⊗ w_j - u_l ⊗ w_k, i≠l, j≠k,            norm² = 14/15.

For the rank-two row pair at most one of the three terms in the norm formula can be above the shortest squared norm 4/5, and that one must be 6/5. If y_1 and y_2 are the short terms, the long difference forces opposite signs. If the short terms include y_1-y_2, one rewrites using u_1+u_2+u_3=0 so that the other two coefficient vectors are short and opposite in sign. This gives exactly the listed rank-two vectors; rank one is immediate. Each shell is a single orbit under row and column permutations and an overall sign.

The only finite check needed is that no 8 distinct sign classes containing a medium or long vector have a positive semidefinite deficit I-BᵀB. The adjacent exact script carries out this exhaustive check as follows. When a long vector exists it fixes one representative from the long orbit and allows all other shells; otherwise, if a medium exists, it fixes a representative from the medium orbit and allows only the first two shells. It filters against the 2×2 principal-minor condition, giving 21 and 31 initial candidates respectively, then extends in increasing index order, discarding a prefix as soon as its deficit Gram matrix is not positive semidefinite. The 15-scaled entries are integers. A zero current pivot requires a zero current row; a nonzero positive pivot uses the exact Schur complement. The complete searches test 50 and 888 extensions, respectively, with no feasible eight-column list in either case. Signs cannot change semidefiniteness, and dependent columns were not excluded, so the check is sufficient for bases. The script also independently checks the tree-complement criterion over all 6,435 eight-edge subsets in this exceptional block.

### From shortest vectors to all minimizers

Every block in the allowed family has minimum squared norm >1/2, including (3,5) with 8/15. Thus if an entire basis has operator norm at most one in normalized coordinates, each column is supported in exactly one block. Each block must then get a full basis of its own; either independence plus cardinality or generation shows this. Our short-vector tests and exceptional cases force all the columns to be projected coordinate products (or the one-dimensional analogues).

For one prime, the p distinct projected coordinate vectors form a Parseval frame, and any p-1 are a lattice basis since their only relation is the all-ones relation. The operator norm is one: the omitted vector contributes rank one to the difference between the frame operator and the identity, and p-1≥2.

For two primes, let P=P_p⊗P_q. If S is a set of (p-1)(q-1) distinct projected edges, its frame operator on H_p⊗H_q is P diag(1_S)P. It is bounded above by I, and the omitted edges number p+q-1, which is smaller than (p-1)(q-1) for all distinct odd primes (including 3,5). Thus the omitted frame operator has a kernel and the selected operator has an eigenvalue one. The edge basis criterion is exact: orthogonality to the projected edges in S is the balanced row-and-column circulation space supported on the complement graph, which vanishes if and only if that graph is acyclic (cycle circulations are nonzero, forests have none by leaf peeling). The complement has p+q-1 edges and is therefore a spanning tree when acyclic. For each omitted tree edge, its fundamental cut yields an integral cut vector, orthogonal to all circulations, with coefficients ±1 and with just that one omitted edge nonzero. Projecting the cut expresses the omitted edge as an integral combination of selected edges, proving integral generation. The tree count follows from the matrix-tree theorem, since the positive Laplacian eigenvalues of K_{p,q} are q (p-1 times), p (q-1 times), and p+q.

In particular the powerful tensor basis attains norm one in normalized coordinates; since every candidate at norm at most one also attains one, the bound is sharp. The optimization concerns the canonical-to-coordinate Gaussian covariance step only. It supplies no algorithm for Ring-LWE and does not imply that every geometrically minimizing basis also admits the Hankel tensor relation of the original reduction.
