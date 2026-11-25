# Exact alternating quantum max-flow of the eight-cycle in further dimensions

**Yongxian Zhang.** AI-assisted research note with an exact arithmetic certificate.

Use [Gesmundo–Landsberg–Walter's periodic translation-invariant model](https://arxiv.org/abs/1801.09106): one common \(q\)-tuple of \(q\times q\) matrices on all eight vertices, flattened across the odd/even split. Over the complex numbers the exact quantum max-flow at \(q=5,6,7,8\), respectively, is
\[
625,\quad1296,\quad2400,\quad4096.
\]
The same problem for arbitrary \(q\) is not solved by this note.

For \(M\) the alternating flattening and \(P\) the cyclic shift on tuple indices of length four, cyclicity of trace gives \(M^{\mathsf T}=MP\) and \(MP=PM\). Thus the restriction of the ordinary bilinear form with matrix \(M\) to the \(-1\) eigenspace of \(P\) is skew-symmetric, and that eigenspace pairs to zero with the other eigenspaces. Its dimension is \((q^4-2q+q^2)/4\), by the four permutation traces. When \(q=7\) the dimension is \(609\), odd, giving \(\operatorname{rank}(M)\le q^4-1=2400\). In the other three cases the size of \(M\) already bounds its rank by the stated value.

For the lower bounds, write indices as \(0,\dots,q-1\), take \(K_{ij}=(i+1)^j\) over the integers, and set \(A_i=e_iK_{i,*}\). These choices give
\[
M_{u,v}=\prod_{j=0}^3 K_{u_j,v_j}K_{v_j,u_{j+1\bmod4}} .
\]
The standalone C++ checker constructs this matrix mod 1009 and uses exact Gaussian elimination; it finds the four ranks above. Nonzero minors modulo 1009 are nonzero over the integers, hence over \(\mathbb C\). Run `c++ -O3 -std=c++17 verify.cpp -o verify && ./verify` in this directory.

**Multiplicative family.** Given common local tensors attaining full alternating rank at dimensions \(q_1\) and \(q_2\), take the tensor products \(A_i^{(1)}\otimes A_j^{(2)}\) as the shared slices for dimension \(q_1q_2\). The eight-vertex alternating flattening is, up to index permutations, the Kronecker product of the original flattenings. Its rank is \((q_1q_2)^4\). Thus the checker and [GLW Remark I.6](https://arxiv.org/pdf/1801.09106) for squares give full rank for every \(q=a^2 5^b 6^c 8^d\), \(a\ge1\) and \(b,c,d\ge0\). In particular this covers infinitely many nonsquare dimensions. This conclusion is about the single-copy translation-invariant alternating model and does not follow for general \(q\) merely from the small checks.
