# Exact asymptotic rank for odd complete graph tensors

Let \(G\) have \(n\) vertices, with one tensor leg per vertex and a shared binary identity tensor on each edge. Denote the resulting graph tensor by \(T_G\), and put \(\Gamma_F(G)=\log_2\widetilde R_F(T_G)\). Combining the public formal rectangular exponent theorem in OpenAI's Euclidean tensor geometry release with the complete-graph upper bound yields
\[
 \Gamma_F(K_n)=n^2/4\qquad(n\ge2)
\]
over every field \(F\). The new consequence concerns odd \(n\), where the elementary cut lower bound gives only \((n^2-1)/4\). The same result holds for any \(n\)-vertex graph with a partition into three nonempty parts, each of size at most \(n/2\), such that all edges between different parts are present.

## Inputs and scope

The upper bound is [Zhou, arXiv:2610.34273v3, Theorem 1.1](https://arxiv.org/html/2610.34273v3), independently also obtained by [Khoruzhii](https://lemmata.iol.berlin/tensor-rank). Both give the odd interval before applying the following additional input. The exact rectangular exponent we use is OpenAI's [pinned Lean theorem \(\texttt{rectangular\_exponent}\)](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/SpectralBooks/ExactExponent.lean#L45), with the [formal polynomial-identity circuit model defined here](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/SpectralBooks/ArithmeticExponent.lean#L20). Its precise rectangular formula is stronger than the rectangular corollaries written out in the companion PDF. An [independent report of a standard Lean-kernel replay](https://lilting.ch/en/articles/matrix-multiplication-exponent-nine-fourths-openai) includes the rectangular declaration and reports only Lean's standard axioms for all three exponent theorems. We use that source theorem as a result; we do not reprove it or claim to have built its full Lean development ourselves.

For positive sorted wire weights \(x\ge y\ge z\), the source gives formal rectangular exponent
\[
 \omega_F(x,y,z)=x+y+\frac{[\max(0,(x+y)z-xy)]^2}{4xyz}.
\]
Here wire exponent \(x\) means a side length growing as the base to power \(x\), not a tensor-leg dimension.

## From partitions to matrix multiplication

Merge the tensor legs of each of three groups into one leg. Rank cannot increase, since a decomposable summand on the original legs remains a decomposable summand across the three groups. In each merged leg, all its internal edges give a fixed tensor factor. Apply a linear functional taking value one on that factor, leaving the product of the cross-edge identities. All operations work unchanged on each Kronecker power. The resulting three-leg tensor is the matrix multiplication tensor with sides \(2^{x},2^{y},2^{z}\), where the three wire exponents count the cross edges between each pair of groups. This follows directly by writing the three cross-edge labels in the three vertex-group legs as \((i,j),(j,k),(k,i)\).

For clarity, its log asymptotic rank is at least the formal circuit exponent in the source. For any fixed \(k\), choose a rank decomposition of size \(r\) of the tensor with sides \(2^{kx},2^{ky},2^{kz}\). It gives a bilinear scheme on blocks: take fixed linear combinations of input blocks, perform \(r\) recursive products, and linearly combine outputs. Let \(L=\max(2^{k(x+y)},2^{k(y+z)},2^{k(x+z)})\), the maximum number of scalar entries in an input or output block at the base scale. Flattening rank gives \(r\ge L\). At recursion depth \(j\), all the nonrecursive linear combinations cost \(O(L^{j-1})\) at the top (the constant depends on the fixed scheme), so total cost is \(O(jr^j)\). Pad arbitrary base size up to a power of \(2^k\) and absorb the logarithmic factor in the positive exponent slack. Thus \(\omega_F(x,y,z)\le \log_2(r)/k\). Apply this to optimal rank at each \(k\) and take the infimum. No identification with finite-size circuit complexity is needed.

## Closing the interval

Let the three group sizes in decreasing order be \(a\ge b\ge c>0\), and assume \(a\le b+c\). If all cross edges are present, then \((x,y,z)=(ab,ac,bc)\). In the formula,
\[
 (x+y)z-xy=abc(b+c-a)\ge0,\qquad 4xyz=4a^2b^2c^2.
\]
Consequently the grouped lower bound is
\[
 a(b+c)+(b+c-a)^2/4=(a+b+c)^2/4=n^2/4.
\]
The target graph is a subgraph of \(K_n\), so its tensor is obtained from \(T_{K_n}\) by projecting every unwanted edge label to one fixed value at both endpoints. Its asymptotic rank therefore has upper bound \(n^2/4\) in the logarithmic normalization. This proves equality.

For \(K_{2m+1}\) take group sizes \(m,m,1\); even \(n\) already follows from the balanced two-way cut. More generally a complete multipartite graph with no part larger than half the total and at least three parts can merge the two smallest parts until three groups remain. At each step those two parts have sum at most \(n/2\), since at least two other parts are at least as large; cross edges stay present. This proves the same exact value. These deductions do not determine the asymptotic rank of arbitrary graphs.
