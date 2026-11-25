# Exact alternating max-flow on the six-cycle and the ternary eight-cycle

**Yongxian Zhang.** Research note (AI-assisted proof development and verification).

Work over \(\mathbb C\), with one common \(q\)-tuple of \(q\)-by-\(q\) matrices \(A_i\) defining a translation-invariant tensor on the cycle. Flatten the trace tensor into its alternating legs:
\[
 M_{u,v}=\operatorname{tr}(A_{u_0}A_{v_0}\cdots A_{u_{d-1}}A_{v_{d-1}}),
 \qquad u,v\in [q]^d.
\]
In [Gesmundo–Landsberg–Walter's notation](https://arxiv.org/abs/1801.09106), the maximum rank of \(M\) is the periodic translation-invariant quantum max-flow \(\operatorname{QMF}'(C_{2d},(\mathrm{odd},\mathrm{even}),q)\). We prove that it is \(q^3\) for \(C_6\) and every \(q\ge3\) (the binary value \(6\) is already known), and \(80\) for \(C_8\) and \(q=3\). These are single-copy statements, not graph-tensor asymptotic rank statements.

## Six-cycle

With \(A_i=e_i K_{i,*}\) and \(K_{ij}=1\) for \(i=j\), \(K_{ij}=t\) otherwise, the trace is a power \(t^{h(u,v)}\), where
\[
 h(u,v)=\sum_{j=0}^2 \big( {\bf1}_{u_j\ne v_j}+{\bf1}_{v_j\ne u_{j+1}}\big)
\]
with cyclic subscripts. Let \(r(u)\) count the cyclic changes \(u_j\ne u_{j+1}\); then \(h(u,v)\ge r(u)\). Divide row \(u\) by \(t^{r(u)}\) and write the resulting polynomial matrix as \(P+tQ+O(t^2)\). Below, a submatrix indexed by word lists \(X,Y\) is denoted by \(P(X,Y)\), and similarly for \(Q\).

When \(h(u,v)=r(u)\), every \(v_j\) is an endpoint of \((u_j,u_{j+1})\). Thus \(\operatorname{supp}v\subseteq\operatorname{supp}u\) and \(P\) is block lower triangular by support inclusion. For one-symbol supports the diagonal block is the identity. For a three-symbol support \(T\), the diagonal block is \(I+S\) with the cyclic shift \(S\) of three positions. Indeed retaining all three distinct symbols forces the endpoint choices to be the same at all three positions (all stay or all shift). This block is invertible: \(S^3=I\).

For a two-symbol support \(\{a,b\}\), list the words in minority order: first the three with minority \(b\) at positions \(0,1,2\), then those with minority \(a\) in the same order. The diagonal block has rank \(4\) and both kernels have basis columns
\[
 Z=\begin{pmatrix}-1&-1\\1&0\\0&1\\-1&-1\\1&0\\0&1\end{pmatrix}.
\]
The corresponding left kernel vectors extend by zero to the other supports: pairing these vectors with columns on one-symbol supports also vanishes. Both assertions are direct two-symbol checks, included in the certificate. For a right kernel vector on a pair \(Y\), the singleton coordinates are zero and the triple coordinates for supports \(T\supset Y\) are corrected to \(-P(T,T)^{-1}P(T,Y)Z\). All other triple coordinates vanish. These vectors give full bases because the other diagonal blocks are invertible.

The first-order map from right kernel to left cokernel is measured by the \(2\)-by-\(2\) blocks pairing these bases via \(Q\). For pair supports \(X,Y\), contributions from triple corrections arise only from a triple \(T\) containing both pairs: \(P(T,Y)\) forces \(Y\subset T\), and \(Q(X,T)\) can introduce only one new symbol, leaving both symbols of \(X\) in the triple. For the latter observation, of the three positions in a pair row \(u\), exactly one has equal neighboring symbols. An excess of one in \(h-r\) is possible only by selecting a third symbol at one of the two unequal positions and otherwise making a minimum choice. A three-symbol column must consequently contain the two original symbols. Also \(Q(X,X)=0\), since in the same two-symbol alphabet the excess is either \(0\) or \(2\). Distinct disjoint pairs have \(Q(X,Y)=0\) and no shared triple. For distinct adjacent pairs there is one shared triple; the direct term and its correction can be computed together on that triple. Renaming letters (even swapping the two symbols of a pair) does not change our basis on minority positions. The three-symbol certificate below gives
\[
 Z^\top\!\big[Q(X,Y)-Q(X,T)P(T,T)^{-1}P(T,Y)\big] Z
 =
 \begin{cases}
 -H,&X=Y,\\
 H,&|X\cap Y|=1,
 \end{cases}
 \qquad
 H=\begin{pmatrix}2&-2\\4&2\end{pmatrix}.
\]
For \(X=Y\) this is counted once for each of its \(q-2\) triples, with no direct term. Therefore the whole first-order map equals
\[
 (A_{\mathrm{line}(K_q)}-(q-2)I)\otimes H .
\]
It is invertible: if \(B\) is the unsigned vertex-edge incidence matrix, the first factor is \(B^\top B-qI\). Since \(BB^\top=(q-2)I+J\), its possible eigenvalues are \(q-2,-2,-q\), all nonzero for \(q\ge3\). Also \(\det H=12\). Choosing separate constant row and column bases with the kernels at the end, the leading invertible block is a complement to these kernels and the lower-right Schur complement starts with this invertible first-order map. Hence the determinant is not identically zero in \(t\); a nonzero complex \(t\) gives rank \(q^3\).

## Eight-cycle, \(q=3\)

Write \(\rho(u_0,u_1,u_2,u_3)=(u_1,u_2,u_3,u_0)\) and \(P_\rho e_u=e_{\rho u}\). Cyclicity of trace gives \(M^\top=MP_\rho\) and \(MP_\rho=P_\rho M\). Thus on the \(-1\) eigenspace of \(P_\rho\), \(M\) gives a skew-symmetric pairing, as in GLW §II.B. In detail, this eigenspace is orthogonal under the ordinary bilinear form to each of the other rotation eigenspaces and has a nondegenerate induced form. The eigenspace has dimension \((3^4-3+3^2-3)/4=21\), by the traces of the four powers of \(P_\rho\). The skew block is singular, so \(\operatorname{rank}M\le80\).

For equality take \(A_i=e_i K_{i,*}\) with
\[
 K=\begin{pmatrix}1&1&1\\1&2&3\\1&4&5\end{pmatrix}.
\]
Then \(M_{u,v}=\prod_j K_{u_jv_j} K_{v_ju_{j+1}}\). Index words in lexicographic order on \(\{0,1,2\}^4\), delete row and column \(79\) with zero-based indexing (word \((2,2,2,1)\)). The remaining determinant is \(94\) modulo \(101\), giving a nonzero integer minor.

## Reproduction

Run the accompanying certificate with Python 3 and SymPy. It verifies the local rational computations and the integer minor reduced modulo \(101\) using exact arithmetic. The proof does not require any numerical optimization or a general-purpose determinant search.
