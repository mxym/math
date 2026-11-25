# Exact translation-invariant alternating quantum max-flow on a four-cycle

For all integers \(q\ge1\), when both bond and physical dimensions equal \(q\), the maximum alternating flattening rank on a periodic four-cycle with the same complex slice tensor at every site is
\[
 q^2-\bigl(\tbinom q2\bmod 2\bigr).
\]
This matches [Gesmundo–Landsberg–Walter, Theorem I.2](https://arxiv.org/pdf/1801.09106); their discussion reports numerical evidence for tightness in general and gives exact attainment in square dimensions. The deficit pattern also appears numerically in [Hastings](https://arxiv.org/abs/1603.03717). The proof here treats all dimensions simultaneously.

Let \(F_{ab,cd}=\operatorname{tr}(A_aA_cA_bA_d)\), and let \(P\) interchange the two indices in an index pair. Cyclicity of trace gives \(FP=PF=F^{\mathsf T}\). Accordingly \(F\) is block diagonal in the symmetric and skew pair spaces, with symmetric and skew-symmetric blocks respectively. Their dimensions are \(q(q+1)/2\) and \(q(q-1)/2\). The latter block has even rank, proving the upper bound.

For the lower bound take rank-one slices \(A_a=e_a y_a^{\mathsf T}\), the row \(y_a^{\mathsf T}\) being row \(a\) of \(K=I+tX\) for a matrix \(X\) with zero diagonal. Then
\[
 F_{ab,cd}=K_{ac}K_{cb}K_{bd}K_{da}.
\]
In the symmetric block the \(aa\)-rows and columns give the identity at \(t=0\); couplings between them and distinct-pair indices are \(O(t^2)\). For distinct pairs \(a<b\), the leading \(t^2\) term of the diagonal entry, in normalized symmetric pair bases, is \(2X_{ab}X_{ba}\): both arrangements \((a,b)\) and \((b,a)\) contribute. Off-diagonal entries among distinct pairs are \(O(t^3)\), since only equal unordered pairs can make two or more cyclic steps diagonal. Eliminating the equal-index block changes this leading term only at \(O(t^4)\). Thus whenever all \(X_{ab}\ne0\) for \(a\ne b\), the symmetric block has full rank for sufficiently small nonzero \(t\).

In normalized skew pair bases, the leading term is \(t^3B(X)\). Index by oriented edges, with reversing an edge negating its coordinate. Equal and disjoint pairs give zero at leading order. For different edges oriented out of \(a\), substitution gives
\[
 B(X)_{ab,ac}=X_{ab}X_{bc}X_{ca}-X_{ac}X_{cb}X_{ba}.
\]
The matrix is skew-symmetric. We show it can have maximal even rank for every \(q\).

Use the fixed matrix
\[
Y=\begin{pmatrix}0&2&1&1\\1&0&3&1\\3&1&0&2\\1&4&3&0\end{pmatrix}.
\]
The Pfaffian of \(Y-Y^{\mathsf T}\) is \(-7\). The upper-triangular entries of \(B(Y)\), in order \(01,02,03,12,13,23\), listed row by row, are
\[
 (17,-2,17,-2,0);\quad (-7,17,0,-7);\quad(0,-2,-7);\quad(21,21);\quad(21).
\]
The Pfaffian is \(-3682\), obtained by expanding along the first row. Leading submatrices of \(Y\) give starting cases \(q=1,2,3,4\) of ranks \(0,0,2,6\) for \(B\) (the \(01,02\) entry for \(q=3\) is \(17\)).

Suppose \(B(X_q)\) has maximal possible even rank \(r\), and replace \(X_q\) by a block matrix on \(q+4\) vertices with \(X_q\) on old vertices, \(LY\) on new vertices, and all cross entries equal to \(\varepsilon\). In the principal skew submatrix we keep \(r\) old internal edges supporting a nonsingular principal minor, all six new internal edges and all \(4q\) mixed edges. A principal minor of order \(r\) exists in every skew-symmetric matrix of rank \(r\): the \(r/2\)-th wedge power of its alternating form is nonzero, and its coordinate coefficients are the principal Pfaffians.

The two internal blocks have no coupling (the relevant edges are disjoint), and are nonsingular for \(L\ne0\). On the mixed block orient every edge from old to new. Entries from edges sharing an old endpoint give, after dividing by \(\varepsilon^2\), one copy of \(L(Y-Y^{\mathsf T})\) per old endpoint. Edges sharing a new endpoint give entries independent of \(L\) after this division, and disjoint entries vanish. Thus the scaled mixed block is nonsingular for sufficiently large fixed \(L\), by the nonsingular leading block diagonal. Couplings of mixed with internal edges are \(O_L(\varepsilon^2)\) because each contributing triangle uses two cross entries. Eliminating the internal blocks gives an \(O_L(\varepsilon^4)\) Schur correction, so the whole retained principal matrix is nonsingular for sufficiently small nonzero \(\varepsilon\). Its dimension is \(r+6+4q\), which is maximal even rank at size \(q+4\), since the dimension of the edge space increases by the even number \(6+4q\).

The existence of this leading skew minor gives a nonempty Zariski open condition on \(X\) (the complement of the zeros of its nonzero polynomial). The condition \(X_{ab}\ne0\) for every off-diagonal entry is also nonempty and open, so their intersection is nonempty in the affine space of zero-diagonal matrices. Fix \(X\) in the intersection. In the skew block of \(F\), the minor of order \(r\) has nonzero coefficient at \(t^{3r}\), and the symmetric block has a nonzero determinant polynomial by the computation above. A sufficiently small nonzero \(t\) makes both minors nonzero. This proves the matching rank lower bound.

This addresses the four-cycle with identical slices and equal dimensions, not arbitrary periodic lengths or heterogeneous dimensions. The calculation uses rank-one tensor slices and linear algebra, not the Euclidean mean-width pricing theorem.
