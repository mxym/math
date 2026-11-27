# Thirteen missing order-nine cardinalities

A quantum Latin square of order \(n\) is an \(n\)-by-\(n\) array of
unit vectors in \(\mathbb C^n\) in which each row and column is an
orthonormal basis. Its cardinality counts distinct rays, so global
phase multipliers do not matter. All arrays below use zero-based
cell and coordinate indices. Any displayed unnormalized nonzero vector
is divided by its Euclidean norm.

## 1. Mixed Schur products

If \(H,K\) have unimodular entries and \(H^*H=K^*K=nI\), the cells
\[
 X_{ab}(k)=n^{-1/2} H_{ka}K_{\sigma(k),b}
\]
are a quantum Latin square for every permutation \(\sigma\).
Fixing \(a\) gives the columns of a unitary obtained by row-permuting
\(K/\sqrt n\) and then multiplying coordinates by the unimodular
entries of column \(a\) of \(H\). Fixing \(b\) gives the analogous
unitary from \(H/\sqrt n\). This is a prior construction; see sources.

### Nine sixth-root witnesses

Let \(M_j\) be the \(j\)-th matrix in the 17-record BH(9,6) file from
the original Lampio–Östergård–Szöllősi catalog. The record index is
one-based. The matrix entries are the sixth roots encoded there in
row-major order. In the table \(j^\top\) means the transpose of \(M_j\).
Each permutation is written as \((\sigma(0),\ldots,\sigma(8))\).

| Cardinality | \(H\) | \(K\) | \(\sigma\) |
|---:|:---:|:---:|:---|
| 60 | \(11^\top\) | 8 | (7,2,8,4,5,6,3,0,1) |
| 62 | \(7^\top\) | \(7^\top\) | (7,2,1,5,8,6,3,0,4) |
| 65 | 7 | 3 | (2,4,5,6,0,3,1,8,7) |
| 66 | 4 | \(1^\top\) | (1,5,3,6,7,4,0,2,8) |
| 68 | \(8^\top\) | \(7^\top\) | (6,3,7,0,5,4,1,2,8) |
| 69 | \(4^\top\) | \(14^\top\) | (5,3,7,1,2,4,0,8,6) |
| 70 | \(8^\top\) | \(8^\top\) | (0,7,5,4,3,2,6,1,8) |
| 71 | \(7^\top\) | 7 | (8,5,7,3,4,1,0,2,6) |
| 74 | 8 | 8 | (8,4,0,3,6,2,1,7,5) |

If \(A,B\) are the two exponent matrices, the ray key is the vector
of residues
\[
 (A_{ka}+B_{\sigma(k),b}-A_{0a}-B_{\sigma(0),b})_{k=0}^{8}
 \pmod 6 .
\]
The first coordinate is zero, so it has removed the global phase
without ambiguity. The finite certificate is exhaustive: form the
81 keys, compare all \(\binom{81}{2}=3240\) unordered pairs, and
count their classes. One implementation also builds the actual
unnormalized vectors in \(\mathbb Q(\sqrt{-3})\) with exact integer
quadratic-field pairs and rechecks the Gram matrices and each pair
of rays by dephasing algebraically. It checks the original Hadamard
axioms for all 17 records, all 810 upper-triangular Gram entries for
each witness, and agrees with the residue test on every cell pair.

### The three-value witness for 73

Write the field as \(\mathbb F_3[u]/(u^2+1)\) and encode \(a+bu\)
by \(a+3b\). The nonzero squares have encodings \(1,2,3,6\).
Let \(\chi\) be the quadratic character with \(\chi(0)=0\). Take
\[
 \xi=\frac{1+i\sqrt{15}}4,\qquad
 H_{ka}=K_{ka}=\xi^{\chi(k-a)},\qquad
 \sigma=(0,5,7,4,6,2,8,1,3).
\]
For \(x\) with encoding 0 through 8, the values of
\(\chi(x)-\chi(x-1)\) are
\((-1,1,0,2,-2,0,2,-2,0)\). Multiplication by any fixed nonzero
column shift changes its argument bijectively and at most flips the
sign of this histogram. The inner product of distinct columns is
therefore \(3+(\xi+\xi^{-1})+2(\xi^2+\xi^{-2})=0\), using
\(\xi+\xi^{-1}=1/2\) and \(\xi^2+\xi^{-2}=-7/4\). Norms squared
are nine. The phase is not a root of unity, since otherwise \(1/2\)
would be an algebraic integer. Every exponent vector has sum zero.
Consequently two cells give the same ray exactly when their exponent
vectors coincide. Exact comparison gives 72 singleton classes and
one class of size nine. The same verifier independently verifies
the result using \(\mathbb Q(\sqrt{-15})\) and all 3240 cell pairs.

## 2. A block splice for 34, 61, and 67

Let \(U=\mathbb C^4\) and \(V=\mathbb C^5\); the final ambient space is
\(U\oplus V\). Partition both row and column indices into \(A\) of size
4 and \(B\) of size 5 (in that order). The following ingredients suffice:

- \(P\) is a quantum Latin square of order four in \(U\).
- \(T\) is a partially filled \(5\)-by-\(5\) array in \(U\) with
  empty diagonal. Each of its punctured rows and columns is an
  orthonormal basis of \(U\).
- \(R,S\) are quantum Latin squares of order five in \(V\), and
  \(R\)'s last row \((w_b)_{b=0}^{4}\) agrees ray by ray with the last
  column of \(S\). Rephase that column if necessary.

Fill the four blocks as follows:
\[
 \begin{array}{c|cc}
       & A & B\\\hline
 A & P & R\text{ without its last row}\\
 B & S\text{ without its last column} & T\text{ with }w_b\text{ in cell }(b,b)
 \end{array}
\]
The upper and lower rows each contain a basis of both \(U\) and \(V\),
by their respective source row conditions; likewise the left and right
columns each contain a basis of both spaces. Thus the result is a
quantum Latin square of order nine. The rays in its two orthogonal
subspaces are disjoint, and it includes all rays in the four
ingredients, so its cardinality is
\[
 |\operatorname{rays}(P)\cup\operatorname{rays}(T)|
 +|\operatorname{rays}(R)\cup\operatorname{rays}(S)|.
\]

**Maximum squares for orders four and five.** In order \(d\) take the
mixed Schur product of the Fourier matrix with its row-permuted
copy, so the cell coordinates are proportional to
\(\zeta_d^{ka+\rho(k)b}\). Use \(\rho_4=(0,1,3,2)\) and
\(\rho_5=(0,1,2,4,3)\). Since \(\rho_d(0)=0\), equality of two
rays implies \(kA+\rho_d(k)B=0\) in \(\mathbb Z/d\mathbb Z\)
for all \(k\), where \((A,B)\) are the two index differences.
At \(k=1\) this gives \(A+B=0\). At \(k=2\) for \(d=4\), or
\(k=3\) for \(d=5\), it then gives \(B=0\), hence \(A=0\).
Thus all \(d^2\) rays differ. Their vectors are flat in the displayed
coordinates (all coordinate moduli equal and nonzero).

**The common \(V\) ingredients.** Take \(R\) to be this maximum
order-five square, moving row zero to the last position and retaining
the other rows in order. One choice of \(S\) is classical on the basis
\(w\), namely \(S_{ba}=w_{b+a+1\bmod 5}\), and then the union has
25 rays. For the second choice put
\[
 Ww_j=\zeta_7^j w_j,\qquad S_{ba}=W R_{ab} .
\]
Its last column has the specified rays, and \(S\) has 25 rays.
Their intersection has precisely the five rays of the \(w\) basis:
each remaining vector in \(R\) has at least two nonzero coordinates
in that basis, and so does every non-basis vector in \(S\).
The ratios of nonzero coordinates from \(R\) lie in
\(\mathbb Q(\zeta_5)\), since inner products of our original
normalized Fourier-form vectors are sums of powers of \(\zeta_5\)
divided by 5. If a non-basis ray in \(R\) agreed with a ray of
\(W R\), division of a coordinate ratio for two distinct nonzero
positions \(i,j\) would put \(\zeta_7^{i-j}\) in
\(\mathbb Q(\zeta_5)\). This is impossible because its degree over
\(\mathbb Q\) is 6, while the field degree is 4. The union therefore
has \(25+25-5=45\) rays.

**34 = 9 + 25.** Begin \(P\) with the classical Klein-four square
whose symbol at \((i,j)\) is \(i\mathbin{\mathrm{xor}}j\) in an
orthonormal basis \(e_0,\ldots,e_3\). In the top-left \(2\)-by-\(2\)
intercalate replace symbols 0 and 1 by \((e_0+e_1)/\sqrt2\)
and \((e_0-e_1)/\sqrt2\), respectively. Every affected row and
column still uses a basis of the same two-dimensional subspace.
The result has exactly six rays. Apply to all cells the orthogonal
map \(I-\frac23J_3\) on the first three coordinates (where \(J_3\)
is the all-ones matrix) and identity on the fourth. Its images of
\(e_0,e_1,e_2,e_0+e_1,e_0-e_1\) all have at least two nonzero
coordinates. Use for \(T\) the cyclic puncture
\(T_{ij}=e_{(j-i\bmod5)-1}\) for \(i\ne j\).
The two \(U\) sets share exactly the ray of \(e_3\), so their union
has \(6+4-1=9\) rays. Use the classical choice for \(S\).

**61 = 16 + 45.** Take the maximum order-four \(P\) described above.
Use the same cyclic \(T\) formula but with \(e_0,\ldots,e_3\)
replaced by the basis in row zero of \(P\). Its four rays add none
to \(P\). Use the second choice for \(S\).

**67 = 22 + 45.** Use the same maximum flat \(P\).
For \(T\) start from this classical symbol array:
\[
 \begin{pmatrix}
 4&3&2&1&0\\
 2&4&3&0&1\\
 1&0&4&3&2\\
 0&2&1&4&3\\
 3&1&0&2&4
 \end{pmatrix}.
\]
Each row and column is a permutation, and the diagonal consists of 4.
Delete the diagonal. Initially assign \(e_s\) to symbol \(s\ne4\).
In rows 0,1 and columns 3,4, replace 0 and 1 with the two rotated
rays from the 34 construction, without the subsequent three-coordinate
map. This is an intercalate, so punctured row and column bases are
preserved. The original four rays remain, and the two new rays give
six in \(T\). All have at least one zero coordinate and are
therefore disjoint from the flat rays of \(P\). Use the second
choice for \(S\).

An independent direct checker builds these actual vectors, omitting
only nonzero common scalars. It uses \(\mathbb Q(i)\) for \(U\) and
\(\mathbb Q(\zeta_{35})\) for \(V\). It verifies 810 row/column Gram
entries per square, including all diagonal entries being nonzero.
It compares all 3240 unordered cell pairs by exact cross-products,
without using the analytic cardinality argument. For a negative
control replacing the second maximum square by its classical
basis square changes the 61 construction to cardinality 41.

## 3. Exact scope of the conclusion

The thirteen witnesses are precisely the cases in the uncertain
order-nine row of Zhang–Lv–Cao's Table 6. Combining them with the
attainable values in that row gives every integer from 9 through 81
except 10. A basis row and the total cell count give the general
bounds 9 and 81. Their Theorem 1.1(1) records the established
impossibility of order plus one, here 10. Therefore the spectrum
is exact. Theorem 1.2 of that paper is not invoked for order nine,
which it explicitly excludes.
