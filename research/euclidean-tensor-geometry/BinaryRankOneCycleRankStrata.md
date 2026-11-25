# Exact alternating ranks for binary rank-one slices

This technical addendum classifies the rank of each binary rank-one witness. The optimal rank at physical and bond dimension two was already proved by a different argument in the [immutable v1.0.0 archive](https://github.com/mxym/math/blob/16a0c94c6893cff67780fbb64b0c4bc8addffbf1/paper.md). This note is not a new claim about that optimum. The symmetric rank-one witness family and the universal bond-two upper bound come from [Gesmundo–Landsberg–Walter, Theorem I.5 and §IV.1](https://arxiv.org/html/1801.09106#S4.SS1).

For any bond dimension, take two slices \(A_i=x_i y_i^{\mathsf T}\), allowing zero slices, and put \(K_{ij}=y_i^{\mathsf T}x_j\). Let \(K=\begin{pmatrix}a&b\\c&d\end{pmatrix}\), and let \(s\ge2\) be the half-length. Over \(\mathbb C\) the alternating rank is exactly as follows (read from the top down):

| Condition | Rank |
| --- | ---: |
| \(bc=0\) | Number of nonzero entries among \(a,d\) |
| \(bc\ne0,\ a=d=0\) | \(2\) |
| \(bc\ne0,\) precisely one of \(a,d\) is zero | Number of labeled cyclic binary words of length \(s\) avoiding \(101\), including across the boundary |
| \(adbc\ne0,\ ad=bc\) | \(1\) |
| \(adbc\ne0,\ ad=-bc\) | \(2^{s-1}\) |
| All remaining cases | \(3\cdot2^{s-2}\) |

The same formulas hold over any field of characteristic not two, since rank is unchanged by passing to its algebraic closure. Exactly 9,604 finite-field cross-checks, spanning all overlap matrices over \(\mathbb F_7\) and all half-lengths \(s=2,3,4,5\), agree with the formula.

**Reduction.** The trace of a cyclic word is the product of its neighboring \(K\)-entries. Scaling the rows of \(K\) rescales the two slices and hence changes flattening rows and columns only by nonzero scalar factors. Diagonal similarity of \(K\) changes no cyclic product at all. If \(adbc\ne0\), row scaling makes both diagonal entries equal to a nonzero \(\mu\), then diagonal similarity makes the off-diagonal entries both equal to \(\nu\ne0\), with \(\nu^2/\mu^2=bc/ad\).

**Zeros.** If \(bc=0\), only monochromatic cyclic words can contribute. If \(a=d=0\) and \(bc\ne0\), only the two fully alternating words contribute, giving rank two. If exactly one diagonal entry is zero, assume \(a=0\) by interchanging symbols. For odd word \(u\), its row factors are \(f_{u_i u_{i+1}}\) with \(f_{ij}=(K_{i0}K_{0j},K_{i1}K_{1j})\). The three factors \(f_{00},f_{01},f_{10}\) are nonzero multiples of \((0,1)\); \(f_{11}=(bc,d^2)\) is independent of them. Thus the row rank counts the distinct index sets \(U=\{i:u_i=u_{i+1}=1\}\). The cyclic indicator of \(U\) cannot contain \(101\). Conversely, for an indicator avoiding \(101\), set \(u_i=1\) precisely when \(i\) is incident to an edge of \(U\). Every unmarked edge incident to two such vertices would have a marked edge on both sides, contrary to avoidance. This proves the count, also for \(s=2\) with cyclic indexing.

**Walsh calculation in the normalized nonzero case.** Represent the symbols by spins \(\pm1\). At fixed even word \(v\), Walsh-transform the odd positions with row index \(S\subseteq[s]\). For \(U=\{i:v_{i-1}=v_i\}\), the local factors for \(i\in U\) are \(\mu^2+\nu^2\) if \(i\notin S\) and \((\mu^2-\nu^2)v_i\) if \(i\in S\). For \(i\notin U\) they are \(2\mu\nu\) if \(i\notin S\) and zero otherwise. If \(\mu^2=\nu^2\), only the empty Walsh row survives, and it is nonzero. If \(\mu^2=-\nu^2\), each column is a nonzero multiple of the single row \(S=U\). There are \(2^{s-1}\) feasible \(U\), namely those with parity \(s\bmod2\), because the number of spin changes around the cycle is even.

Otherwise invertible row and column scalings give entries \(\mathbf1_{S\subseteq U}\prod_{i\in S}v_i\). Each \(U\) comes from one pair \(v,-v\); taking the columns' sum and difference gives two blocks, each supported on one row parity. In matching parity, \(S=U\) supplies a triangular minor of size \(2^{s-1}\). In opposite parity, keep the columns with \(1\in U\), selecting rows \(S=U\setminus\{1\}\). Those rows omit \(1\), so inclusion is exactly inclusion in \(U\setminus\{1\}\); ordering by size gives a second triangular minor of size \(2^{s-2}\). Both diagonals are nonzero. For the upper bound over \(\mathbb C\), any overlap matrix is realized by two rank-one slices at bond dimension two, and Theorem I.5 applies. For arbitrary characteristic not two, the upper bound transfers by the integer-polynomial identity: each minor of larger size for the four-variable overlap matrix is a polynomial with integer coefficients, identically zero over \(\mathbb C\), hence zero in every characteristic. The two minors give the exact lower bound directly in every characteristic not two.
