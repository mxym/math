# Exact binary periodic alternating ranks in characteristic two

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review claimed.

Use the single-shared-tensor periodic model of [Gesmundo–Landsberg–Walter (GLW)](https://arxiv.org/abs/1801.09106), with both physical and bond dimensions two. For two slices \(A_0,A_1\in\mathrm{Mat}_2(F)\) and half-length \(s\ge2\), the flattened matrix has entries
\[
 M_{u,v}=\operatorname{tr}(A_{u_1}A_{v_1}\cdots A_{u_s}A_{v_s})
\]
on binary words of length \(s\). The maximal rank for any characteristic-two field \(F\) is as follows:
\[
 \max\operatorname{rank} M=
 \begin{cases}
 3\cdot 2^{s-2},&|F|>2,\\
 2,5,10,17,&F=\mathbb F_2,\quad s=2,3,4,5\text{ respectively},\\
 2^{s-1},&F=\mathbb F_2,\quad s\ge6.
 \end{cases}
\]
These are maxima over slices in the named field, not over the algebraic closure. The earlier [immutable complex proof](https://github.com/mxym/math/releases/tag/periodic-ti-quantum-max-flow-v1.0.0) and [characteristic-not-two overlap classification](https://github.com/mxym/math/blob/d67d63ebb0d061719a91655d8944e5192c885db6/research/euclidean-tensor-geometry/BinaryRankOneCycleRankStrata.md) treated different scopes.

## Every rank-one overlap stratum

For \(A_i=x_i y_i^{\mathsf T}\), define \(K_{ij}=y_i^{\mathsf T}x_j\) and write \(K=\begin{pmatrix}a&b\\c&d\end{pmatrix}\). The resulting words have trace equal to the cyclic product of neighboring \(K\)-entries. Let \(c_s\) count labeled (not up to rotation) binary words of length \(s\) cyclically avoiding \(101\). The rank is:

| Condition | Rank |
| --- | ---: |
| \(bc=0\) | Number of nonzero entries among \(a,d\) |
| \(bc\ne0,\ a=d=0\) | \(2\) |
| \(bc\ne0,\) exactly one of \(a,d\) is zero | \(c_s\) |
| \(adbc\ne0,\ ad=bc\) | \(1\) |
| \(adbc\ne0,\ ad\ne bc\) | \(3\cdot2^{s-2}\) |

The cases with zeros follow by the support argument in the linked rank-one note, which works also in characteristic two. In the single-zero case, for example \(a=0\), each row is a tensor product of the two independent factors \((0,1)\) and \((bc,d^2)\), up to nonzero scaling. The second factor occurs precisely on the edges \(i\) with \(u_i=u_{i+1}=1\). The indicator of this edge set avoids \(101\); conversely, choose \(u_i=1\) iff vertex \(i\) touches a marked edge of an avoiding pattern. An unmarked edge between two chosen vertices would be surrounded by two marked ones, contrary to avoidance. Distinct attainable factor patterns are linearly independent.

For nonzero entries pass to an algebraic closure without changing rank. Nonzero row scaling of \(K\) rescales the physical slices and hence the flattening rows and columns; diagonal similarity of \(K\) leaves cyclic products unchanged. These operations put \(K=\begin{pmatrix}1&t\\t&1\end{pmatrix}\), with \(t^2=bc/ad\). If \(t^2=1\), the trace tensor has rank one. Otherwise change the odd-coordinate basis to \(e=(1,1)\) and \(f=(0,1)\). For a fixed even word \(v\), let \(U=\{i:v_{i-1}=v_i\}\). Its column factors are \(te\) at a change and \(e+(1+t^2)f\) or \(t^2e+(1+t^2)f\) at an equality, according to the common bit. Thus each of the two words realizing \(U\) can be rescaled to coefficient one at tensor coordinate \(U\) (where \(U\) indicates the \(f\)-positions). All other coordinates are subsets of \(U\). The two words realizing \(U\) are complements, and every \(U\) with \(|U|\equiv s\pmod2\) occurs. In the difference of the two rescaled columns, coordinate \(U\) cancels and every one-element deletion of \(U\) has coefficient one, because the normalized local \(e\) coefficients differ by one in characteristic two.

Choose one original column per \(U\), and one difference column per \(U\) containing 1. Choose the corresponding rows \(U\) and \(U\setminus\{1\}\), respectively. Order by the selected row sizes. The columns are supported only in degrees no larger than their selected row, and those of different type have different leading-degree parity. For an original column the only leading row is \(U\). For a difference column the only selected row at leading degree it can meet is \(U\setminus\{1\}\): every other one-element deletion still contains 1. This yields a triangular minor of size \(2^{s-1}+2^{s-2}\) with unit diagonal. The universal matching upper bound follows from [GLW Theorem I.5](https://arxiv.org/html/1801.09106#S1.SS4): each larger minor is an integer polynomial in the slice entries which vanishes identically over \(\mathbb C\), so all its integer coefficients are zero. Therefore it also vanishes over \(F\). For \(|F|>2\), use \(K=\begin{pmatrix}1&1\\r&1\end{pmatrix}\), with \(r\notin\{0,1\}\), realizable by two rank-one slices over \(F\) itself. This proves the first line in the theorem.

## Two elements: exhaustive structural reduction

Linearly dependent slices yield rank at most one. For independent slices over \(\mathbb F_2\), their span is one of the 35 two-dimensional subspaces of \(\mathrm{Mat}_2(\mathbb F_2)\). All ordered bases of a plane give the same rank, by physical basis invariance. Simultaneous conjugation also preserves rank. Encode a matrix by its four row-major entry bits, starting with the least significant bit. A plane is canonically represented by the two smallest codes among its three nonzero matrices. Enumerate all \(1\le a<b\le15\), retaining the pair precisely when it is canonical for \(\{a,b,a\mathbin{\mathrm{XOR}}b\}\); take the least canonical pair obtained under the six invertible conjugations. This short exhaustive computation yields:

| Representative | Orbit size | Rank |
| --- | ---: | ---: |
| (1,2) | 3 | \(1\) |
| (1,4) | 3 | \(1\) |
| (1,6) | 6 | \(2^{s-1}\) |
| (1,8) | 3 | \(2\) |
| (1,10) | 6 | \(2\) |
| (1,14) | 6 | \(c_s\) |
| (2,4) | 3 | \(2\) |
| (2,9) | 3 | \(0\) |
| (6,11) | 1 | \(2\) |
| (7,9) | 1 | \(2\) |

For (1,2) and (1,4) use triangularity: only the all-projector word has nonzero trace. For (1,8) use the two diagonal matrix units. For (1,10) both slices are rank one, both diagonals of the overlap are nonzero, and the off-diagonal product is zero. For (1,14) replace the second slice by its sum with the first; the overlap of the projector and all-ones matrix has precisely one zero diagonal and two nonzero off-diagonals. For (2,4) use the strictly alternating off-diagonal matrix units. For (2,9) the identity has zero trace, and all other words are either nilpotent or zero. For (6,11) the pencil determinant is \(1+t+t^2\). Its two singular directions over \(\mathbb F_4\) are independent nonzero rank-one matrices with zero traces; their span contains an invertible matrix, so their off-diagonal overlap product cannot vanish. Rank does not change under field extension, and the overlap table gives two. For (7,9) the non-identity slice has two distinct eigenvalues over \(\mathbb F_4\); the extended plane spans the two diagonal matrix units in an eigenbasis.

For (1,6) use the projector \(E_{00}\) and swap \(X\). With at least one projector the trace is one exactly when every gap between projectors contains an even number of swaps. The all-swap word has trace zero. Thus the two parity classes of projector positions strictly interlace and each contains the same number \(k\ge1\) of projectors. Fix a \(k\)-subset of odd positions. The alternating flattening row in the even \(k\)-subset block is the exterior product of the \(k\) indicator vectors of the disjoint intervals of even positions between successive odd projectors. Over \(\mathbb F_2\) the coordinate on an even \(k\)-subset is one precisely when it hits each interval exactly once. The indicators sum to the all-ones vector \(w_1\), so every such wedge is in \(w_1\wedge\bigwedge^{k-1}\mathbb F_2^s\) and the rank is at most \(\binom{s-1}{k-1}\). For independent rows, use odd sets \(1=i_1<i_2<\cdots<i_k\). With \(w_j=e_j+\cdots+e_s\), the interval indicators are \(w_{i_j}+w_{i_{j+1}}\) and the last is \(w_{i_k}\). Their wedge is exactly \(w_1\wedge w_{i_2}\wedge\cdots\wedge w_{i_k}\); these form a basis of that exterior-product space. Summing the block ranks gives \(2^{s-1}\).

It follows that the maximum is \(\max(c_s,2^{s-1})\). To evaluate \(c_s\), use the last-two-symbol adjacency graph with transitions \(00\to00,01\), \(01\to10,11\), \(10\to00\), \(11\to10,11\). Its length-\(s\) closed-walk trace counts the labeled avoiding words and its characteristic polynomial is \(x(x^3-2x^2+x-1)\). Thus \(c_1=c_2=2,\ c_3=5\) and \(c_s=2c_{s-1}-c_{s-2}+c_{s-3}\) for \(s\ge4\). Duplicating the first letter injects avoiding cyclic words into the next length without creating \(101\), so \(c_{s-1}\le c_s\) and the recurrence gives \(c_s\le2c_{s-1}\). Hence \(c_4=10,c_5=17,c_6=29<32\) settle the crossover for all lengths.

## Replay

Run the bundled `verify-characteristic-two.js` using Node.js. It checks the full orbit census, all 35 planes for \(s=2,\ldots,8\), and all 256 overlaps over \(\mathbb F_4\) for \(s=2,\ldots,6\). The plane reduction, exterior powers, and triangular minors establish the all-length claims; the finite rank sweeps are cross-checks.
