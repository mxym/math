# An integral optimal witness for binary periodic alternating rank

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review claimed.

Let \(s\ge2\). For a cyclic tensor with \(2s\) sites, use the same two \(2\times2\) slices at each site and flatten the odd labels against the even labels. The maximum alternating rank over a field \(F\) is \(3\cdot2^{s-2}\) **for every field other than \(\mathbb F_2\)**. Over \(\mathbb F_2\) the exact values are \(2,5,10,17\) for \(s=2,3,4,5\), and \(2^{s-1}\) for each \(s\ge6\). The latter and the other characteristic-two cases were established in the [previous characteristic-two archive](https://github.com/mxym/math/releases/tag/periodic-binary-characteristic-two-v1.0.0).

The new integral witness is the single pair
\[
 P=\begin{pmatrix}1&0\\0&0\end{pmatrix},\qquad
 X=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
\]
Its alternating matrix for every \(s\ge2\) has Smith normal form over \(\mathbb Z\)
\[
 \mathrm{diag}\!\bigl(1^{[2^{s-1}]},\,2^{[2^{s-2}]},\,0^{[2^{s-2}]}\bigr),
\]
where superscript brackets specify multiplicities. In particular the same integral pair is optimal **simultaneously over all fields of characteristic other than two**, including \(\mathbb F_3\), by one proof. The characteristic-zero upper bound is [Gesmundo–Landsberg–Walter, Theorem I.5](https://arxiv.org/html/1801.09106#S1.SS4). Any larger minor is an integer polynomial in the two slices, identically zero over \(\mathbb C\); it is therefore identically zero over every field. The issue is attainment when the field is small.

## Interlacing blocks and exterior powers

Index an odd word by the subset of positions using \(P\), and an even word in the same way. If both use no projector, the entry is \(\operatorname{tr}(X^{2s})=2\). For any word with at least one \(P\), the trace is one exactly when every cyclic gap between consecutive projectors contains an even number of swaps, since \(PX^\ell P=P\) for even \(\ell\) and zero otherwise. This is equivalent to cyclic interlacing of the odd and even projector positions, so their counts must agree. Thus the flattening splits into the no-projector entry and blocks \(B_k\), \(1\le k\le s\), indexed by \(k\)-subsets of the two parity classes.

In the standard integral basis \(e_1,\ldots,e_s\) of the even positions, put \(w_i=e_i+\cdots+e_s\). A row indexed by \(U=\{i_1<\cdots<i_k\}\) has value one exactly on the even subsets that choose one element from each interval \([i_1,i_2),\ldots,[i_{k-1},i_k),[i_k,s]\cup[1,i_1)\). This row is the list of coordinates of the wedge of the \(k-1\) indicator vectors \(w_{i_j}-w_{i_{j+1}}\) and the final **signed** interval vector
\[
 w_{i_k}+(-1)^{k-1}(w_1-w_{i_1}).
\]
Indeed, if a column chooses the short wrap portion \([1,i_1)\), the selected coordinate from the last row moves to the start in the sorted column list and contributes the permutation sign \((-1)^{k-1}\). The signed coefficient cancels it. If the column chooses the non-wrap portion instead, both signs are positive.

For odd \(k\), the sum of the interval vectors is \(w_1\), so every row lies in the saturated summand
\[
 w_1\wedge\bigwedge\nolimits^{k-1}\mathbb Z^s.
\]
Rows with \(i_1=1\) are precisely its basis \(w_1\wedge w_{i_2}\wedge\cdots\wedge w_{i_k}\), by telescoping the interval vectors. Hence the row lattice equals that summand; all nonzero Smith entries are 1, with multiplicity \(\binom{s-1}{k-1}\).

For even \(k>0\), the sum of the interval vectors is \(2w_{i_1}-w_1\). Over \(\mathbb Q\), put \(T(w_i)=w_i-\tfrac12 w_1\) for every \(i\). The interval differences are \(T(w_{i_j})-T(w_{i_{j+1}})\), and replacing the last interval by the sum gives \(2T(w_{i_1})\). An elementary triangular wedge expansion now identifies the row with \(2T(w_{i_1})\wedge\cdots\wedge T(w_{i_k})\). Thus in the integral \(w\)-wedge basis the row map is \(2\bigwedge^k T\). Use the unimodular basis \(w_1,w_2-w_1,\ldots,w_s-w_1\) of \(\mathbb Z^s\). In this basis \(T\) is diagonal with \(1/2\) on the first coordinate and 1 elsewhere, hence \(B_k\) is integrally equivalent to \(\binom{s-1}{k-1}\) ones and \(\binom{s-1}{k}\) twos.

Summing over the blocks gives \(2^{s-1}\) ones and \(1+\sum_{k\ge2,\ k\,\mathrm{even}}\binom{s-1}{k}=2^{s-2}\) twos. The remaining \(2^{s-2}\) entries are zero. This establishes the Smith form and the optimal rank in every odd characteristic and characteristic zero. Its characteristic-two specialization recovers the swap/projector contribution \(2^{s-1}\) of the earlier proof, but not the larger optima for the three smaller half-lengths \(s=3,4,5\) over \(\mathbb F_2\). Those require the other pencil analyzed in that earlier classification.

## Replay

Run `node verify-integral-witness.js` for an independent arithmetic cross-check. It verifies 33,116 even-block matrix-entry identities and the exact integer determinants for all positive even \(k\le s\) and \(2\le s\le9\). The signed wedge proof gives the result for all \(s\).
