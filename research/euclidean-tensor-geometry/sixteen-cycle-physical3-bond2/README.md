# Exact alternating rank on the 16-cycle with physical dimension 3 and bond dimension 2

**Yongxian Zhang.** AI-assisted proof development and independent internal exact-arithmetic checks; no external peer review claimed.

In the translation-invariant periodic model of [Gesmundo–Landsberg–Walter](https://arxiv.org/html/1801.09106), the maximum alternating flattening rank on the 16-cycle at physical dimension 3 and bond dimension 2 is **6518** over \(\mathbb C\). The ambient and min-cut dimensions are \(3^8=6561\). The deficit is 43, not 27 as predicted by saturation of the [reflection-imbalance bound](../PeriodicAlternatingTwistedReflection.md). This is not the equal-bond-3 problem or an exact formula for arbitrary lengths.

## 1. Generic normal form and the obstructed block

On a dense open set, the slices span a hyperplane in \(\mathrm{Mat}_2\) whose annihilator under the trace pairing has two distinct nonzero eigenvalues. Conjugate to diagonal form. After an invertible physical basis change the slices can be taken as
\[
A_{+}=E_{01},\quad A_{-}=E_{10},\quad A_0=\operatorname{diag}(1,t).
\]
The bound proved on this one-parameter family therefore holds for all slices by the polynomial-minor rank criterion.

Let \(M\) be the alternating flattening, with \(8\)-letter row and column words. A nonzero coefficient requires combined charge zero, where the charge is the sum of letters in \(\{-1,0,1\}\). In the charge-zero row and column spaces simultaneously, the cyclic shift of a word is \(R\). The flattening commutes with \(R\) and obeys \(M^\mathsf T=MR\), so the restriction to \(R=-1\) is skew for the standard bilinear form. In this sector the involution \(X\) reversing positions \(i\mapsto-i\bmod 8\) and negating every letter anticommutes with \(M\). These are precisely the twisted-reflection identities in the linked proof; entrywise transposition exchanges \(A_+\) and \(A_-\) and fixes \(A_0\). The two eigenspaces of \(X\) are mutually orthogonal, and the standard bilinear form is nondegenerate on each. Thus the rank in this sector is twice the rank of one cross block.

The sector has dimension 141; the two \(X\)-dimensions are 57 and 84. One exact way to form the cross block \(D(t)\) is to choose a representative \(w\) for every even-length orbit of \(R\) in charge zero. The vector \(v_w=\sum_i(-1)^i e_{R^iw}\), summing once around the orbit, spans that orbit's \(-1\) eigenspace. Reflection induces signed permutation \(v_w\mapsto\epsilon v_{w'}\). For a pair, use \(v_w\pm\epsilon v_{w'}\); for a fixed orbit use its sign. In this basis each output coordinate in the smaller eigenspace is its coefficient at the first orbit representative.

## 2. Exact upper certificate and independent check

Enumerating the transitions (equivalently, all \(2^{16}\) binary virtual cycles) builds every integer coefficient of \(D(t)\). The preferred [sparse certificate](./upper_sparse.cpp) gives eight polynomial row vectors of degree at most 8 with coefficients \(\pm1\). It multiplies each by \(D(t)\), checks that every integer coefficient vanishes, and checks independence at \(t=7\) modulo 101. This already gives \(\operatorname{rank}_{\mathbb Q(t)}D(t)\le49\). For a second upper check, its entries have degree at most 12 and coefficient \(\ell_1\)-norm at most 4. The [modular checker](./upper_certificate.cpp), on the [35 listed primes](./primes.txt), gives rank at most 49 for all \(t=0,1,\ldots,600\) in each field, with maximum 49 in each. Every \(50\times50\) minor has degree at most 600, so reduction modulo each prime is identically zero as a polynomial. By the Leibniz formula each integer coefficient is bounded by \(50!4^{50}\), which is less than the product of the 35 distinct primes. Thus every such polynomial minor vanishes over \(\mathbb Z\). The \(141\)-dimensional sector loses at least \(141-2\cdot49=43\) ranks. Because it is an invariant direct summand, the same loss holds for the whole matrix.

An independent [symbolic checker](./verify_symbolic.py) builds the block by enumerating virtual bit cycles instead of tracing each row/column word pair, then uses exact fraction-free elimination over \(\mathbb Z[t]\). Its rank is 49, and it independently gives dimensions, degree and norm as above.

## 3. Matching lower certificate

At \(t=7\) in \(\mathbb F_{101}\), the whole flattening has rank 6518. The neutral block has dimensions \(1107\times1107\) and rank 1064; all opposite nonzero-charge blocks are full. [The C++ checker](./lower_certificate.cpp) traces words, and an independent [binary-cycle checker](./verify_lower.py) builds the same charge blocks and does exact modular elimination. A nonzero integer minor modulo 101 proves the lower bound over \(\mathbb C\). The trace-based and independent outputs agree, as recorded in [verification.txt](./verification.txt).

Run the independent checks using Python with SymPy and NumPy. For the C++17 checkers (g++):
```sh
g++ -O3 -std=c++17 upper_sparse.cpp -o upper_sparse
./upper_sparse
g++ -O3 -std=c++17 upper_certificate.cpp -o upper
./upper < primes.txt
g++ -O3 -std=c++17 lower_certificate.cpp -o lower
./lower 8 7 101
```

The additional deficit over the reflection estimate is established for this length only. It motivates studying ranks inside the separate conserved-charge/rotation blocks instead of assuming that the aggregate reflection imbalance is the only obstruction.
