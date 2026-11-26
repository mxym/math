# Exact alternating rank for the 12-cycle in dimension seven

**Yongxian Zhang.** AI-assisted proof development and independent internal replay; no external peer review claimed.

In the one-site translation-invariant periodic trace model, with both physical and virtual bond dimension \(q=7\), the maximum complex rank of the alternating flattening on \(C_{12}\) is
\[
F_{12}(7)=7^6-1=117648.
\]
This is an exact single-dimension result, not a general solution of \(F_{12}(q)\). See [Gesmundo–Landsberg–Walter, §II](https://arxiv.org/html/1801.09106#S2) for the model and rotation bound, and [the all-dimension linear defect result](../twelve-cycle-linear-defect/README.md) for a different, nonexact general bound.

## Upper bound

For six-letter words \(a,b\), set \(M_{a,b}=\operatorname{tr}(A_{b_5}A_{a_5}\cdots A_{b_0}A_{a_0})\), so the chronological order starts with \(a_0,b_0\). Let \(R\) act by moving the first letter to the last position. Cyclicity of trace gives \(M^\mathsf T=MR\): transposition interchanges the two word labels, and changing the trace starting point puts the second word into the order \(b_1,\ldots,b_5,b_0\). Taking the transpose again shows \(MR=RM\). The \(-1\)-eigenspace of \(R\) is orthogonal to the other eigenvalues for the standard bilinear form, and there \(M\) is skew. This eigenspace is odd-dimensional: \(R\) is a product of five adjacent swaps; each has determinant \((-1)^{7^4\binom72}=-1\). The remaining nonreal eigenvalues occur in reciprocal pairs and \(1\) contributes no sign. Thus at least one dimension is lost for every choice of slices.

## Explicit tensor and certificate

Index the physical and virtual bases by \(\mathbb F_7\) as a set. Take the integer monomial slices \(A_a e_x=w(a,x)e_{x+a}\) with addition modulo seven, and the following weights, in rows indexed by \(a\) and columns by \(x\):
~~~text
40 40 40 12 40 12 12
39  2 38 38 30 15 27
39 30  2 15 38 27 38
25 42 28 19 36 13 35
39 38 30 27  2 38 15
25 28 36 35 42 19 13
25 36 42 13 28 35 19
~~~
The equality \(w(2a,2x)=w(a,x)\) leaves 17 independent orbits. For exact replay, reduce the integer slices modulo 43. For any pair of words, the entry is a sum over seven starting virtual states: apply the alternating labels one at a time, multiply the corresponding weights, and count the resulting coefficient only if the final state is the initial one. Thus the matrix maps additive word charge \(h=\sum_i a_i\bmod7\) to \(-h\). It commutes with \(R\) and with multiplication-by-two \(S\) of all the letters, the latter from virtual conjugation. Rotation has order six; \(S\) has order three and preserves charge zero. Nonzero charges \(1,2,4\) are identified by \(S\), and \(6,5,3\) are their negatives.

Work in \(\mathbb F_{43}\) with primitive sixth root \(z=7\). On charge zero, simultaneous eigenvalues of \(R,S\) are \(z^j,z^{2k}\). On nonzero charges use the rotation only. For a word orbit and a chosen representative \(u\), form the vector with coefficient \(z^{-jr-2km}\) on \(R^r S^m u\). If two assignments disagree at one word the target eigenspace contributes nothing on that orbit. Otherwise this is a basis vector with representative coefficient 1. To obtain the matrix on these bases, sum over each column orbit with its coefficients and read one representative entry per row orbit. This gives the actual restricted matrix, since \(M\) commutes with the operators and maps one charge to its opposite.

The standard transpose pairs the rotation eigenvalues \(z^j,z^{-j}\) and the multiplier eigenvalues \(z^{2k},z^{-2k}\) in charge zero. Therefore \(M^\mathsf{T}=MR\) identifies the ranks for \((h,j,k)\) and \((-h,-j,-k)\) (negating \(j,k\) modulo 6 and 3). Along with the multiplier action on nonzero charges, the following blocks suffice:
 
| Charge of output | Multiplier index | Rotation index | Dimensions and exact ranks modulo 43 |
|---|---:|---|---|
| \(1\) | not used | \(0,1,2,3,4,5\) | \(2812,2792,2808,2795,2808,2792\), all full |
| \(0\) | \(0\) | \(0,1,2,3\) | \(950,926,930,941\); last rank \(940\), other blocks full |
| \(0\) | \(1\) | \(0,1,2,3,4,5\) | \(931,933,939,927,939,933\), all full |

Orbit-basis dimensions can also be checked directly from fixed-word counts. If a power of the rotation has cycles of length \(\ell\) and the multiplier is trivial, its fixed word count in every charge is \(7^{6/\ell-1}\) (the cycle length is invertible modulo seven). If the multiplier is nontrivial on charge zero, there are \(7^{6/\ell}\) fixed words for \(3\mid\ell\), because each geometric orbit then sums to zero; otherwise only the all-zero word is fixed. Character projection gives the sizes in the table. The full matrix has rank exactly \(117648\) modulo 43; a nonzero minor of the integer matrix modulo 43 stays nonzero over \(\mathbb C\). Together with the upper bound this proves the claim.

## Reproduce

Run the standalone C++17 checker:

~~~sh
g++ -O3 -std=c++17 -fopenmp c12q7.cpp -o c12q7
./c12q7
~~~

OpenMP is optional. The checker precomputes deterministic transfers of four alternating letters, forms each compressed block using those transfers, and applies modular Gaussian elimination with an independently generated inverse table. The separate Node prototype uses transfers of six alternating letters; the two implementations agree. The published weights are fixed integers, not sampled inside the C++ rank calculation.
