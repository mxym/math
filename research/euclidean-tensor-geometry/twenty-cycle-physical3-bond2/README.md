# Exact alternating rank on the 20-cycle with physical dimension 3 and bond dimension 2

**Yongxian Zhang.** AI-assisted proof development and independent internal exact checks; no external peer review claimed.

In the [translation-invariant periodic trace model](https://arxiv.org/html/1801.09106), the maximum alternating flattening rank on the 20-cycle with physical dimension 3 and bond dimension 2 is **58796** over \(\mathbb C\). Its deficiency from the min-cut \(3^{10}=59049\) is 253. This extends the [exact 16-cycle calculation](../sixteen-cycle-physical3-bond2/README.md) at the same dimensions, not a general formula in the length.

## From a high-degree trace matrix to a linear pencil

Use the generic normal form \(A_+=E_{01}, A_-=E_{10}, A_0=\operatorname{diag}(1,t)\), justified by the hyperplane argument in the 16-cycle proof. Let the half-length \(s\) be even. A contributing trace cycle is a periodic binary walk \(b_0,b_1,\ldots,b_{2s}=b_0\) whose labels are \(\Delta_h=b_{h+1}-b_h\in\{-1,0,1\}\). The power of \(t\) is the number of steps with \(\Delta_h=0\) and \(b_h=1\). The walk has equally many rises and falls, and only falls have \(b_h=1\) among the nonzero steps. Thus that exponent is
\[
e=2s b_0-\sum_{h=0}^{2s-1}h\Delta_h-\#\{h:\Delta_h=1\}.
\]
The sum of the \(b_h\) used here follows by telescoping \(b_{h+1}=b_h+\Delta_h\).

Restrict the alternating flattening to charge-zero words on both sides, word rotation \(R=-1\), and one cross block between the two twisted-reflection eigenspaces, exactly as for the 16-cycle. For a neutral word \(w\), put
\[
\rho(w)=\left(-2\sum_i i\,\Delta_i(w)-\#\{i:\Delta_i(w)=1\}\right)\bmod 2s
\]
in the interval \([0,2s-1]\). Neutrality makes \(\rho\) invariant under rotating the word and under reversing \(i\mapsto-i\) while reversing all signs. In an alternating interleaving of two neutral words \(u,v\) the odd-step index contributes an extra \(\sum_i\Delta_i(v)=0\). Thus every contributing virtual walk has exponent \(e\equiv \rho(u)+\rho(v)\pmod{2s}\). The all-zero word has rotation \(+1\) and does not appear, so \(0\le e<2s\). The formula holds for every orbit representative and its reflection partner. Consequently each entry in the signed cross block is either zero or an integer multiple of the single monomial with that residue exponent. Rescale rows and columns by \(t^{-\rho(w)}\) in their respective bases. This turns the cross block into an integer matrix pencil \(D_0+xD_1\), where \(x=t^{-2s}\); no determinant degree in \(t\) is needed.

## Exact upper and lower at \(s=10\)

For \(s=10\), the specified sector has dimension 891, with twisted-reflection eigenspace dimensions 405 and 486. Its total rank is twice the cross-block rank, by skewness and nondegeneracy of the bilinear form on each eigenspace. The [86 sparse polynomial relations](./relations.txt) on the 405 rows have degree at most 1 in \(x\). Each annihilates the cross block identically by integer coefficient multiplication; they are independent at \(x=7^{-20}\) modulo 101. It follows that cross-block rank is at most \(405-86=319\) in characteristic zero. This forces deficiency at least \(891-2\cdot319=253\). The bound extends from the generic normal form to all tuples by vanishing minors.

At \(t=7\) in \(\mathbb F_{251}\), use the charge decomposition (row charge \(q\) pairs only with column charge \(-q\)) and all ten word-rotation eigenvalues in that field. For each orbit of length \(\ell\), the character vectors for the \(\ell\)-th roots form a basis, since 251 does not divide \(\ell\). The [block elimination log](./lower_log.txt) lists \(q=0,\ldots,10\) and momentum \(k=0,\ldots,9\). All are full except \(q=0,k=5\), which has dimension 891 and rank 638. Negative charges have identical ranks to the corresponding positive ones by the transpose-shift identity, so the total rank is 58796. This exact modular specialization proves the matching complex lower bound.

The [C++ upper checker](./upper_sparse.cpp) reconstructs the pencil and verifies all relations without symbolic-system dependencies. The [C++ lower checker](./lower_certificate.cpp) traces all required word pairs. The [independent Python checker](./verify_binary_cycles.py) instead enumerates closed binary walks, then verifies the relations and reproduces the full block ranks by modular elimination:
```sh
g++ -O3 -std=c++17 upper_sparse.cpp -o upper
./upper
g++ -O3 -std=c++17 lower_certificate.cpp -o lower
./lower 10 7 251
python verify_binary_cycles.py relations.txt     # requires NumPy
```

No claim is made that this family of pencil nullities is classified for larger half-lengths.
