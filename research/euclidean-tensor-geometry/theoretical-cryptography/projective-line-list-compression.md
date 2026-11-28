# List-dependent linear compression by counting uncovered projective lines

**Scope.** A finite-dimensional mathematical method for supplied subspaces and two fully specified forward progression laws. It does not infer unknown parameters, compute original point masses from compressed tables, or address any implemented cryptosystem.

Let \(U_1,\ldots,U_m\le\mathbb F_p^d\) be given by bases, with the prime \(p\) in binary. Let \(\mathcal P(U)\) be the set of one-dimensional subspaces of \(U\), of size \((p^{\dim U}-1)/(p-1)\). Write
\[
  H_{\rm mult}=\sum_i|\mathcal P(U_i)|,\qquad
  H_{\rm un}=\left|\bigcup_i\mathcal P(U_i)\right|.
\]

**Theorem.** A deterministic algorithm polynomial in the input bit length constructs a linear map into \(\mathbb F_p^k\) that is injective on every supplied \(U_i\), where \(k=0\) if \(H_{\rm mult}=0\), and otherwise
\[
             k\le\min\{d,\,1+\lfloor\log_p H_{\rm mult}\rfloor\}.
\]
If the supplied spaces have dimension bounded by a fixed constant, the same conclusion holds replacing \(H_{\rm mult}\) by the smaller **distinct-line** count \(H_{\rm un}\), with no enumeration of the distinct lines even there. The map is tailored to the explicit list. This is not a universal seeded condenser guarantee.

**Application.** For two fully specified progression-convolution laws on \(\mathbb F_p^d\) as in the [finite-vector identity note](https://github.com/mxym/math/blob/713cbb44cd43d1fe8c302d8e8791d5968de6113a/research/euclidean-tensor-geometry/theoretical-cryptography/vector-progression-law-identity.md), one can deterministically compress them so that their original laws are equal exactly when their images are equal. In the common-uniform-space case the compressed dimension is at most
\[
  \min\!\left\{d,\ 1+
       \left\lfloor\log_p\big((p+1)\tbinom{L}{2}+L+1\big)\right\rfloor\right\}
\]
for \(L\) distinct nonzero stride lines after projecting out the common uniform space, with the trivial zero-list case as usual. One may also use the sharper actual projective union count for that list. For fixed \(p\) the whole **compressed** laws can be computed exactly in polynomial bit time. The original identity decision was already polynomial-time; this is a dimensional and representation improvement, not a new complexity class for the decision.

## 1. One row at a time, without scanning the field

The goal is that the kernel of the collected rows contain no listed projective line. After some rows have been chosen, replace every space by its intersection with their joint kernel. For the moment count the remaining lines with multiplicity; the same proof applies to the weighted count in §2. If the remaining line count is \(H\), a uniformly random new row has expected remaining count \(H/p\), since each line is annihilated with probability \(1/p\).

Construct the new row one coefficient at a time using exact conditional expectation. Let \(Z_j=\operatorname{span}(e_1,\ldots,e_j)\), and suppose \(\beta\) is the already fixed row on \(Z_j\). For a remaining space \(U\), write \(V=U\cap Z_j\). Its conditional expected line count is
\[
 |\mathcal P(V\cap\ker\beta)|
              +\frac{|\mathcal P(U)|-|\mathcal P(V)|}{p}.       \tag{1}
\]
A line outside \(Z_j\) has some still free, nonzero coordinate and hence the row value stays uniform. A line inside \(Z_j\) is already decided.

At the next coordinate, put \(V'=U\cap Z_{j+1}\), and restrict \(\beta\) (extended by zero in the new coordinate) and the new coordinate functional \(\eta\) to \(V'\). The only part of (1) depending on the new coefficient \(t\) is the number of lines in the kernel of \(\beta+t\eta\) on \(V'\). If \(\eta=0\), it is constant. If \(\eta\ne0\) and \(\beta,\eta\) are not proportional on \(V'\), it is also constant. Otherwise there is exactly one exceptional \(t\) for which \(\beta+t\eta=0\) on \(V'\). This adds
\[
                     p^{\dim V'-1}
\]
over the ordinary kernel-line count. Both the exceptional key and its weight are computable by field arithmetic on a basis. Thus the nonconstant part over all \(t\) is a sparse dictionary of exceptional keys, at most one per space. To find a minimum, compare the listed weights and also take the default zero value if a field element is missing. A missing key can be found by sorting the represented integers from 0 to \(p-1\), and if all keys are present then there are only as many to inspect as the input dictionary already contains. No loop over a binary-large field is paid.

The chosen value is at most the conditional average. Once the row is completed the remaining integer count is at most \(H/p\). A row chosen while \(H>0\) is independent of the preceding rows: any combination of those rows annihilates all residual spaces and could not decrease a positive count. The count therefore vanishes within \(d\) rows and as soon as \(p^k\) exceeds the initial count. The relevant powers of \(p\) have \(O(d\log p)\) bits, and the row/kernel intersections are ordinary linear algebra. This proves the multiplicity form.

## 2. Remove overlap exactly when the listed dimensions are small

Discard zero spaces and let \(\mathcal L\) be the set of all distinct nonzero intersections of nonempty subsets of the list. If the supplied dimensions are at most a fixed \(s\), \(\mathcal L\) is generated by intersections of at most \(s\) original spaces: start with one of them and retain another only when the current intersection dimension strictly decreases, ending at a positive dimension. Thus \(\mathcal L\) can be built and deduplicated in polynomial time in the original list (with exponent depending on \(s\)). For example at dimensions one and two only pairwise plane intersections need be added after duplicate spaces are removed.

For each \(V\in\mathcal L\) in decreasing inclusion order compute
\[
                   c_V=1-\sum_{W\in\mathcal L,\,W\supsetneq V}c_W.       \tag{2}
\]
These integers need not be positive. For any line contained in some supplied space, the intersection of all members of \(\mathcal L\) containing that line is itself in \(\mathcal L\) and nonzero. Its supersets there are exactly the spaces containing the line; (2) says that the sum of their weights is one. A line outside the union is in none. Consequently, for every subspace \(K\),
\[
        \left|\bigcup_i\mathcal P(U_i\cap K)\right|
                     =\sum_{V\in\mathcal L} c_V|\mathcal P(V\cap K)|.   \tag{3}
\]
In particular use the **original** weights after every row; simply restrict each member \(V\) to the new joint kernel. Signed weights do not cause a problem: conditional expectation is linear, so they just give a sum of signed exceptional weights on the same sparse set of keys as in §1. Include a missing default key when it exists and take the least exact integer of all candidates. Equation (3) ensures the resulting objective is the true nonnegative integer line count. Even the crude bound \(|c_V|\le2^{|\mathcal L|}\) leaves polynomial bit length. This proves the distinct-line improvement.

For orientation, if the list consists of all lines and pair planes from the projective lines of a \(t\)-dimensional subspace, the unique count is just \((p^t-1)/(p-1)\), while counting all pair planes with repetition can be much larger. Counting each geometric obstruction once can change the certified output dimension, not only a prefactor in the running time.

## 3. Which data the projection must preserve for forward-law identity

Write each law as \(A+\sum_i U_i v_i\), with independent uniform integer indices \(0,\ldots,L_i-1\). Call \(W\) the span of the strides with \(p\mid L_i\). The finite-vector identity theorem proves that the Fourier support is exactly the annihilator of \(W\). If the two \(W\)'s differ, pick a linear form that vanishes on one and not the other, using a basis of one annihilator and a stride in the other. This one-dimensional image separates the laws: one has a nonzero primitive Fourier value where the other vanishes.

When the two \(W\)'s agree, project to their common quotient \(V\). The original laws are uniform along the cosets of \(W\), so equality in \(V\) is equivalent to original equality. Remove zero strides, keep the known starts, and list the distinct nonzero stride lines \(D_1,\ldots,D_L\) across both distributions. Use the compression theorem on
1. every stride line;
2. the span of every pair of distinct stride lines;
3. the line generated by the difference of the two natural centers for odd \(p\), or their starts for \(p=2\), if that difference is nonzero.

Nonzero stride lines survive and remain pairwise distinct by injectivity on the pair planes. Within each line the map preserves the exact field coefficients, so folded keys \(w,-w\) collide only as they already did. Hence each line's integer length product and every sparse folded exponent key in the pinned identity signature are carried faithfully. The center difference or start difference is zero after the map exactly when it was zero beforehand. There are no newly uniform directions in the projected quotient because every remaining length is prime to \(p\). By all parts of the identity criterion the projected pair is equal exactly when the original pair is. We use the complete **joint** signature, not just some one-dimensional marginals.

Counting the lines in each input plane with multiplicity gives
\(H_{\rm mult}\le(p+1)\binom L2+L+1\).
In particular \(p^k\le pH_{\rm mult}=O(p^2(1+L^2))\) when \(H_{\rm mult}>0\). At fixed \(p\) one can tabulate all compressed integer counts by repeated finite convolutions in this state space. On a nonzero stride each of its \(p\) residue indices has count \(\lfloor L_i/p\rfloor\) or one more; a zero stride is deterministic. A common normalization denominator is \(\prod_i L_i\), of polynomial bit length. For sufficiently large \(p\) (e.g. \(p\ge\binom L2+L+2\)) the output dimension is at most 2, but this is a **dimension** bound; for binary-large \(p\) a printed table can still be too long, and the compressed signature remains the appropriate test.

The factor of two in the logarithmic direction bound is unavoidable for a map that preserves all listed pair planes in general. Supply all projective lines in either of two disjoint \(t\)-dimensional summands. A nonzero vector in their sum either lies in a listed line, or is a sum of nonzero vectors in two different listed lines and therefore lies in their pair plane. The map must be injective on the full \(2t\)-space. This uses \(L=2(p^t-1)/(p-1)\), and even the distinct-line union equals the projective space of dimension \(2t-1\) in this instance.

## Scope and precedents

[Alon–Dietzfelbinger–Miltersen–Petrank–Tardos, *Linear Hashing*](https://tidsskrift.dk/brics/article/view/18808) studies randomly chosen linear maps. [Forbes–Guruswami, *Dimension Expanders via Rank Condensers*](https://arxiv.org/abs/1411.7455), Definition 2.4, specifies **seeded families** and bounds the bad seeds for each subspace. [Cohen–Doron–Goldgraber, *Algebraic-Geometric Parvaresh–Vardy Subspace Designs and Rank Condensers*](https://arxiv.org/abs/2609.32834) is likewise a design/condenser family. With a sufficiently large such family, one common good seed for a given list also follows by a union bound; this is not claimed to be a new general hashing principle. The concrete construction here instead chooses a single map from the explicit input list, with exact sparse conditional expectations and an optionally exact union bound for overlapping small-dimensional spaces. The new application retains the complete known-law signature in a much smaller ambient dimension.

The accompanying `verify_projective_line_list_compression.py` independently enumerates small fields' projective lines and prefix objectives, compares exact forward-law tables, and includes a large binary-encoded prime without field enumeration. These are checks of the stated mathematics, not assumptions in the proof.

No counting oracle for the original point mass is furnished: the compressed mass of a given image is the sum over a whole fiber. In particular the earlier separation between exact joint identity and the hardness of an original point query remains intact. No unknown record, attack, or implementation enters this theorem.
