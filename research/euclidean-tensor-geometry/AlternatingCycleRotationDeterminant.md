# Rotation-determinant obstruction and sharp large-bond rank on alternating cycles

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review claimed.

Let \(s\ge2\), and form a complex periodic matrix product state on \(2s\) sites using the same \(p\) matrices \(A_0,\ldots,A_{p-1}\in\mathrm{Mat}_D(\mathbb C)\) at each site. Put the odd sites on one side and even sites on the other. Write \(F_s(p,D)\) for the largest flattening rank over these choices. The physical dimension \(p\) and bond dimension \(D\) are independent.

**Theorem.** Define \(\epsilon(p,s)=1\) in either of the following two disjoint cases, and 0 otherwise:
- \(s\) is even and \(p\equiv3\pmod4\);
- \(s=2\) and \(p\equiv2\pmod4\).

Then \(F_s(p,D)\le p^s-\epsilon(p,s)\) for every \(D\), with equality if
\[
D\ge 1+p^s+2\sum_{j=1}^{s-1}p^j.
\]
Equality holds already at \(D\ge p+1\) when \(s\) is odd. An additional sufficient bound is \(D\ge p+1+s p^s\), using the sparse correction construction below.

The upper bound answers [Gesmundo–Landsberg–Walter (GLW), Remark II.2](https://arxiv.org/html/1801.09106#S2) in the physical congruence class of their Theorem I.3: it proves the deficit for **every even half-length** at \(p\equiv3\pmod4\), not only for half-length \(2\bmod4\). The parity theorem does not by itself determine the general rank at \(D=p\). The [separate eight-cycle theorem](https://github.com/mxym/math/releases/tag/periodic-eight-cycle-odd-quantum-max-flow-v1.0.0) supplies the exact rank in that model for \(s=4\) and \(p\equiv3\pmod4\).

## Determinant of the word rotation

For words \(a,b\) of length \(s\), put
\[
M(a,b)=\operatorname{tr}(A_{a_0}A_{b_0}\cdots A_{a_{s-1}}A_{b_{s-1}}).
\]
Let \(\rho\) be the left rotation on words and \(Re_b=e_{\rho b}\). By cycling the first factor in \(M(b,a)\) to the end, we obtain \(M^{\mathsf T}=MR\). Two-site cyclic invariance also gives \(MR=RM\). Conversely \(M^{\mathsf T}=MR\) implies \(M(b,a)=M(a,\rho b)\) and hence the tensor of interleaved coefficients is one-site cyclic-invariant.

On the \(p^s\) word basis, a swap of two adjacent positions acts by \(p^{s-2}\binom p2\) transpositions: fix the other letters and choose two distinct letters to swap. Since the rotation is a product of \(s-1\) adjacent swaps,
\[
\det R=(-1)^{(s-1)p^{s-2}\binom p2}.
\]
For \(s=2\) the factor \(p^{s-2}\) is 1. If \(s>2\) and \(p\) is even it is even; if \(p\) is odd the parity of \(\binom p2\) is the parity of \((p-1)/2\). This gives \(\det R=(-1)^{\epsilon(p,s)}\). When the sign is negative, \(\det M=\det M^{\mathsf T}=\det M\det R\) implies \(\det M=0\). Neither the symmetry nor this argument assumes \(D=p\).

## Constructing a matrix of maximal symmetry-allowed rank

Use one hub and \(p\) leaves, with \(A_i=E_{0,i+1}+E_{i+1,0}\) at bond \(p+1\). In a closed trace walk the two possible hub placements pair the adjacent odd/even sites in the two alternating ways. This gives \(M_0=I+R^{-1}\). For odd \(s\), the permutation \(R\) has odd order and no eigenvalue \(-1\), so \(M_0\) is already full rank.

In general take \(E_-=\ker(R+I)\). Because \(R\) is an orthogonal permutation, \(E_-\) has a real orthonormal basis made of normalized alternating vectors on its even word orbits; the real orthogonal complement remains a direct complement after complexification. Put an invertible \(2\times2\) skew block on consecutive pairs of these vectors, leaving a single vector unused if \(\dim E_-\) is odd; set the operator \(K\) to zero on the complement. Then \(K^{\mathsf T}=-K=KR\). Thus \(M_0+K\) satisfies the one-site cyclic relation. It is invertible on the complement, while on \(E_-\) its rank is \(\dim E_--(\dim E_-\bmod2)\). Since all nonreal eigenvalues of \(R\) come in conjugate pairs, \(\det R=(-1)^{\dim E_-}\). Hence \(M_0+K\) has the required rank.

## Realizing the cyclic matrix with explicit bond size

A cyclic-invariant tensor \(T\) on \(2s\) sites can be realized with
\[
1+p^s+2\sum_{j=1}^{s-1}p^j
\]
bond states by a direct layered construction. Set \(n=2s\). Use a cyclic clock with layers \(0,\ldots,n-1\). Layer 0 is a singleton. Layer \(j\) has one word register of length \(j\) for \(1\le j<s\), and of length \(n-j\) for \(s\le j<n\). A letter transition advances the clock by one. During the first \(s-1\) transitions append the read letters to the prefix register. At transition \(s-1\to s\), with prefix \(u\) and read letter \(i\), allow a transition to every suffix \(v\) of length \(s\) with weight \(T(uiv)/n\). During the remaining \(s\) transitions permit exactly the transitions that read and delete the first letter of the suffix, returning to the singleton. The same physical matrices collect all clock-layer transitions with a given letter.

Starting at layer 0 on any specified word gives the product coefficient \(T(w)/n\), since only one suffix is compatible with the rest of the word. A trace start at any other layer gives the same contribution for the cyclic rotation that first starts at layer 0: cut every closed walk where it visits the singleton and rotate its letters and weights. The trace sums all \(n\) starts, including repeated rotations of short-period words with their multiplicity, so is \(T(w)\). The bond count is the sum of the register sizes. Apply this to the interleaved coefficients of \(M_0+K\), and zero-pad the matrices to reach any larger bond dimension.

For a different bound one can use the cyclic-word blocks underlying [GLW Proposition III.1](https://arxiv.org/html/1801.09106#S3) directly on the correction \(K\). For each rotation orbit of supported interleaved words of minimal period \(\ell\), use a disjoint directed cycle with \(\ell\) states, edges labeled by the primitive word. If the desired nonzero orbit coefficient is \(b\), give one edge a weight whose \((2s/\ell)\)-th power is \(b\), and give the others weight one. Exactly one clock start matches a given word in the orbit; the trace traverses the cycle \(2s/\ell\) times. Hence the total bond cost for \(K\) is at most the number of its supported entries. Each paired pair of word orbits of lengths \(\ell_1,\ell_2\le s\) contributes \(2\ell_1\ell_2\le s(\ell_1+\ell_2)\) entries. These orbits are all disjoint in the pairing, so the number is at most \(s p^s\). Direct sum with the hub gives the alternative bound in the theorem. This uses actual trace representations, not only a statement about linear span.
