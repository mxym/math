# A cyclotomic symmetry obstruction to the odd Ehlich bound

**Yongxian Zhang.** AI-assisted proof development and internal verification.

Let \(q\ge11\) be prime with \(q\equiv1\bmod4\), and set \(n=7q\). Put \(c=(7q-3)/4\). Suppose a rational prime \(p\) divides \(c\) to odd valuation, and \(p^j\equiv-1\bmod q\) for some \(j\ge1\). Then an \(n\)-by-\(n\) \(\{\pm1\}\)-matrix attaining the Ehlich determinant bound cannot have a row/column monomial automorphism of order \(q\), i.e. a pair \((P,Q)\) of signed permutation matrices of joint order \(q\) with \(PHQ^{\mathsf T}=H\).

In particular this excludes such order-73 symmetry at order \(511=7\cdot73\), the first higher-order candidate not excluded by Tamura's rational-form tests: \(c=127\) and \(127^{18}\equiv-1\bmod73\). No assertion is made about matrices without the specified symmetry.

## Canonical Gram spaces

At equality in the odd-order Ehlich bound, independently switching signs and permuting rows and columns puts both Gram matrices in the same canonical form
\[
HH^{\mathsf T}=H^{\mathsf T}H=G=(n-3)I_n-J_n+4\operatorname{diag}(J_q,\dots,J_q)
\]
with seven blocks (see [Browne–Egan–Hegarty–Ó Catháin, *A Survey of the Hadamard Maximal Determinant Problem*, Theorem 28](https://doras.dcu.ie/28743/1/A%20survey%20on%20the%20Hadamard%20maximal%20determinant%20problem.pdf)). The two normalizations are independent since any signed permutation on one side leaves the opposite Gram invariant. In particular \(GH=HG\). Let \(L\) be the seven-dimensional subspace of vectors constant on each block. It is the direct sum of the eigenspaces of \(G\) with eigenvalues \(n-3+4q\) and \(n-3-3q\); \(L^\perp\) has eigenvalue \(n-3\). Since these eigenvalues are distinct, \(H\) and \(H^{\mathsf T}\) preserve \(L\).

In the normalized block-indicator basis of \(L\), the matrix \(C\) of \(H|_L\) consists of the common row sums in its \(q\times q\) blocks. It satisfies
\[
 CC^{\mathsf T}=(n-3+4q)I_7-qJ_7
 \quad\Longrightarrow\quad |C_{ij}|^2\le n-3+3q=10q-3<q^2 .
\]

## From an automorphism to a cyclotomic norm

After normalization an automorphism still has the form \(P H Q^{\mathsf T}=H\), with \(P G P^{\mathsf T}=Q G Q^{\mathsf T}=G\). The signs in either signed permutation are common across all coordinates: a pair with opposite signs would transform an off-diagonal entry from \(\{3,-1\}\) to \(\{-3,1\}\), disjoint from the allowed values. The common sign is positive for odd order. The permutations preserve the block partition because they preserve the locations of the entry 3. Their action on the seven blocks is trivial since \(q>7\); in each block a permutation either fixes every coordinate or is a full \(q\)-cycle.

At least one permutation is nontrivial. If on one side a block cycles and on the other side a block is fixed, invariance makes rows constant across the cyclic column block (or columns constant across the cyclic row block). The corresponding common row or column sum has absolute value \(q\), impossible by the bound on \(C_{ij}\) (common column sums agree with row sums by totaling the block). Thus all seven blocks on both sides cycle. Label each cycle so that its permutation is the same standard shift. The matrix \(B=(J_n-H)/2\) is then a \(7\times7\) array of circulant \(q\times q\) blocks.

Restrict \(B\) to the seven-dimensional complex Fourier subspace with primitive character \(\zeta_q\) (one vector in each block). The restricted matrix \(M\) has entries in \(\mathbb Z[\zeta_q]\), as the Fourier transform of each circulant block is evaluation of an integer polynomial in \(\zeta_q\). This subspace lies in the complexification of \(L^\perp\), so \(J_n\) vanishes there, and the Gram identity gives \(MM^*=c I_7\). With \(\alpha=\det M\) we get \(\alpha\overline{\alpha}=c^7\).

For completeness, any nonzero \(\alpha\in\mathbb Z[\zeta_q]\) with \(\alpha\overline\alpha=N\in\mathbb Z\) must have \(v_p(N)\) even under the assumed congruence. Write \(\alpha=F(\zeta_q)\) for \(F\in\mathbb Z[X]\). If \(p\mid N\), reduce the norm identity at each primitive \(q\)-th root \(\omega\) in \(\overline{\mathbb F}_p\). Here \(p\ne q\): since \(p\mid c\), any case \(p=q\) would imply \(q\mid3\). The congruence gives \(F(\omega^{-1})=F(\omega)^{p^j}\), so every such root is a zero of \(F\) modulo \(p\). These roots are simple; hence \(\Phi_q\) divides \(F\) modulo \(p\), implying \(\alpha=p\beta\) in \(\mathbb Z[\zeta_q]\). Now \(\beta\overline\beta=N/p^2\) is rational and an algebraic integer, so is an integer. Iterate to obtain the even valuation. But \(v_p(c^7)\) is odd. This contradiction proves the obstruction.

## Scope and prior results

[Tamura's analysis of Ehlich block matrices](https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/1465-8.pdf) supplies earlier rational-form obstructions and, in the normal Gram setting, a group-divisible design description. The additional hypothesis here concerns monomial automorphisms and the proof obstructs their nontrivial Fourier character. It does not decide attainment at order 511 without that symmetry, nor the maximal determinant at any order. For recent searches for lower-bound witnesses at other odd orders see [Butbaia et al., arXiv:2608.22518v3](https://arxiv.org/abs/2608.22518v3). No exhaustive priority claim is made.
