# Uniform Smith-profile comparison in growing dyadic ramified quotients

The law of a single coefficient-noise entry can remain far from uniform in a ramified quotient, even while the **entire Smith profile** of a large matrix of such entries converges to the uniform-matrix profile. We prove this uniformly in the dyadic ring degree, via a two-kernel Fourier estimate for Schur lifting and a conditional digit bound. The matrix and coefficient draws are synthetic; no hard problem, concrete parameter set, or scheme is evaluated.

## 1. Statement

Let \(d\) be any power of two and \(R_d=\mathbb F_2[T]/(T^d)\). This is exactly the reduction of \(\mathbb Z[Y]/(Y^d+1)\) modulo \(2\), with \(Y=1+T\); \(T\) generates the unique maximal ideal of the quotient. Let \(u\ge0\) be fixed, \(n\to\infty\), and consider \(n\times(n+u)\) matrices. In the input matrix independently sample each entry as
\[
 \sum_{j=0}^{d-1} B_j(1+T)^j,\qquad
 B_j\in\mathbb F_2\text{ independent},\qquad
 \mathbb E(-1)^{B_j}=\delta .
\]
Assume \(|\delta|\le\delta_0<1\) uniformly in \(d,n\). This includes the parities of independent centered one-dimensional integer Gaussian coefficients with any fixed positive width. In the dyadic coefficient basis, the canonical metric is a common scaling of the coefficient metric. The comparison matrix has independent uniform \(R_d\) entries. Write \(\Delta_{n,d}\) for the TV distance between the laws of their cokernels **as isomorphism classes of \(R_d\)-modules** (equivalently, their full truncated Smith profiles).

There exist constants \(c,C>0\), depending only on \(u,\delta_0\), with the following property. Choose any integer \(1\le K\le\min(d,n)\), and put \(B\) equal to the least power of two at least \(K\). If
\[
 K\,\operatorname{artanh}\!\left(|\delta|^{d/B}\right)\ \le\ \tfrac14\log n,
 \tag{1}
\]
then the TV distance for the projected \(R_K\)-cokernels is at most \(Ce^{-cn}\), and
\[
 \Delta_{n,d}\le Ce^{-cn}+{\bf1}_{K<d}\,2^{1-K(u+1)}. \tag{2}
\]
The logarithm in (1) is natural. The constants do not depend on \(d,K\) or the exact bias. For example \(K=\min(d,\lfloor c_0\log n\rfloor)\) works for all sufficiently large \(n\) with suitably small fixed \(c_0>0\). This implies a uniform polynomial-rate convergence over all dyadic \(d\), and exponential convergence whenever that choice includes all \(d\) digits. When \(d\) is of order \(n\), (1) allows \(K\) of order \(n/\log n\), giving a stretched exponential bound. For a fixed nonzero bias and \(d\to\infty\), the individual full-depth entry law has TV tending to one from uniform: its \((1+T)^j\) coefficient vector has the biased product Hamming-weight law, whereas the comparison vector is unbiased. Thus (2) does not follow by coupling the full entry laws.

## 2. Conditional two-kernel Schur lifting

This ingredient applies more generally over a finite commutative chain ring with uniformizer \(\pi\), length \(K\), and residue field \(F\) of size \(q\), with all residue digits given by fixed representatives. Consider an \(n\times m\) matrix \(M\), and fix its first digit \(M_0=M\bmod\pi\) of rank \(s\). Let \(r_L=n-s,\ r_R=m-s\), and let \(d_L,d_R\) be the minimum nonzero Hamming weights of its left and right residue kernels when their dimensions are positive.

Assume, for each \(1\le j<K\), that given the entire original matrix history through digit \(j-1\), its digit-\(j\) entries are **independent conditional on that history**, and every nontrivial additive Fourier coefficient of each entry's conditional law has magnitude at most \(b_j\in[0,1]\). The numbers \(b_j\) need not be the same across levels, and there is no independence assumption between the digits of a single entry. If both kernel dimensions are positive, the law of the remaining Schur block divided by \(\pi\), through all \(K-1\) layers, satisfies
\[
 D_{\rm KL}\bigl(P_{M_0}\,\|\, U\bigr)
 \ \le\ \sum_{j=1}^{K-1}
 \log\!\left(1+(q^{r_Lr_R}-1)b_j^{\,2d_Ld_R}\right).
 \tag{3}
\]
Here \(U\) is an independent uniform \(r_L\times r_R\) matrix over the length-\((K-1)\) quotient, and \(P_{M_0}\) is conditional on the fixed first digit. Relative entropy uses natural logarithms. The conditional cokernel TV comparison to the Haar matrix with the same first-digit rank follows by the deterministic Smith map and Pinsker's inequality. If either kernel dimension is zero, the first digit alone determines the cokernel, with the appropriate free summand, and the comparison is exact.

**Proof.** Choose invertible row and column operations over the residue field reducing \(M_0\) to an identity block and zeros. Lift the operations to invertible matrices over the chain ring. Their bottom rows and final columns, reduced modulo \(\pi\), form a left-kernel basis \(L\) and a right-kernel basis \(Q\) respectively; their dimensions are \(r_L\times n\) and \(m\times r_R\). In transformed coordinates the Schur block is
\[
 S=D-CB^{-1}E,\qquad
 \widetilde M=\begin{pmatrix}B&E\\ C&D\end{pmatrix}.
\]
The unit block \(B\) is invertible and \(C,E,D\) vanish modulo \(\pi\). Consequently \(S\) is divisible by \(\pi\) and block elimination gives exactly the cokernel of \(S\). If one changes the digit-\(j\) matrix by \(Z\) with all earlier digits fixed, then modulo \(\pi^{j+1}\) the difference in \(S\) is \(\pi^j LZQ\): any change to the correction \(CB^{-1}E\) has valuation at least \(j+1\), since the other outside block is divisible by \(\pi\), and the inverse of the top block changes by a multiple of \(\pi^j\). So the new significant digit of \(S/\pi\) is \(LZQ\) up to a shift determined by the history. This derivative argument works for arbitrary residue digit representatives, with all carries in the history-dependent shift.

For a nonzero additive Fourier frequency of the \(r_L\times r_R\) target, its pulled-back coefficient matrix has the form \(L^T A Q^T\) with \(A\ne0\), using a fixed nontrivial additive character of \(F\). It is nonzero because both basis maps have full rank. Every column lies in the left kernel and every row lies in the right kernel, so a nonzero column forces at least \(d_L\) nonzero rows, each of weight at least \(d_R\). Thus the absolute conditional Fourier coefficient is at most \(b_j^{d_Ld_R}\). The product exponent is exact at the level of smallest possible support: an outer product of two minimum-weight kernel vectors is an allowed frequency. For instance, for the first lifted digit with all entry biases equal over \(\mathbb F_2\), such a frequency actually has coefficient of magnitude \(b_1^{d_Ld_R}\).

Parseval bounds conditional \(\chi^2\) from uniform by \((q^{r_Lr_R}-1)b_j^{2d_Ld_R}\). Conditioning only on the past Schur digits instead of the original past gives a mixture of these conditional laws, so the same bound holds by convexity. Since \(D_{\rm KL}\le\log(1+\chi^2)\), the entropy chain rule proves (3). For a Haar original matrix, the higher digits are independent and exactly uniform; \(Z\mapsto LZQ\) is onto, so all the Schur digits are independent Haar conditional on \(M_0\). This reference depends only on its rank for the subsequent cokernel law. The original ring length and dimension need not be kept fixed in (3). At \(K=1\) there are no higher digits and the two conditional cokernel laws agree exactly.

## 3. Digit balance in the dyadic coefficient model

In \(R_B\), \((1+T)^B=1\) because \(B\) is a power of two. Thus the entry can be expressed with \(B\) independent parity-sum coefficients \(\widetilde B_i\) in the \((1+T)^i\) basis. Each such coefficient XORs \(d/B\) original bits, so its absolute bias is \(\eta=|\delta|^{d/B}\). Reduction to \(R_K\) does not change its first \(K\) digits.

Fix a lower-digit history in one entry and consider digit \(j<K\). Adding \(T^j\) pairs all coefficient vectors compatible with the history into pairs that have opposite digit \(j\), because it leaves all lower digits fixed. In the \((1+T)^i\) basis it flips exactly \(w_j=2^{s_2(j)}\) bits, where \(s_2(j)\) is the binary digit sum; this follows by expanding \((Y-1)^j\) in characteristic two, or multiplying its binary-digit factors. The probability ratio within each pair is between \(R^{-w_j}\) and \(R^{w_j}\) for \(R=(1+\eta)/(1-\eta)\), by independence of the parity-sum coefficients. Summing over pairs therefore bounds conditional digit bias uniformly by
\[
 b_j\le \tanh\bigl(2^{s_2(j)}\operatorname{artanh}\eta\bigr)
 \le \tanh\bigl(K\operatorname{artanh}\eta\bigr).
 \tag{4}
\]
The last inequality uses \(2^{s_2(j)}\le j+1\le K\), by the binomial expansion count. Across matrix entries, conditioning on the full lower-digit matrices places separate constraints on independent entries, so it preserves conditional independence. The first digit itself is the parity of all \(d\) original bits; its absolute bias is \(|\delta|^d\).

Under (1), (4) implies \(1-b_j\ge n^{-1/2}\): use \(1-\tanh(x)=2/(e^{2x}+1)\). This conditional estimate applies even when the whole entry is not close to uniform; it is the ingredient used instead of a total-variation bound on the entry.

## 4. First-digit rank and the complete profile

For the following estimates, the actual first digit is iid binary with bias at most \(\delta_0<1\), so every bit has maximum mass at most \(1-\alpha\) for the fixed \(\alpha=(1-\delta_0)/2\). A vector of independent such entries hits any fixed linear subspace of codimension \(a\) with probability at most \((1-\alpha)^a\): condition on the free coordinates, which prescribe the remaining \(a\) coordinates if membership holds.

We record three consequences, with uniform exponentially small exceptions.

1. **Dense kernels.** For any nonzero vector of support at most \(\gamma n\), any individual independent row (or column for the other kernel) annihilates it with probability at most \(1-\alpha\) by conditioning on all but one nonzero coefficient position. A union bound over these vectors and the full \(n\) rows or \(n+u\) columns proves that both nontrivial kernels have minimum weights at least \(\gamma n\), for fixed sufficiently small \(\gamma>0\). Indeed the binary Hamming ball count is at most \(\exp[O(\gamma\log(1/\gamma))n]\) for fixed \(u\).
2. **Few missing ranks.** If the rank is at most \(n-r\), some \(n-r\) rows span all rows. For each fixed choice the other \(r\) independent rows lie in a subspace of codimension at least \(r+u\). The bound is therefore \(\binom nr(1-\alpha)^{r(r+u)}\). Taking \(r=\lceil c_1\sqrt n\rceil\) with \(c_1\) large enough makes this exponentially small. In particular \(r_Lr_R=O(n)\) outside that exception.
3. **Haar first-digit rank law.** Expose the first \(\lfloor n/2\rfloor\) rows, which are linearly independent with exponentially high probability by the codimension bound. Their orthogonal complement has no nonzero vector of weight below \(\gamma n\), again by the Hamming-ball union bound, now with only \(\lfloor n/2\rfloor\) independent tests. At every later step, the orthogonal complement of the current span \(W\) is a subspace of that initial orthogonal complement. Orthogonality of additive characters gives
   \[
   \bigl|\Pr(\text{next row lies in }W\mid W)-2^{-\operatorname{codim} W}\bigr|
   \le \delta_0^{\gamma n}.
   \]
   The Haar row-span rank process has exactly the transition probability \(2^{-\operatorname{codim} W}\) of not increasing rank. Couple its transitions from rank \(\lfloor n/2\rfloor\); its early rows are also independent with exponentially high probability. The accumulated disagreement probability is exponentially small, proving the asserted TV comparison of rank laws.

On the good event of the first two statements, the right side of (3) is at most
\[
 n\,2^{O(n)}\exp(-2\gamma^2 n^{3/2}),
\]
using \(K\le n\) and \(1-b_j\ge n^{-1/2}\). Its square root is also exponentially small. Compare first to a Haar higher-digit law conditional on the same first-digit rank, and then use statement 3 to replace that rank law by Haar. This proves the \(Ce^{-cn}\) bound over \(R_K\).

For the Haar-cokernel tail in the full-depth comparison, over \(R_K\) the expected number of surjections from the matrix cokernel to \(R_K\) is at most \(2^{-Ku}\). Indeed there are at most \(2^{Kn}\) candidate surjections from \(R_K^n\); every fixed surjection kills all \(n+u\) independent Haar columns with probability \(2^{-K(n+u)}\). Whenever the cokernel has a depth-\(K\) summand it surjects onto \(R_K\), and multiplying a surjection by all units produces \(2^{K-1}\) different ones. This bounds the tail probability by \(2^{1-K(u+1)}\). By the elementary divisor decomposition for this chain ring, reduction from \(d\) to \(K\) caps all Smith exponents at \(K\). Couple the projected profiles, then lift the coupling. If the projected profiles agree and the Haar profile has no depth-\(K\) summand, all full exponents already agree. This proves (2); when \(K=d\) no lifting or tail bound is needed.

## 5. Prior work and scope

[Maples, *Cokernels of random matrices satisfy the Cohen–Lenstra heuristics*](https://arxiv.org/abs/1301.1239) develops quantitative universality over the \(p\)-adics. [Lvov, *Universality results for random matrices over finite local rings*, arXiv:2601.10821v1, Theorems 1.1 and 2.2](https://arxiv.org/html/2601.10821v1) treats general fixed finite local rings and stronger invariants, with constants depending on the ring and smallest nonzero atom. The result here is narrower in its law but uniform when the dyadic ramification depth and matrix dimension grow simultaneously and the full-entry law may be far from uniform. [Wang–Stanley, *The Smith Normal Form Distribution of a Random Integer Matrix*](https://math.mit.edu/~rstan/papers/randomsnf.pdf) gives context for Haar matrix Smith laws, and classical repeated-root coding identities explain the binary toggle weight. We only need the elementary parity calculation above. No claim about determinants or the geometrically embedded column span, or about universal distributions at all moduli simultaneously, is made.

The [existing dyadic Gaussian module generation analysis](cyclotomic-gaussian-module-generation.md) concerns integer-module surjectivity under different hypotheses. The present result treats the full local invariant-factor law in the finite ramified mod-\(2\) quotient and makes no global generation assertion. The supplied verifier uses small synthetic digit laws to check the algebra and conditional Fourier identities. It neither fits a hardness estimate nor uses any cryptographic samples.
