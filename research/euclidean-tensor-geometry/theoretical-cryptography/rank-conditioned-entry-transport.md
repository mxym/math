# Entrywise transport of rank-conditioned matrices and parity Gaussians

Conditioning an independently generated matrix on full rank usually changes its law by a nonvanishing total-variation distance in the near-square regime. Nevertheless it can be coupled to the original matrix with only a bounded expected number of changed **entries**. An exact-marginal coupling can also achieve the information-theoretically minimal number of changed entries with probability tending to one. A parity lifting transfers both statements to the centered discrete Gaussian coefficient model of dyadic cyclotomics, when conditioning on rank at the prime above two.

These are coupling and geometric stability results. They do not assert that the same coupling is efficiently sampleable, that rank over the ramified residue field is integral surjectivity, or that any deployed scheme's assumptions may be changed.

## 1. Theorems

Let \(q\) be a prime power, \(1\le r\le m\), let \(U\) be the uniform law on \(\mathbb F_q^{r\times m}\), and let \(d_H\) count coordinates (individual entries) at which two matrices differ. If \(P,P'\) have densities \(w,w'\) relative to \(U\) that depend only on matrix rank, then
\[
                W_{1,d_H}(P,P')\le C\,\|w-w'\|_{L^2(U)}     \tag{1}
\]
for an absolute constant \(C\), independent of \(q,r,m\). In particular, the uniform law \(U_{\rm full}\) on full-row-rank matrices satisfies \(W_{1,d_H}(U,U_{\rm full})=O(1)\) uniformly in all three parameters. Likewise on square matrices over any **fixed** finite field, the uniform law on singular matrices is at bounded expected entrywise distance from \(U\).

Over all finite fields, there is also a coupling \((A,B)\) of \(U\) and \(U_{\rm full}\) with
\[
             \Pr\{d_H(A,B)=r-\operatorname{rank} A\}
                     \ge 1-C' r^{-1/2},                       \tag{2}
\]
uniformly for \(m\ge r\) and \(q\), with an absolute constant \(C'\). Any full-rank \(B\) has \(d_H(A,B)\ge r-\operatorname{rank}A\), so even the expected cost in (1) for square matrices over a fixed field cannot vanish (it is at least \(1/q\)). The couplings exhibited for (1) and (2) need not be the same. In particular (2) is not an assertion about the expected cost on its exceptional event.

For context, [Costello's answer to the 2025 MathOverflow coupling question](https://mathoverflow.net/questions/492001/small-hamming-distance-coupling-of-singular-and-nonsingular-matrices-over-f-q) resolves the stated **column**-cost question (replace a bounded expected number of whole columns). Equation (1) is a stronger metric in that example, and covers both types of conditioning. The pointwise rank-deficiency lower bound, and square binary attainment by some nearest invertible matrix, also appear in [On Invertibility of Large Binary Matrices, Lemma 2 and Theorem 4](https://doi.org/10.3390/math14020270). A pointwise nearest-matrix rule does not by itself establish the uniform full-rank second marginal. Here (2) controls that marginal using degrees from **both** sides of the single-coordinate graph. The literature comparisons are about these particular statements, not a priority claim.

## 2. Dense frequencies in each nonzero rank layer

Put \(N=rm\), and write \(|M|\) for the Hamming weight of \(M\) (number of nonzero entries). For every \(1\le k\le r\), let \(\mathcal R_k\) be the rank-\(k\) matrices. We claim
\[
               \mathbb E_{M\sim\mathrm{Unif}(\mathcal R_k)}
                             \frac1{|M|}\le \frac{C_0}{rm} .              \tag{3}
\]

Indeed, let \(L\) be a uniform full-column-rank \(r\times k\) matrix and \(R\) a uniform full-row-rank \(k\times m\) matrix, independently. The law of \(LR\) is invariant under multiplication on both sides by invertible matrices, is supported on rank \(k\), and so is uniform there. The two rank conditions each have probability at least
\[
                       p_*=\prod_{j\ge1}(1-2^{-j})>0
\]
before conditioning independent uniform entries, by the standard sequential basis count.

With \(L\) fixed, let \(I\) be the number of its nonzero rows; \(I\ge1\). Before conditioning \(R\) on rank, its columns are independent uniform \(v\in\mathbb F_q^k\). The random variable \(|Lv|/I\) lies in \([0,1]\) and has mean \(1-1/q\ge1/2\), since every nonzero row gives a uniform dot product. Hoeffding then implies \(\Pr\{|LR|<mI/4\}\le e^{-m/8}\). After conditioning \(R\) the probability is at most \(p_*^{-1}e^{-m/8}\), and \(|LR|\ge1\) on that conditional law. Hence
\[
             \mathbb E[|LR|^{-1}\mid L]\le 4/(mI)+p_*^{-1}e^{-m/8}.
\]
Before conditioning \(L\), the indicator that a row is nonzero is Bernoulli with mean \(1-q^{-k}\ge1/2\). The same argument gives
\(\mathbb E[1/I\mid L\text{ full}]\le 4/r+p_*^{-1}e^{-r/8}\).
As \(m\ge r\), the first display averaged over \(L\) is at most \(C_0/(rm)\), proving (3).

## 3. Fourier transport and exact expected-cost coupling

For a nontrivial additive character \(\psi\) of \(\mathbb F_q\), use characters \(X\mapsto\psi(\sum_{ij} M_{ij} X_{ij})\), indexed by all \(M\in\mathbb F_q^{r\times m}\). They form an orthonormal basis on \(U\), since multiplication by any nonzero scalar preserves the sum over the field. If \(h=w-w'\), then \(\widehat h(0)=0\). Transposing the left and right group actions in the Fourier pairing shows \(\widehat h(M)\) is constant on each rank orbit. Therefore (3) and Parseval give
\[
       \sum_{M\ne0}\frac{|\widehat h(M)|^2}{|M|}
       \le \frac{C_0}{rm}\|h\|_2^2.                            \tag{4}
\]
On the other hand, for any real \(1\)-Lipschitz function \(f\) in entrywise Hamming distance, let \(P_{ij}\) average over the single entry \((i,j)\) with others fixed. Then
\[
 \sum_M |M|\,|\widehat f(M)|^2
   =\sum_{ij}\|f-P_{ij}f\|_2^2\le rm/4 ,
\]
because the conditional range is of length at most one and the variance of a real variable in an interval is at most one quarter of the squared length. Cauchy–Schwarz with (4) bounds \(|\mathbb E_U[fh]|\le \sqrt{C_0}\|h\|_2/2\). Finite Kantorovich–Rubinstein duality proves (1), including existence of a coupling attaining the infimum. No enumeration of the Fourier coefficients on rank layers is required.

For a rank event of probability \(p\), the right side for its conditional law versus \(U\) is \(C\sqrt{1/p-1}\). For full row rank \(p\ge p_*\) over all these fields and sizes. For singularity of a square \(p\ge1/q\), by the last step in the sequential column rank count. This gives the two bounded-cost consequences stated above.

## 4. Rank layers and a matching marginal up to small TV

Consider the bipartite graph between \(\mathcal R_k\) and \(\mathcal R_{k+1}\), with edges exactly single-coordinate changes. Let \(K_k\) move from rank \(k\) by choosing uniformly one rank-increasing neighbor, \(k<r\). Such neighbors always exist: a proper column space and a proper row space each miss some coordinate vector, and choosing both increases rank by one. More generally, an update by \(c e_i e_j^{\mathsf T}\) for \(c\ne0\) can increase rank by one **only** if \(e_i\) is outside the column space and \(e_j\) outside the row space, in which case all \(q-1\) values of \(c\) do so. If \(e_i\) is outside the column space, the new kernel is the old kernel intersected with \(\ker e_j^{\mathsf T}\), proving this direction; use transpose when only the row condition holds. If both coordinate vectors are inside, the rank cannot increase. The induced map \(T\) from the domain quotient by the old kernel to the old column space is invertible. The matrix determinant lemma shows that the update decreases rank exactly when \(1+c e_j^{\mathsf T}T^{-1}e_i=0\); thus there is one downward change at this position if the pairing is nonzero, and none otherwise.

Let \(V_k\) be uniform on \(\mathcal R_k\). For the uniform measure on graph edges, the left and right marginals are \(V_k,V_{k+1}\) biased by their respective degrees \(d^+,d^-\). Thus
\[
 \|V_k K_k - V_{k+1}\|_{\rm TV}
       \le \tfrac12\mathbb E\big|d^+/\mathbb E d^+-1\big|
            +\tfrac12\mathbb E\big|d^-/\mathbb E d^--1\big| .       \tag{5}
\]
Indeed the conditional edge law given its left endpoint is \(K_k\), and stochastic maps contract TV. Expectations use the uniform law on the corresponding side.

For a rank layer \(k\), the two spaces are independent uniform \(k\)-subspaces of their respective dimensions. This follows from the transitive group action and the fact that each pair of spaces admits the same number \(|GL_k(\mathbb F_q)|\) of isomorphisms from the domain quotient to the column space, which are uniform conditional on the spaces. In a uniform \(k\)-subspace of \(\mathbb F_q^a\), each \(e_i\) is included with probability \(p=(q^k-1)/(q^a-1)\). Distinct coordinate vectors have nonpositive inclusion covariance, since their joint probability (for \(a\ge2\)) is
\[
       \frac{(q^k-1)(q^k-q)}{(q^a-1)(q^a-q)}\le p^2
\]
for \(k\ge1\), with the \(k=0\) case immediate. The same covariance bound holds for exclusion indicators. Thus either type of count has variance at most its expectation. The upward degree is \(q-1\) times the product of the two independent **exclusion** counts, whose means are at least \(r/2,m/2\) as \(k<r\). Its relative mean absolute deviation is \(O(r^{-1/2})\), using independence and the inequality
\[
      \mathbb E|UV-1|\le\mathbb E|U-1|+\mathbb E|V-1|
\]
for nonnegative independent mean-one \(U,V\).

For the downward degree let \(\ell=k+1\), and conditional on the column/row spaces let \(I,J\) count their included coordinate vectors. Let \(T\) be the uniform induced isomorphism from the domain quotient to the column space. Each included pair is eligible for a downward change exactly if \(e_j^{\mathsf T}(T^{-1} e_i)\ne0\), where the functional is well-defined on the domain quotient. The image of a fixed \(e_i\) is uniform nonzero in \(\mathbb F_q^\ell\), so the conditional mean is \(\theta_\ell IJ\), \(\theta_\ell=(q-1)q^{\ell-1}/(q^\ell-1)\ge1/2\).

For two distinct pairs with the same \(i\), the two functionals are independent since the coordinate rows are independent and annihilate the old kernel. Comparing a single uniform nonzero vector to a uniform arbitrary vector incurs TV \(q^{-\ell}\); in the latter case the two evaluations are independent uniform field elements. For different \(i\), two distinct coordinate vectors in the column space are independent, so their two inverse images are a uniform ordered independent pair. Compare this to two iid uniform unrestricted vectors, which are dependent with probability at most \((q+1)q^{-\ell}\). Again the tested evaluations are independent in the unrestricted pair, whether or not the same functional is used twice. Thus the covariance of the nonzero indicators is \(O(q^{1-\ell})\), including the difference between the marginal mean \(\theta_\ell\) and \(1-1/q\). Repeated identical pairs have variance at most one. Thus
\[
        \operatorname{Var}(d^-\mid I,J,\text{spaces})
                \le IJ+C_1 (IJ)^2 q^{1-\ell}.                 \tag{6}
\]

Write \(a=\mathbb E I\), \(b=\mathbb E J\), which are positive. The inclusion variance bounds and independence give
\(\mathbb E|IJ/(ab)-1|\le a^{-1/2}+b^{-1/2}\).
By (6), \(\mathbb E|d^--\theta_\ell IJ|\le \sqrt{ab}+C_2 ab\,q^{(1-\ell)/2}\). Dividing the latter by \(\theta_\ell ab\) gives an additional \(O((ab)^{-1/2}+q^{(1-\ell)/2})\) in (5). If \(a,b\ge1\), \((ab)^{-1/2}\) is bounded by the previous inverse-square-root terms; if either is smaller than one, the trivial bound TV \(\le1\) suffices. Put \(u=m-r\) and \(h=r-k\). Then \(a\ge (r/2)q^{-(h-1)}\) and \(b\ge(m/2)q^{-(u+h-1)}\). For \(1\le h\le r/2\) we have \(\ell\ge r/2\), so (5) is at most \(C_3\,q^{(u+h-1)/2}/\sqrt r\); a bound above one is harmless.

## 5. Proof of the high-probability minimal-edit coupling

For \(A\sim U\) let \(D=r-\operatorname{rank}A\). For each \(j\ge1\),
\[
           \Pr(D\ge j)\le p_*^{-1}q^{-j(u+j)}                 \tag{7}
\]
because each fixed \(j\)-dimensional subspace of the left kernel annihilates all \(m\) columns with probability \(q^{-jm}\), and there are at most \(p_*^{-1}q^{j(r-j)}\) such subspaces. The latter count follows by counting ordered bases and dividing by \(|GL_j(\mathbb F_q)|\). Conditional on \(D=j\le r/2\), run \(K_{r-j},\ldots,K_{r-1}\) to obtain \(B_0\). Its distance from \(A\) is exactly \(j\): the path uses \(j\) single-coordinate changes and must correct the rank difference. By (5) and TV contraction, its law conditional on \(D=j\) differs from \(V_r\) by at most \(C_3 r^{-1/2}\sum_{h=1}^jq^{(u+h-1)/2}\). For larger \(j\) the same path exists and the error bound 1 suffices. For each \(j\) glue a maximal coupling of \(B_0\)'s conditional law and \(V_r\), producing \(B\) with conditional law \(V_r\) and with mismatch probability at most this bound. The unconditional mismatch is at most
\[
 C_4r^{-1/2}\sum_{h\ge1}q^{(u+h-1)/2-h(u+h)}
         +p_*^{-1}2^{-\lfloor r/2\rfloor^2}=O(r^{-1/2}),
\]
uniformly for \(u\ge0\) and \(q\), with small \(r\) absorbed into the constant. This proves (2). Exact minimality for all pairs at all finite sizes is false: at \(r=1,m\ge2\) every already full input would have to stay fixed, but the zero input cannot spread its remaining mass to all nonzero outputs using only one coordinate change (already over the binary field).

## 6. Exact parity lift and the dyadic Gaussian consequence

Let a product law on \(\mathbb Z^N\) have independent discrete Gaussian coordinates, with arbitrary positive widths and real centers, and partition its coordinates into nonempty blocks. Let \(\Pi\) record the parity of the sum in each block, and write \(K_b\) for the conditional law at parity vector \(b\). For **any** laws \(p,p'\) on the parity vectors, put \(P=\sum_b p(b)K_b\), \(P'=\sum_b p'(b)K_b\). Then
\[
                 W_{1,\ell_1}(P,P')
                   =W_{2,\ell_2}(P,P')^2=W_{1,d_H}(p,p').     \tag{8}
\]
An analogous equality holds if cost counts altered integer coordinates. Every coupling downstairs lifts to one with exactly a single \(\pm1\) change in each changed block, and nothing changed in matching blocks.

For one coordinate, couple the distributions conditional on even and odd by the same quantile of their two ordered supports. On the *even* grid, the odd law shifted by \(-1\) has center \(c-1\) and the odd law shifted by \(+1\) has center \(c+1\), with width the same and \(c\) the center of the unshifted law. On a common grid, a discrete Gaussian's density ratio for increasing the center is increasing in the coordinate, which implies stochastic ordering. For instance the difference of the two densities has at most one sign change and the total difference is zero, yielding the cumulative inequalities. Therefore under the quantile coupling \(Z_{\rm odd}-1\le Z_{\rm even}\le Z_{\rm odd}+1\), so the difference is exactly one in absolute value. For a whole block, couple arbitrarily the two conditional laws of the pair (prefix parity, last coordinate parity) under the two opposite total parities. Any pair of such parity pairs differs in exactly one component. In the unchanged component couple identically and in the changed component use induction (or the single-coordinate coupling); given each parity pair, the prefix and last coordinate have independent conditional laws. This proves the block statement, and independent coupling given both parity vectors gives the lift. Any coupling must alter each changed block at least once in integer distance, so both costs in (8) have the claimed lower bound.

In the dyadic cyclotomic ring \(R_n=\mathbb Z[\zeta_{2n}]\), the residue at the unique prime above two is the parity of the sum of power-basis coefficients. Take an \(r\times m\) matrix of independent centered canonical discrete Gaussians, with coefficient width \(t=s/\sqrt n\). Let \(X\) denote this matrix and \(Y\) have its exact law conditioned only on full residue rank. Put \(\lambda=\exp(-\pi/\min(t,1)^2)\). The one-dimensional Gaussian Fourier bound (e.g. §2 of [the subfield note](dyadic-subfield-generation.md), or the first factor in Jacobi's product) gives \(|\phi_t(1/2)|\le e^{-\lambda}\), so the parity table of \(X\) differs from \(U\) in TV by at most \(\delta=rm\,e^{-\lambda n}/2\). If \(F\) is the full-rank event, conditioning both laws costs at most \(2\delta/U(F)\) in TV, by subtracting the two normalized restricted probabilities; \(U(F)\ge p_*\). Joining maximal couplings at the ends of (2), and then applying the exact lift, gives a coupling of \(X,Y\) under which the number of modified coefficients is exactly the residue rank defect of \(X\), each by \(\pm1\), except with probability \(O(r^{-1/2}+rm\,e^{-\lambda n})\). Separately, from (1), (8) and the triangle inequality for entrywise transportation,
\[
                W_{2,\mathrm{coef}}(X,Y)^2
                       \le C_5 + C_6 (rm)^2 e^{-\lambda n}.
\]
The same bound holds for \(W_{1,\ell_1}\) in coefficient norm. In canonical Euclidean norm the squared \(W_2\) cost is \(n\) times the coefficient cost by the orthogonal power-basis normalization. Neither conclusion conditions on full integral generation, where odd-prime failures require separate information.

## Reproduction

Run `python3 verify-rank-conditioned-entry-transport.py`. It checks generated finite matrices, exact Fourier orbit equality, reverse degree identities and uniform-edge marginal accounting, plus finite rational instances of the parity lift. The asymptotic theorem is proved above, not inferred from those examples.
