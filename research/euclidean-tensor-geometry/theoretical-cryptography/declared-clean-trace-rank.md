# Exact rank of heterogeneous declared-clean trace observations

This note treats a synthetic, exact linear measurement model. The declared projections are known to be noise-free by construction, not inferred from noisy samples. The results are rank probabilities and a polynomial test for a unique compatible vector. They do not give a reduction from standard Ring-LWE, a procedure to recognize correct equations in noisy data, or a claimed algorithm for any cryptographic target.

## 1. Model and result

Let \(F=\mathbb F_Q\) be fixed and let \(L/F\) be a finite field extension of degree \(f\). Work in \(V=L^n\), of dimension \(N=fn\) over \(F\), with an \(L\)-bilinear nondegenerate pairing \(\langle\cdot,\cdot\rangle\). The observation schedule consists of nonzero, publicly declared \(F\)-subspaces \(W_1,\dots,W_m\subseteq L\). Write
\[
 k_i=\dim_F W_i,\qquad K=\max_i k_i,\qquad M=\sum_i k_i.
\]
Each \(a_i\) is independent and uniform in \(V\). For a vector \(x\in V\), the \(i\)-th observation is the exact \(F\)-linear functional on \(W_i\)
\[
   w\longmapsto \operatorname{Tr}_{L/F}\big(w\langle a_i,x\rangle\big).
                                                           \tag{1}
\]
It suffices to provide \(k_i\) values in an \(F\)-basis of \(W_i\). A noise variable supported in the declared trace-orthogonal complement of \(W_i\) would make no contribution to (1); no claim is made about a model in which this structural promise is absent or unknown.

For each \(i\) define the scalar stabilizer field \(F_i=\{u\in L:uW_i\subseteq W_i\}\). The notation
\[
 g=\min_{\alpha\in L\setminus F}|\{i:\alpha\notin F_i\}|                  \tag{2}
\]
counts the least number of blocks that reject any one nonbase scalar. If \(L=F\), set \(g=+\infty\). Each \(F_i\) is a subfield: scalar stability is closed under sums and products, and a nonzero stabilizing scalar acts bijectively on the finite \(W_i\), so its inverse also stabilizes. If \(f_i=[F_i:F]\) and \(f>1\), (2) is equivalently
\[
              g=\min_{\ell\ {\rm prime},\ \ell\mid f}
                            |\{i:\ell\nmid f_i\}|.                       \tag{3}
\]
Indeed an element of degree \(b>1\) over \(F\) belongs to \(F_i\) iff \(b\mid f_i\). A prime divisor \(\ell\) of \(b\) can reject no more blocks than that element, and a degree-\(\ell\) element exists. Given bases, each \(F_i\) is itself obtained as a vector space by linear equations on the multiplication-by-\(u\) images of a basis of \(W_i\). Thus (3) is also a polynomially checkable condition, not a quantification the algorithm must enumerate over all \(L\).

Let \(D\) be the \(F\)-nullity of the combined map (1), and \(D_{\rm iid}\) the nullity of an \(M\)-by-\(N\) independent uniform matrix over \(F\).
For every integer \(1\le r\le N\) and \(B\ge |M-N|\), put
\[
       T_r(d)=\prod_{j=0}^{r-1}(Q^d-Q^j).
\]
Then the following finite comparison holds:
\[
  0\le \mathbb E T_r(D)-\mathbb E T_r(D_{\rm iid})
    \le Q^{(N-M)r-g}\sum_{b=1}^{r-1}\big(m Q^{r K+B}\big)^b .             \tag{4}
\]
When \(f=1\), the difference vanishes. In particular the first moment is exact:
\[
   \mathbb E(Q^D-1)=(Q^N-1)Q^{-M}.
\]
If \(M-N\to+\infty\), the combined map is injective with probability tending to one, for any masks. If \(M<N\), injectivity is impossible. In the critical window \(M-N=c\) fixed, suppose \(N\to\infty\) and
\[
                    \frac{g}{K+\log_Q(2m)}\longrightarrow\infty.         \tag{5}
\]
The distribution of \(D\) then approaches that of \(D_{\rm iid}\) in total variation. The common limiting mass at \(d\ge\max(0,-c)\) is
\[
 \frac{C_Q Q^{-d(d+c)}}
      {\displaystyle\prod_{j=1}^d(1-Q^{-j})
       \displaystyle\prod_{j=1}^{d+c}(1-Q^{-j})},
 \qquad C_Q=\prod_{j=1}^\infty(1-Q^{-j}).                                 \tag{6}
\]
In particular, for \(c\ge0\) the limiting probability of a unique compatible vector on consistent data is \(\prod_{j=c+1}^{\infty}(1-Q^{-j})\); when \(c<0\) it is zero.

This lets the ambient field vary. For repeated \(W\) with stabilizer exactly \(F\), we have \(g=m\), so (5) holds in the critical window even for \(K=o(\sqrt{N})\). At the opposite extreme, if all masks have a common stabilizer field larger than \(F\), their observations are naturally grouped over that field; applying the result with that field as base may be more appropriate. Merely knowing that \(\bigcap_i F_i=F\) is not enough to conclude (6); see Section 4.

For a deterministic input instance, consistency, rank, and uniqueness are decided by ordinary Gaussian elimination on the \(M\)-by-\(N\) matrix in (1). If the augmented system is consistent, its solution set is an affine space of dimension \(D\). With explicit field representation, pairing and bases, forming the matrix uses polynomially many field operations in \(N+M\); elimination uses at most \(O(MN\min(M,N))\) operations in \(F\) on top of formation. The finite field is given by its represented basis and operations, e.g. polynomial-basis arithmetic, not by an oracle whose implicit domain has exponentially longer descriptions. For fixed \(F\), this is polynomial in the explicit input length. This algorithmic assertion uses (1)'s exact observations; the probability statement is about the random designs, not about solving a contaminated system.

## 2. Finite moment comparison

\(T_r(D)\) counts ordered independent \(r\)-tuples over \(F\) in the kernel. Fix an \(F\)-independent tuple \(x=(x_1,\ldots,x_r)\in V^r\). Let
\[
    C_i=\{(w_1,\ldots,w_r)\in W_i^r:\ \textstyle\sum_j w_jx_j=0\},
    \quad e_i=\dim_F C_i,\quad H=\operatorname{span}_L\Big(\bigcup_i C_i\Big),
    \quad b=\dim_L H.
\]
The exact probability that \(x\) is in the kernel is \(Q^{-Mr+\sum_i e_i}\). Indeed the \(F\)-linear combinations of the \(i\)-th block's constraints correspond, by the nondegenerate trace pairing, to the vectors \(\sum_j w_jx_j\); hence the rank of these constraints on the uniform \(a_i\) is \(rk_i-e_i\). Their probabilities multiply over the independent \(a_i\). The iid comparison assigns the same fixed tuple probability \(Q^{-Mr}\), proving the sign in (4).

For \(b>0\), a set of \(b\) coordinate positions gives an isomorphism from \(H\) to \(L^b\). In these coordinates \(H\) is a graph with \(b\) free entries. It has some graph coefficient \(\alpha\notin F\): otherwise \(H\) contains a nonzero vector in \(F^r\), giving an \(F\)-linear relation on the \(x_j\). Also \(b\le r-1\), since \(H=L^r\) would force each \(x_j=0\). For every \(i\), the graph's free coordinates of \(C_i\) lie in \(W_i^b\), so \(e_i\le k_i b\). If \(e_i=k_i b\) then *every* choice in \(W_i^b\) gives output coordinates in \(W_i\). Testing each free coordinate alone forces all graph coefficients, including \(\alpha\), into \(F_i\). Thus at least \(g\) of the blocks lose one dimension and
\[
                         \sum_i e_i\le Mb-g.                              \tag{7}
\]
If \(f=1\), every graph coefficient is in \(F\); therefore no such \(H\ne0\) occurs.

For a fixed \(b>0\) there are at most \((\sum_i |W_i|^r)^b\le (mQ^{rK})^b\) possible \(H\) arising this way: each has an \(L\)-basis drawn from the union of the \(W_i^r\). A fixed such \(H\) gives \(b\) independent equations over \(L\) on the vector tuple \(x\), so at most \(Q^{(r-b)N}\) possible tuples even if the \(F\)-independence restriction is discarded. Multiplying this bound by \(Q^{-Mr+Mb-g}\) and summing \(b=1,\ldots,r-1\) proves (4). For \(r=1\) the sum is empty; multiplication of a nonzero vector by a nonzero scalar cannot vanish and therefore every individual nonzero vector has kernel probability exactly \(Q^{-M}\).

## 3. Passage from moments to nullity and uniqueness

Under (5), difference (4) tends to zero for each fixed \(r\). The iid moment tends to \(Q^{-cr}\) because \(\mathbb E T_r(D_{\rm iid})=Q^{-Mr}\prod_{j<r}(Q^N-Q^j)\). The first moment gives tightness on the nonnegative integers. For each \(r\), the \((r+1)\)-st moment gives uniform integrability of \(T_r(D)\): on \(D\ge b>r\) the ratio to \(T_{r+1}(D)\) is at most \(1/(Q^b-Q^r)\). Thus every subsequential law has the same Gaussian-binomial moments \(Q^{-cr}/|\mathrm{GL}_r(F)|\).

Here these moments determine the law, without using ordinary real moment determinacy. For \(u\ge0\) use the finite identity
\[
  1_{\{D=u\}}=\sum_{r\ge u}(-1)^{r-u}Q^{\binom{r-u}{2}}
                      {D\brack r}_Q\,{r\brack u}_Q .
\]
For each finite \(D\) this follows by factoring \({D\brack u}_Q\) and using the finite \(q\)-binomial theorem at \(-1\) for \(D-u\), with the \(D<u\) case immediate. Expectation and summation can be interchanged: for fixed \(u,c,Q\), Gaussian-binomial moments decay as \(O_Q(Q^{-r^2-cr})\), and the other factors together grow as \(Q^{r^2/2+O_{Q,u}(r)}\). The comparison law comes from counting \(M\)-by-\(N\) matrices of rank \(N-d\): divide the number of full-rank factorizations through dimension \(N-d\) by the number of bases of that intermediate space. The resulting finite mass is
\[
 Q^{-d(d+c)}
 \frac{\displaystyle\prod_{j=d+1}^{N}(1-Q^{-j})
       \displaystyle\prod_{j=d+c+1}^{M}(1-Q^{-j})}
      {\displaystyle\prod_{j=1}^{N-d}(1-Q^{-j})}.
\]
The limit is (6). Tightness and convergence of every atom on the integers give total variation convergence; a triangle inequality gives comparison to the finite iid law as well.

## 4. Exact tower formula and an obstruction to intersection-only criteria

Suppose the masks, after reordering, are scalar multiples of subfields in a decreasing tower \(L\supseteq L_1\supseteq\cdots\supseteq L_s\supseteq F\). Let \(k_t=[L_t:F]\) and use \(m_t\) masks at level \(t\). For exact budget \(M=N\), the finite probability that the trace map is injective is
\[
        \prod_{t=1}^s\ \prod_{j=0}^{m_t-1}(1-Q^{-k_t(d_t-j)}),
  \qquad d_t=\frac{N-\sum_{u<t}k_um_u}{k_t}.                              \tag{8}
\]
A nonzero scalar factor can be absorbed into the uniform \(a_i\). Rank of (1) is the dimension of \(\sum_i a_iW_i\) over \(F\) after identifying \(V\) with its trace dual via the nondegenerate pairing. At level \(t\) the preceding span is \(L_t\)-linear since it was assembled from larger fields. If any level wastes a dimension, total rank cannot reach \(N=M\). Otherwise the quotient is an \(L_t\)-space of dimension \(d_t\), and the \(m_t\) independent, uniform projected \(a_i\) must be independent there. This gives (8); with exact budget \(m_t\le d_t\) and the tower implies each \(d_t\) is an integer.

For an explicit failure of the intersection-only criterion, take \(L=\mathbb F_{Q^2}\), \(V=L^n\), \(n-u\) masks \(W_i=L\), and \(2u\) masks \(W_i=F\), for any fixed \(u\ge1\). The intersection of the stabilizers is \(F\), \(g=2u\) and \(M=N\). Formula (8) gives the finite answer
\[
  \left(\prod_{j=u+1}^{n}(1-Q^{-2j})\right)
  \left(\prod_{j=1}^{2u}(1-Q^{-j})\right)
\]
and limiting answer \(C_{Q^2}\prod_{j=1}^u(1-Q^{-(2j-1)})>C_Q\). If \(u\to\infty\) with \(n\ge u\), the same formula instead tends to \(C_Q\). This is an exact example where the number of rejecting blocks, not just their existence, matters.

For a positive genuinely heterogeneous example, let \(L=\mathbb F_{Q^6}\), take \(n=5t\), and use \(6t\) masks \(\mathbb F_{Q^2}\) and \(6t\) masks \(\mathbb F_{Q^3}\). None individually has stabilizer \(F\); nevertheless \(g=6t\), \(M=N=30t\), and the limit is \(C_Q\). In contrast, using only \(\mathbb F_{Q^2}\) masks with \(M=N\) has limit \(C_{Q^2}\). These are families of math objects, not parameter advice about a deployed scheme.

## 5. Relation to prior results and to ring structure

[Cyclic orbit codes and stabilizer subfields](https://www.aimsciences.org/article/doi/10.3934/amc.2015.9.177) develops the scalar stabilizer and orbit/intersection geometry. [Random Krylov spaces over finite fields, Theorem 5](https://www.math.clemson.edu/~sgao/papers/BGL01.pdf) gives exact probabilities for untruncated module generation. [Chen–Tseng, Corollary 3.4](https://arxiv.org/abs/1208.0851) counts equal-width splitting subspaces for a multiplication operator with a generating field element; [Ram, §4](https://doi.org/10.1017/fms.2026.10193) treats general operators for equal-order truncated Krylov spaces. In the present single-component model such equal-order power masks are special cases \(W_i=\operatorname{span}_F(1,\theta,\ldots,\theta^{k-1})\). No novelty is claimed for the previously counted special cases.

The fixed ambient field, homogeneous-mask critical nullity law is already present in [the uniform-support critical-load note](https://github.com/mxym/math/commit/fcc5538a59af172d873b0e89e29d09dca38ae1b7), by taking the trace adjoint of the restricted iid matrix. The additional results here are (4)–(5) for heterogeneous observation spaces, including growing extension and growing mask size, the rejection multiplicity distinction, and the exact nested-mask calculation as a comparison. The proof counts high-deficiency spaces by bases of their equations; it does not assume coordinate entries in (1) are independent.

For a squarefree polynomial ring quotient over a finite field, CRT represents multiplication componentwise in finite fields. A **declared-clean**, componentwise trace observation model on any of those fields is an instance of (1); the statements do not assert that ordinary noisy ring samples give those observations, that joint masks mixing components factor, or that any plausible real-world observation has this error geometry. The exact algebraic simplification is caused by explicitly noise-free projections, not by merely writing a ring in CRT coordinates.

For perspective, if independent additive errors \(E_i\) are present before these projections, then for each fixed input \(x\) and design \((a_i)\) the TV distance between the projected output law and its declared-clean counterpart is exactly
\[
    1-\prod_i\Pr\!\left[\operatorname{Tr}_{L/F}(wE_i)=0
                              \text{ for every }w\in W_i\right].
\]
This compares the laws at fixed \(x\), not after forgetting a mixed input. For uniform scalar errors over \(L\), the probability of coincidence is \(Q^{-M}\) by nondegeneracy; any per-sample density bound \(d\mathcal L(E_i)/dU_L\le \eta_i\) gives at most \(Q^{-M}\prod_i\eta_i\). Thus frequent full rank under the *declared-clean* design does not make the clean-data premise frequent under arbitrary noise.

**Replay.** The accompanying checker enumerates small abstract field rank and moment counts, verifies the graph equality condition independently by finite enumeration, and checks exact tower examples. It does not process noisy samples or reconstruct a hidden vector.
