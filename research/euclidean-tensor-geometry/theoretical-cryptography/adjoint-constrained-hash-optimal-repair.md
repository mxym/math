# Exact readout laws and optimal repair seeds for adjoint-constrained hashing

A uniform self-adjoint matrix in a finite field product does not behave like a uniform unrestricted matrix on all simultaneous readouts. This note determines the exact readout deficit. It also determines **the minimum number of equally likely auxiliary seed values** for an independent additive perturbation that removes the deficit for every input up to given rank budgets. Correlating the corrections across the field factors does not reduce this number, even if the randomized correction is not linear.

This is a positive finite-algebra result. It treats specified distributions with no cryptographic target or secret-dependent experiment.

## 1. Two local readout laws

There are two types of adjoint orbit. In each type all column spaces and ranks are over that orbit's output field.

### Unitary factor

Let \(K=\mathbb F_{q^2}\), \(F=\mathbb F_q\), and \(D^*=\bar D^{\,T}\), using the nontrivial involution of \(K/F\). Let \(H\) be uniform among the \(n\times n\) Hermitian matrices. Fix a full-row-rank \(W\in K^{m\times n}\) and input matrix \(X\in K^{n\times b}\) of rank \(r\). Put
\[
 U=\operatorname{im}X,\qquad V=\operatorname{im}W^*,\qquad s=\dim_K(U\cap V).
\]
The observation \(WHX\) is uniform on an \(F\)-linear subspace of size \(q^{2mr-s^2}\). By comparison \(WAX\) for unrestricted uniform \(A\) is uniform on a space of size \(q^{2mr}\). In particular the exact collision probability for a fixed difference \(X\) is
\[
 \Pr(WHX=0)=q^{-2mr+s^2}. \tag{1}
\]

To see this, replace the columns of \(X\) by any basis of \(U\) and the rows of \(W\) by adjoints of a basis of \(V\). These operations only remove deterministic column relations and make invertible changes of coordinates. Use a common basis of \(U\cap V\) first in both bases, and extend their union to a basis of \(K^n\). Congruence by the full change-of-basis matrix is an \(F\)-linear bijection on Hermitian matrices, so its entries have the usual independent Hermitian degrees of freedom in this basis. Read the pairings \(v^*H u\) for \(v\) and \(u\) in the respective bases. Both entries of an adjoint pair occur exactly when both indices lie in the common basis. Thus only the \(s\times s\) block has a Hermitian constraint; the other entries are independent uniform \(K\) values. The common block contributes \(s^2\) rather than \(2s^2\) base-field dimensions. This proof does not assume the subspaces are nonisotropic or choose orthonormal bases.

### Exchanged pair

Over \(K=\mathbb F_Q\), model two exchanged factors by the public pair \((B,B^T)\) with \(B\) uniform unrestricted \(n\times n\). Read \(W_1 B X_1\) and \(W_2 B^T X_2\), where \(m_i=\operatorname{rank}W_i\) is full row rank, \(r_i=\operatorname{rank}X_i\), \(U_i=\operatorname{im}X_i\), and \(V_i=\operatorname{im}W_i^T\). Put
\[
 s_1=\dim_K(V_1\cap U_2),\qquad s_2=\dim_K(V_2\cap U_1).
\]
Their joint law is uniform on a space of size \(Q^{m_1r_1+m_2r_2-s_1s_2}\). The joint collision probability is the reciprocal of this size. Choose adapted bases separately on the row space \(V_1+U_2\) and column space \(U_1+V_2\), then extend both to \(K^n\). Independent invertible changes of row and column basis preserve a uniformly random bilinear form. The two rectangular reads of that form have shared entries exactly in the \(s_1\times s_2\) block. The second observation is considered with its transpose when aligning these blocks. Independent unrestricted seeds would remove the equalities on precisely those entries.

Local formulas multiply across independently drawn adjoint orbits, even for an input source correlated across them: condition on the fixed difference first. This is not a claim of two-universality on an entire product ring, where differences can vanish in selected factors.

### A collision-to-uniformity consequence with the seed public

For a standalone random column \(X\in K^n\) independent of \(H\), write \(\operatorname{Col}(X)=\Pr(X=X')\) for an independent copy \(X'\). Reading (1) for the three cases \(X-X'=0\), \(X-X'\in V\setminus\{0\}\), and \(X-X'\notin V\) gives
\[
 \mathbb E_H\chi^2\bigl(\mathcal L(WHX\mid H),U_{K^m}\bigr)
 = (q^{2m}-q)\operatorname{Col}(X)+(q-1)\operatorname{Col}(X\bmod V).
\]
Here \(\chi^2(P,U_{K^m})=q^{2m}\sum_x P(x)^2-1\). If an independent public \(W\) has uniformly random row space \(V=\operatorname{im}W^*\), the expression averaged over \(W\) becomes
\[
 (q^{2m}-1)\operatorname{Col}(X)
 +(q-1)\frac{q^{2m}-1}{q^{2n}-1}\bigl(1-\operatorname{Col}(X)\bigr).
\]
Every fixed nonzero difference lies in the uniform \(V\) with the same probability \((q^{2m}-1)/(q^{2n}-1)\). One-half the square root of either displayed expression bounds the corresponding joint TV with the public seed retained, by Cauchy–Schwarz and Jensen. In particular this can give approximate uniformity without exact perturbation when \(n>m\) and \(\operatorname{Col}(X)\) is small enough. This public-seed bound is distinct from the exact readout-law requirement below.

## 2. Exact randomized repair: minimum seed cardinality

Start from the independent uniform adjoint seeds above. An independent random variable \(S\), uniform on a finite set of size \(N\), selects an **additive** matrix perturbation in every factor, by any deterministic functions of \(S\). These functions may be nonlinear and correlated across the factors. The readout projection matrices \(W\) or \(W_i\) are fixed and known; the perturbation may depend on the projection matrices but **not** on the input. Require that, for every input whose ranks are at most the specified budgets, the joint readout law be exactly the law obtained from independent unrestricted uniform seed matrices. This law is over the original seed and auxiliary seed together, not conditional on either one's value.

For a unitary orbit with row count \(m\) and rank budget \(b_0\), put \(t=\min(m,b_0)\). Its contribution to the required seed cardinality is \(q^{mt}\). For an exchanged pair with output row counts \(m_1,m_2\) and corresponding rank budgets \(b_1,b_2\), put
\[
 t=\min(m_1,m_2,b_1,b_2).
\]
Its contribution is \(Q^{\max(m_1,m_2)t}\). The theorem is that the product of these contributions **divides** every feasible \(N\), and this product itself is feasible. Zero rank budgets are allowed. The proof applies to any finite product of the indicated orbits, including mixed field sizes or characteristics.

### What distribution must the correction have?

On a unitary orbit choose any \(\omega\in K\setminus F\); there is a direct sum over \(F\),
\[
 M_n(K)=\operatorname{Herm}_n(K)\oplus\omega\operatorname{Herm}_n(K).
\]
This holds also in characteristic two, by comparing \(\omega\) and \(\bar\omega\). Absorb the Hermitian part of the perturbation into the independently uniform base seed: the adjusted Hermitian matrix remains uniform and independent of the correction. Fix a basis matrix \(E\) for \(V\). The remaining perturbation has the form \(\omega D\) with \(D\) Hermitian, and only its compressed variable \(D_V=E^*DE\in\operatorname{Herm}_m(K)\) affects the missing coordinates. Every value of \(D_V\) can be lifted: choose \(F_0\) with \(E^*F_0=I\) and use \(D=F_0D_VF_0^*\).

When the shared subspace in section 1 is represented by a full-column-rank \(P\in K^{m\times s}\), the missing quotient of the readout has correction \(\omega P^*D_VP\bmod\operatorname{Herm}_s(K)\). It is naturally identified with \(P^*D_VP\). Every \(s\)-subspace of \(V\) for \(s\le t\) occurs, by choosing \(U\) equal to it. Under the nondegenerate additive trace pairing on Hermitian matrices, the dual frequencies of this restriction are the matrices \(PJP^*\), with \(J\) Hermitian of size \(s\). The trace pairing is nondegenerate: diagonal coordinates pair over \(F\), and each off-diagonal coordinate pairs through the nondegenerate field trace of \(K/F\). Trace to the prime field then gives all additive characters. The union of these frequency spaces over allowed \(P\) is exactly the Hermitian matrices of rank at most \(t\). For the converse, if a Hermitian matrix \(A\) has image in \(\operatorname{im}P\), choose a left inverse \(L\) of \(P\); then \(A=P(LAL^*)P^*\), by the image condition and Hermitian symmetry. This argument works in characteristic two as well.

For an exchanged pair, absorb the first perturbation \(Z_1\) into \(B\). The only remaining value is \(D=Z_2-Z_1^T\) in the second matrix. Compress it to \(D_V=E_2^T D E_1\), where \(E_i\) is a basis matrix of \(V_i\); again compression is onto. The missing shared-block equalities are repaired by the restrictions \(P_2^T D_V P_1\) to subspaces of \(V_1,V_2\). Their dimensions are independently at most \(\min(m_1,b_2)\) and \(\min(m_2,b_1)\). Every such pair of subspaces occurs by choosing \(U_2,U_1\) to be these two spaces. Under the entrywise trace pairing on rectangular matrices the corresponding union of dual frequency spaces is precisely rank at most \(t\) in the \(m_2\times m_1\) matrix space: the two column spaces of a matrix and its transpose determine the two subspaces that contain it.

In both cases a uniform base law on the restricted support, translated by any independent correction, is constant inside each coset of that support. Therefore the fully unrestricted readout law is obtained exactly when the joint correction is uniform in the product of the missing output quotients. Equivalently, writing \(\mu\) for the law of all compressed corrections, its characteristic coefficients must vanish on all nonzero frequencies in the **rank box**
\[
 \mathcal B=\prod_i\{A_i:\operatorname{rank} A_i\le t_i\}. \tag{2}
\]
All tuple frequencies in this box are attainable simultaneously because the input restrictions can be chosen independently in each field orbit. This criterion does not require \(\mu\) to be an additive-subspace law.

### Divisibility, including nonlinear correlated repairs

First restrict to the factors of a common characteristic \(p\). Let \(\mathcal G\) be the additive group of all compressed corrections in these factors and use its trace pairing to identify it with the dual group. Write \(\widehat g(A)=\sum_D g(D)\chi_A(D)\) for unnormalized Fourier transformation. We produce integer functions \(g_i,f_i\) with \(\widehat g_i=c_i f_i\), \(\operatorname{supp} f_i\subseteq\{\operatorname{rank}\le t_i\}\), \(p\nmid f_i(0)\), and
\[
 \frac{|\mathcal G_i|}{|c_i|}=
 \begin{cases}
     q_i^{m_i t_i}, &\text{unitary},\\
     Q_i^{\max(m_{i1},m_{i2})t_i}, &\text{exchanged pair}.
 \end{cases} \tag{3}
\]

For the unitary case, use the negative Gaussian binomial coefficient at parameter \(-q\). It is an integer (evaluate the usual Gaussian-binomial polynomial) and is \(1\bmod p\) when the lower index lies from zero through the upper index. Set \(j=m-t\) and
\[
 g_i(D)=\begin{bmatrix}m-\operatorname{rank}D\\t\end{bmatrix}_{-q},
 \qquad
 f_i(A)=\begin{bmatrix}m-\operatorname{rank}A\\j\end{bmatrix}_{-q}.
\]
The coefficient is zero outside its range. [Schmidt, *Hermitian Rank Distance Codes*, equations (3) and (5)](https://math.uni-paderborn.de/fileadmin-eim/mathematik/AG-Diskrete_Mathematik/Publications-schmidt/hermitian.pdf) give exactly \(\widehat g_i=(-1)^{(m+1)j}q^{mj} f_i\) for this pairing. Since \(|\mathcal G_i|=q^{m^2}\), (3) follows. For a rectangular space, take any coordinate subspace \(L\) of rank at most \(t\) of \(Q\)-dimension \(\max(m_1,m_2)t\): allow only the first \(t\) columns if the number of rows is larger, or only the first \(t\) rows otherwise. Use \(f_i=1_L\), \(g_i=1_{L^\perp}\), and \(c_i=|L^\perp|\), by character orthogonality.

Now tensor these \(g_i,f_i\) to obtain \(\widehat g=c f\) on \(\mathcal G\), \(p\nmid f(0)\). By (2), the convolution \(\mu*g\) has no nonzero Fourier coefficients, so for every \(u\) its value is the constant
\[
 (\mu*g)(u)=\frac{c f(0)}{|\mathcal G|}. \tag{4}
\]
With \(N\) equally likely seed values, \(N(\mu*g)(u)\) is an integer even when the correction repeats some values, because \(g\) is integer-valued. Equations (3) and (4) therefore force the full product of the contributions for this characteristic to divide \(N\). For multiple characteristics, apply the same calculation to each marginal correction law on its characteristic class. Each such marginal is still induced by the same \(N\) equiprobable seeds, and the resulting required divisors are coprime.

### Attainment

For the unitary factor, take \(\mu_i\) uniform on the trace dual of a Hermitian rank-metric code of \(F_q\)-dimension \(m(m-t)\) with nonzero ranks at least \(t+1\). Its size is \(q^{mt}\), and its Fourier coefficients vanish at all required nonzero frequencies. For \(t=m\) take the zero code; for \(t=0\) use the whole Hermitian space. For the intervening cases, [Santonastaso–Zhou, arXiv:2610.26048v1, Theorem 4.1 with extension parameter \(s=2\)](https://arxiv.org/html/2610.26048v1) supplies an \(F_q\)-linear code for every pair, including the parity cases missing from Schmidt's original constructions. Their rank-metric result is taken as an input, not reproved here.

For the rectangular case the analogous code has \(F_Q\)-dimension \(\max(m_1,m_2)(\min(m_1,m_2)-t)\). For completeness, after transposing if necessary let the array be \(a\times b\) with \(a\ge b\). View it as a map from a fixed \(b\)-subspace of \(\mathbb F_{Q^a}\) into that field, and take restrictions of \(x\mapsto\sum_{i=0}^{b-t-1} c_i x^{Q^i}\) for coefficients in \(\mathbb F_{Q^a}\). A nonzero polynomial has kernel dimension at most \(b-t-1\) by its ordinary degree, so the coefficient map is injective and nonzero maps have rank at least \(t+1\); the empty sum case is the zero code. The uniform trace dual thus has exactly the required size. Take all these local dual-code corrections independently and lift the compressions. The resulting total seed size is exactly the product. This is a construction of a uniform positive sampling guarantee, not a rank-metric decoding procedure.

## 3. Biased seeds are a different resource

If every unitary budget \(t\) is even, then the \(g_i\) above are nonnegative: the sign of a negative Gaussian coefficient \(\bigl[\begin{smallmatrix}u\\t\end{smallmatrix}\bigr]_{-q}\) is \((-1)^{t(u-t)}\). The \(c_i\) are then positive, and \(g_i(0)=f_i(0)\) by binomial symmetry. Rectangular functions are nonnegative automatically. Applying the tensor identity (4) across all factors, without an equiprobability assumption, gives
\[
 \mu(u)g(0)\le(\mu*g)(u),\qquad
 \max_u\mu(u)\le \prod_i |c_i|/|\mathcal G_i|.
\]
Thus in this parity range the same lower bound on seed **min-entropy** holds for arbitrary biased distributions.

It need not hold for odd budgets. For one unitary factor and \(t=1\), the largest feasible atom of the compressed correction is exactly
\[
 \alpha=\frac{1+q^{1-2m}}{q+1}.
\]
To prove the bound it suffices by translation to bound the atom at zero. The constraint is that \(x^*Dx\) be uniform in \(F_q\) for every \(x\ne0\). With a separately uniform \(x\in K^m\), the zero probability is therefore \(1/q+(1-1/q)q^{-2m}\). Conditional on any fixed nonzero \(D\) of rank \(s\), diagonalize the Hermitian form by congruence and normalize its nonzero coefficients via the norm map. A nontrivial additive character applied to one independent norm has expectation \(-1/q\), since every nonzero norm has \(q+1\) preimages. Thus the zero probability is \(1/q+(1-1/q)(-1/q)^s\ge q^{-2}\). Combining this with the conditional probability one at \(D=0\) gives the stated upper bound. For attainment, put mass \(\alpha\) at zero and otherwise use \(D=vv^*\) with \(v\) uniform in \(K^m\setminus\{0\}\). For each fixed nonzero \(x\), every nonzero value of \(x^*Dx=\operatorname{Norm}(x^*v)\) in this branch has probability \((q+1)q^{2(m-1)}/(q^{2m}-1)\). Mixing makes every nonzero value have probability \(1/q\), hence the zero value as well. This biased construction does not contradict the equiprobable-seed divisibility theorem.

## 4. Scope and prior results

Finite-field uniform rank laws are classical for full rectangular and full Hermitian matrices; see [Fulman–Goldstein, §§1 and 7](https://arxiv.org/abs/1211.0504). The shared-corner counting statement here allows two arbitrary projected subspaces, or two exchanged-factor readouts. [Boudgoust–Lapiha, *Leftover Hash Lemma(s) Over Cyclotomic Rings*, §§3–4](https://opencryptology.org/2025/1080/versions/20260428T172000Z.pdf) analyze ring-linear hashing for different seed distributions and support conditions; the exact positive replacement considered here does not alter their results. The Fourier identity and code existence used above are from the cited rank-metric literature. The distinct claims in this note are the projected readout laws, the repair equivalence (2), and the exact joint probability-law and seed-cardinality results from applying the Fourier identity to the correction measure rather than to an additive code's inner distribution. No claim of literature priority is made beyond these scoped comparisons.

The seed-size result is for independence of the original seed and the auxiliary perturbation, exact matching on all specified ranks, and an additive change to the matrix. It does not bound a general new sampler, approximate matching, or an implementation. The attached checker uses only small generated finite probability spaces.
