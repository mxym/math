# All-copy quantum channel contraction from a second moment

## 1. Model and statement

Let \(d\ge2\). A quantum channel here is a complex-linear completely positive trace-preserving (CPTP) map on \(M_d(\mathbb C)\). Let \(\Lambda\) be a random channel, and use independent samples when composing channels at different times. Copies at a single time share the same sample. For an integer \(r\ge1\) define
\[
              T_r=\mathbb E\,\Lambda^{\otimes r}.
\]
An ensemble may be finite, discrete or Borel; all expectations below are finite-dimensional matrix integrals. Each \(T_r\) is CPTP. View its characteristic roots with algebraic multiplicity, and remove one occurrence of the fixed root \(1\). Denote the largest modulus of the remaining roots by \(s_r\).

Let \(V\) be the complex trace-zero subspace of \(M_d\), with Hilbert–Schmidt inner product, of dimension \(D=d^2-1\). Let \(A=\Lambda|_V\), and \(S_k=\mathbb E A^{\otimes k}\) for \(k\ge1\). We use an orthonormal Hermitian basis for \(V\), so the coordinate matrices of each \(A\) are real (their actions still extend complex-linearly). The spectral radius of a matrix is denoted by \(\rho\).

**Theorem 1 (all-copy transfer).** For every such ensemble,
\[
 s_1=\rho(S_1),\qquad
 s_r=\max\{\rho(S_1),\rho(S_2)\}\quad\text{for }r\ge2 .
\]
Moreover, \(\rho(S_1)^2\le\rho(S_2)\). Thus \(T_2\) has exactly one characteristic root on the unit circle iff every \(T_r\), \(r\ge2\), has exactly one. Equivalently, the latter happens iff \(\rho(S_2)<1\). Its exact mean-square rate is \(\lim_{m\to\infty}(\mathbb E\|P_m\|_F^2)^{1/m}=\rho(S_2)\), with \(P_m\) defined below.

## 2. Uniform path bound and comparison of moments

In the basis consisting of \(e_0=I/\sqrt d\) followed by the Hermitian basis of \(V\), a channel has the form
\[
                 \begin{pmatrix}1&0\\ t&A\end{pmatrix}.
\]
The trace on \(V\) is zero and remains zero by trace preservation. Consequently the tensor-product block indexed by positions of traceless factors may only map into blocks with a superset of those positions. In any ordering extending this inclusion relation the full \(r\)-copy matrix is block triangular. On a subset of size \(k\ge1\) the diagonal block is \(S_k\), since the scalar-to-scalar entry is \(1\). The empty subset contributes a scalar \(1\). The characteristic polynomial is therefore
\[
  (z-1)\prod_{k=1}^r \det(zI-S_k)^{\binom rk}.
\]
No unitality assumption removes the off-diagonal blocks; they are simply irrelevant to the characteristic polynomial.

Write \(P_m=A_m\cdots A_1\) for \(m\) independent samples of the trace-zero block. Then \(P_m\) represents the trace-zero restriction of the composed channel \(\Psi_m=\Lambda_m\circ\cdots\circ\Lambda_1\). For every matrix \(X\), not only Hermitian matrices, a CPTP channel satisfies \(\|\Psi_m(X)\|_1\le\|X\|_1\). Indeed its adjoint is unital CP; the inequality \(L(Y)^\dagger L(Y)\le L(Y^\dagger Y)\) for a unital CP map \(L\) follows by applying its two-by-two amplification to the positive block matrix with entries \(Y^\dagger Y,Y^\dagger,Y,I\) and taking the Schur complement. Positivity and unitality give \(\|L(Y^\dagger Y)\|_\infty\le\|Y\|_\infty^2\), and duality proves the trace-norm bound. Thus, uniformly over every path and every \(m\),
\[
           \|P_m\|_{2\to2}\le\sqrt d ,
\]
by \(\|X\|_2\le\|X\|_1\le\sqrt d\,\|X\|_2\).

Tensor multiplicativity and independence give \(S_k^m=\mathbb E P_m^{\otimes k}\). Put \(\Omega=\sum_{j=1}^D e_j\otimes e_j\) in the real coordinate basis of \(V\). For any real matrix \(P\),
\(\langle\Omega,(P\otimes P)\Omega\rangle=\sum_{i,j}P_{ij}^2=\|P\|_F^2\).
It follows that
\[
  \mathbb E\|P_m\|_F^2=\langle\Omega,S_2^m\Omega\rangle
                      \le D\|S_2^m\|_{2\to2}.                 \tag{1}
\]
The reverse bound \(\|S_2^m\|_{2\to2}\le\mathbb E\|P_m\|_F^2\) follows from \(\|P_m\otimes P_m\|_{2\to2}\le\|P_m\|_F^2\). Thus (1) and Gelfand's formula give the mean-square rate. Using \(\|P^{\otimes k}\|_{2\to2}=\|P\|_{2\to2}^k\), for \(k\ge2\) we obtain
\[
  \|S_k^m\|_{2\to2}\le
       d^{(k-2)/2}\mathbb E\|P_m\|_F^2
       \le D\,d^{(k-2)/2}\|S_2^m\|_{2\to2}.
\]
For \(k=1\), Cauchy–Schwarz gives
\(\|S_1^m\|_{2\to2}^2\le\mathbb E\|P_m\|_F^2\le D\|S_2^m\|_{2\to2}\).
Gelfand's spectral-radius formula and the tensor block factorization now prove Theorem 1. This is a bounded-product application of the familiar second-moment transfer from random matrix product theory; the bound on products comes from complete positivity and trace preservation, not Hilbert–Schmidt contraction of individual single-copy blocks.

## 3. Exact 2-designs: the radius equals \(\max\{|\alpha|,u\}\)

**Theorem 2.** Fix a channel \(\Phi\) on \(M_d\), and use the distribution
\(\Lambda_U=\operatorname{Ad}_{U}^{-1}\circ\Phi\circ\operatorname{Ad}_{U}\)
where \(U\) is drawn from an exact unitary 2-design probability measure. (For a finite uniform subgroup one can equivalently invert the indexing unitaries.) If \(A_0=\Phi|_V\), put
\[
       \alpha=\frac{\operatorname{Tr} A_0}{D},\qquad
       u=\frac{\|A_0\|_F^2}{D}.
\]
Then \(s_1=|\alpha|\) and \(s_r=\max\{|\alpha|,u\}\) for every \(r\ge2\). For \(r\ge2\), \(s_r<1\) iff \(\Phi\) is nonunitary.

In fact if \(R_U=\operatorname{Ad}_U|_V\), then \(A_U=R_U^\dagger A_0 R_U\). The entries of \(R_U^\dagger X R_U\), for any fixed endomorphism \(X\) of \(V\), have bidegree \((2,2)\) in \(U,\bar U\). An exact unitary 2-design matches this moment of Haar measure. The Haar average commutes with every \(R_V\), and is scalar by irreducibility on the trace-zero matrices. An elementary irreducibility check is as follows. An endomorphism commuting with all diagonal phases is diagonal on each off-diagonal matrix-unit line, since all its nontrivial characters there are different. Permutation matrices force its scalar on these lines to be common. Conjugating \(E_{ij}+E_{ji}\) by a Hadamard rotation in the \(i,j\) coordinates yields \(E_{ii}-E_{jj}\); commutation then forces that same scalar on the whole traceless diagonal subspace. Hence the average is \((\operatorname{Tr}X/D)I\).

Applying this to \(X=A_0,A_0^\dagger A_0,A_0 A_0^\dagger\) gives
\[
 S_1=\alpha I,\qquad
 \mathbb E A_U^\dagger A_U=\mathbb E A_U A_U^\dagger=u I.      \tag{2}
\]
These are the only design identities used for the spectrum. The separate first-order identity \(\mathbb E R_U=0\) (the Haar mean on trace-zero matrices, matched by a 1-design) averages the nonunital translation to zero, so \(\alpha\) is indeed the parameter of the one-copy depolarizing channel. The law of \(A_U^{\otimes k}\), \(k\ge3\), need not agree with Haar.

Conditioning on the previous matrices in \(P_m=A_m\cdots A_1\) and using (2) gives
\(\mathbb E\|P_m\|_F^2=u\,\mathbb E\|P_{m-1}\|_F^2=D u^m\).
The proof of Theorem 1 then gives \(\rho(S_2)\le u\). Conversely
\((A_U\otimes A_U)\Omega=\operatorname{vec}(A_U A_U^{\mathsf T})\);
the Hermitian basis makes \(A_U^{\mathsf T}=A_U^\dagger\), so (2) gives the eigenvector \(S_2\Omega=u\Omega\). Thus \(\rho(S_2)=u\), proving the radius formulas.

Finally, with normalized Choi state \(J_\Phi=d^{-1}\sum_{i,j}\Phi(E_{ij})\otimes E_{ij}\), one has
\[
       d^2\operatorname{Tr}J_\Phi^2=\|\Phi\|_F^2
                  =1+\|t\|_2^2+D u \le d^2.
\]
The first equality is the block reshuffling identity, or follows by using the orthonormal matrix units in the Choi expansion. The second is the trace-adapted block form. The inequality holds because \(J_\Phi\) is a state. If \(u=1\), equality forces \(J_\Phi\) pure, hence a single Kraus operator; trace preservation in the square dimension makes it unitary. Conversely unitary conjugation preserves the Hilbert–Schmidt norm and gives \(u=1\). Since \(|\alpha|\le\sqrt u\) by Cauchy–Schwarz, the desired equivalence for \(r\ge2\) follows. For \(r=1\) only the scalar \(\alpha\) determines contraction, and the converse for \(r\ge2\) is not asserted there.

## 4. Quantitative mixing in diamond norm

Let \(\nu_m=\mathbb E\|P_m\|_F^2=\langle\Omega,S_2^m\Omega\rangle\). If \(\rho(S_2)<1\), each \(T_r\) has a unique stationary density matrix \(\sigma_r\): Cesàro averages of iterates give a stationary state by compactness, and the simple eigenvalue \(1\) gives uniqueness. Write \(R_\tau(X)=\operatorname{Tr}(X)\tau\) for the replacement map. Then, for every \(r\ge1\) and \(m\ge1\),
\[
 \|T_r^m-R_{\sigma_r}\|_\diamond\le
            \min\{2,\ 2rd\sqrt{\nu_m}\}.                      \tag{3}
\]
In the exact-design case the second term is \(2rd\sqrt D\,u^{m/2}\).

To see this, fix one path \(\Psi_m\), let \(\varrho=\Psi_m(I/d)\) and \(\Delta=\Psi_m-R_\varrho\). In the trace-adapted basis \(\Delta\) has all entries zero except the lower-right block \(P_m\). Thus \(\|\Delta\|_{2\to2}=\|P_m\|_{2\to2}\). For a map on \(M_d\), \(\|\Delta\|_\diamond\le d\|\Delta\|_{2\to2}\): an ancilla of dimension \(d\) suffices, and on the joint space \(\|Y\|_1\le d\|Y\|_2\), with \(\|\Delta\otimes\operatorname{id}\|_{2\to2}=\|\Delta\|_{2\to2}\). For the ancilla reduction, decompose any trace-norm input by singular values into rank-one \(|a\rangle\langle b|\) terms. Each vector has Schmidt rank at most \(d\) across the system–ancilla cut. Compress the left and right sides into their two respective at-most-\(d\)-dimensional ancilla subspaces. Multiplying the result on the two sides by the corresponding ancilla isometries preserves trace norm and does not change \(\Delta\)'s system action.

Both \(\Psi_m\) and \(R_\varrho\) are channels, so their tensor products have diamond norm \(1\) (apply trace-norm contraction to each amplification, and use a unit-trace positive test for equality). The telescoping expansion of the difference of tensor powers gives
\(\|\Psi_m^{\otimes r}-R_{\varrho^{\otimes r}}\|_\diamond
 \le r\|\Delta\|_\diamond\):
in each term the other factors are channels and tensoring with a channel cannot increase the stabilized norm, by composing with its amplification. Average over the paths. Their first maps average to \(T_r^m\), while their replacement states average to
\(\tau_m=T_r^m((I/d)^{\otimes r})\).
The triangle and Cauchy–Schwarz inequalities give
\(\|T_r^m-R_{\tau_m}\|_\diamond\le rd\sqrt{\nu_m}\).
Applying this difference to \(\sigma_r\) gives
\(\|\sigma_r-\tau_m\|_1\le rd\sqrt{\nu_m}\), because \(\sigma_r\) is stationary. The diamond norm of the difference of two replacement channels equals the trace distance without the factor \(1/2\) of their output matrices: by partial trace contraction and trace-norm tensor multiplicativity it is at most the output trace norm, and a state input attains equality. Taking a triangle inequality proves (3); the bound \(2\) is immediate for two channels.

For fixed \(r\), the asymptotic \(m\)-th root of this diamond distance is exactly \(s_r\): \(T_r^m-R_{\sigma_r}=(T_r-R_{\sigma_r})^m\) since both products with the replacement are the replacement, and the latter map replaces the simple eigenvalue \(1\) by \(0\) and leaves the rest unchanged. Apply Gelfand's formula and finite-dimensional norm equivalence. This exact exponent is separate from the simple linear-in-\(r\) finite-time prefactor in (3).

## 5. Covariance tolerance and limits of the model

An arbitrary iid ensemble, without any design assumption, has an elementary sufficient condition
\[
                \beta=\|\mathbb E A^\dagger A\|_{2\to2}<1 .
\]
The same recursion gives \(\nu_m\le D\beta^m\), and bounding \(S_2^m=\mathbb E P_m^{\otimes 2}\) directly by \(\nu_m\) gives \(\rho(S_2)\le\beta\). Formula (3) holds with \(u\) replaced by \(\beta\) in its displayed specialization. For conjugation of a fixed channel, a deviation
\(\|\mathbb E R_U^\dagger A_0^\dagger A_0 R_U-uI\|_{2\to2}\le\eta<1-u\)
therefore suffices; this is a precisely specified covariance tolerance, not a claim about every convention for an approximate design.

The covariance bound is sufficient, not necessary. For example the deterministic qutrit channel that measures the computational basis and sends basis labels \(0,1,2\) to \(0,0,1\) squares to a replacement; its trace-zero Hilbert–Schmidt norm squared is at least \(4/3\), since it sends \(\operatorname{diag}(1,1,-2)\) to \(\operatorname{diag}(2,-2,0)\). It therefore has \(\beta>1\) despite mixing in two steps.

A 1-design alone does not suffice: for qubit dephasing, conjugating by the Pauli 1-design leaves the channel unchanged, with a nontrivial eigenvalue \(1\) on the traceless diagonal direction. The 2-design theorem also requires independent sampling across composition times. For a qubit dephasing channel and one uniformly sampled Clifford kept fixed across times, each conjugated channel is idempotent; averaging their powers consequently does not give decay in the number of steps. This model is not the iid product here. Likewise the covariance test for a sampled channel family does not by itself assert anything about correlated or inversion-constrained experimental benchmarking.
