# Analytic guessing bound and infinite-dimensional validity

## 1. Model and statement

Write \(\rho^x\), \(x=0,1\), for normal density operators on
\(\mathcal H_S\otimes\mathcal H_M\otimes\mathcal H_E\).
Here \(S\) is the message, \(M\) is Bob's pre-existing memory, and \(E\)
is Eve's quantum side information. The input is independent of the
initial shared state. The input-dependent preparation is a local
trace-preserving quantum channel, so
\[
 \operatorname{Tr}_S\rho^0=\operatorname{Tr}_S\rho^1.
\]
The vacuum is a fixed unit vector \(|0\rangle\) on \(S\).
The input-wise non-vacuum probabilities are at most \(w_0,w_1\):
\[
 \operatorname{Tr}[(I-|0\rangle\langle0|)_S\,\rho^x_S]\le w_x.
\]
The binary POVM of Bob acts on \(SM\), and Eve's guessing POVM for the
generation input \(x=0\) acts on \(E\) only. These are the assumptions in
Ranu–Wooltorton–Abbott–Fawzi (RWAF), §§II–III, Eqs. (1),(4)–(6).
The proof only uses the displayed common marginal and vacuum budgets.

Let \(n_x=\Pr[b=0\mid x]\), \(E_x=2n_x-1\), and
\(D=|n_0-n_1|=I_{\rm corr}/2\). Write
\(e=1-p_{\rm guess}(B|E,x=0)\).
For \(w_0=w_1=w\) and \(0\le w<1/3\), put
\[
 F=\frac{w(5-9w)}{1-w},\qquad
 C_*=\frac{2(2-w)(1-3w)}{(1-w)^2},\qquad
 c=\frac{4w^2}{(1-w)^2}.
\]
Then \(D\le F+C_*\sqrt e+(1-c)e\).

Equivalently, when \(\Delta=(D-F)_+>0\),
\[
 e\ge \eta:=\left(\frac{2\Delta}{C_*+\sqrt{C_*^2+4(1-c)\Delta}}\right)^2,
 \qquad H_{\min}(B|E,x=0)\ge-\log_2(1-\eta).
\]
For \(\Delta=0\) the lower bound is zero. For feasible data \(e\le1/2\)
and therefore \(\eta\le 1/2\). There is no claim of optimality.
For a binary cq state with subnormalised outcome states \(\sigma_b\)
on \(E\), the dual to guessing has an explicit feasible trace-class
majorant \(Y=(\sigma_0+\sigma_1+|\sigma_0-\sigma_1|)/2\) of both
\(\sigma_b\). The positive spectral projector of
\(\sigma_0-\sigma_1\) attains the upper bound \(\operatorname{Tr}Y\).
This yields the stated min-entropy/guessing identity directly, in both
finite and infinite dimension, with the usual trace-majorant
definition of conditional min-entropy.

## 2. Two-projection inequalities

Naimark-dilate Bob's binary POVM with an initially pure qubit appended
to \(M\), so the effect \(N\) for \(b=0\) is a projection.
A concrete dilation of an effect \(G\) is the block projection
\(\begin{psmallmatrix}G&\sqrt{G(I-G)}\\
\sqrt{G(I-G)}&I-G\end{psmallmatrix}\) with ancillary input the first
basis state. Appending the qubit preserves the shared marginal and the
energy bounds; the block construction works for bounded effects in
any Hilbert dimension. Write
\(P=|0\rangle\langle0|\otimes I_M\), \(Q=I_{SM}-P\), and \(R=I_{SM}-N\).
On \(P\mathcal H_{SM}\oplus Q\mathcal H_{SM}\), write
\[
 R=\begin{pmatrix} A&B^\dagger\\ B&T\end{pmatrix}.
\]
Thus \(0\le A,T\le I\), \(B^\dagger B=A(I-A)\) and \(TB=B(I-A)\).
The ground block acts on the canonically identified space
\(P\mathcal H_{SM}\cong\mathcal H_M\).

Fix a number \(\lambda>1\) and define \(f(a)=\lambda a/(\lambda-1+a)\)
on \([0,1]\). Since \(\lambda-T\) is boundedly invertible, the Schur
complement of \(\lambda Q+P f(A)P-R\) vanishes on \(P\mathcal H_{SM}\):
\[
 f(A)=A+B^\dagger(\lambda-T)^{-1}B
      =A+\frac{A(I-A)}{\lambda-1+A}.
\]
In particular \(R\le\lambda Q+P f(A)P\). Fix \(t_*\ge0\) and put
\[
 h(t)=\frac{\lambda t}{\lambda-1+\lambda t},\quad
 b_*=h'(t_*),\quad c=h(t_*)-t_*h'(t_*)=h(t_*)^2,\quad
 J=(f(A)-cI)_+,\quad K=b_*+1-c.
\]
Here \(0\le c<1\). The concave increasing function \(h\) has tangent
\(c+b_*t\) at \(t_*\); hence
\(0\le(f(a)-c)_+\le b_*a/(1-a)\) for \(a<1\), and \(J\le(1-c)I\).
Set \(\widehat J=I_S\otimes J\), the lift of the ground-block operator.

First, for any positive trace-class \(Y\) on \(SM\) of trace \(q\),
non-vacuum weight \(s=\operatorname{Tr}(QY)\), and marginal \(\mu_Y\),
\[
 \operatorname{Tr}(RY)\le c q+(\lambda-c)s+\operatorname{Tr}(J\mu_Y).
 \tag{A}
\]
Indeed \(f(A)\le cI+J\), and
\(\operatorname{Tr}[PJP\,Y]\le\operatorname{Tr}(\widehat JY)\)
because \(\widehat J\) commutes with \(P\) and is positive.

Second, \(L=\widehat J-KQ\) satisfies \(N L N\le0\) and
\(-KI\le L\le(1-c)I\).
For the compression claim, take \(v=Nv\). As an operator from
\(\mathcal H_{SM}\) to \(P\mathcal H_{SM}\),
\((I-A+\delta I)^{-1/2}PN\) is a contraction for every \(\delta>0\):
its product with its adjoint is
\((I-A)/(I-A+\delta I)\le I\). Thus
\[
 \langle Pv,(I-A+\delta I)^{-1}Pv\rangle\le\|v\|^2.
\]
Monotone convergence of the scalar spectral integral at
\(\delta\downarrow0\) shows that \(Pv\) has no mass at \(a=1\), and
that its integral of \(a/(1-a)\) is at most \(\|Qv\|^2\) after
subtracting \(\|Pv\|^2\). The tangent bound yields the ground
contribution \(\langle Pv,J Pv\rangle\le b_*\|Qv\|^2\).
The excited contribution of \(\widehat J\) is at most
\((1-c)\|Qv\|^2\), so \(N L N\le0\).
The two-sided bounds on \(L\) follow from \(0\le\widehat J\le(1-c)I\).

Consequently, for any positive trace-class \(X\) of trace \(q\), put
\(e_0=\operatorname{Tr}(RX)\). Splitting \(X\) on \(N+R\) gives
\[
 \operatorname{Tr}(LX)\le (1-c)e_0
       +(K+1-c)\sqrt{(q-e_0)e_0}.
 \tag{B}
\]
The \(N\) diagonal term is nonpositive and the \(R\) diagonal term
is at most \((1-c)e_0\). Subtract the midpoint of the operator
interval \([-K,1-c]\) from \(L\) to bound
\(\|NLR\|\le(K+1-c)/2\). The trace of each off-diagonal term is
bounded by \(\|NLR\|\sqrt{\operatorname{Tr}(NX)\operatorname{Tr}(RX)}\),
by factoring \(X=\sqrt X\sqrt X\) and using Hilbert–Schmidt
Cauchy–Schwarz. These steps use bounded functional calculus and
trace-class states, not finite-dimensional spectral decompositions.

## 3. Eve conditioning and the explicit parameters

Relabel Bob's two outcomes, and Eve's guesses accordingly, so that
\(D=n_0-n_1\ge0\). For any binary guessing POVM \(\{Z_g\}\) on \(E\),
apply it hypothetically to both input states. Write \(X_g,Y_g\) for
the two subnormalised \(SM\) states conditioned on \(g\) for inputs
zero and one, using the operations \(\sqrt{Z_g}\) and tracing out \(E\).
The two states in each branch have the same \(M\) marginal, since
\(\operatorname{Tr}_S\rho^0=\operatorname{Tr}_S\rho^1\);
call it \(\mu_g\), with trace \(q_g\). Moreover \(q_0+q_1=1\).
The error for this particular Eve POVM is
\(e_{\rm povm}=e_0+e_1\), where
\(e_0=\operatorname{Tr}(RX_0)\) and \(e_1=\operatorname{Tr}(NX_1)\).
The sums of the non-vacuum weights over \(g\) are at most the
input-wise bounds \(w_0,w_1\), without any branchwise energy assumption.

The difference in branch zero is \(\operatorname{Tr}(RY_0)-e_0\),
and in branch one it is at most \(e_1\) by positivity. Applying (A)
to \(Y_0\) and (B) to \(X_0\), with
\(\operatorname{Tr}(J\mu_0)=\operatorname{Tr}(\widehat J X_0)\),
yields
\[
 D\le c q_0+K w_0+(\lambda-c)w_1-ce_0+e_1
         +(K+1-c)\sqrt{(q_0-e_0)e_0}.
\]
As \(q_1\ge e_1\), \(cq_0+e_1\le c+(1-c)e_1\); also \(q_0-e_0\le1\).
Taking an optimal Eve POVM (or passing to the guessing supremum)
proves the asymmetric bound
\[
 D\le c+K w_0+(\lambda-c)w_1
         +(K+1-c)\sqrt e+(1-c)e.
 \tag{C}
\]
Use \(\lambda=2(1-2w)/(1-w)>1\) and \(t_*=w/(1-2w)\).
Then \(\lambda-1+\lambda t_*=1\),
\(c=(2w/(1-w))^2\), \(b_*=\lambda(\lambda-1)\).
Substitution gives
\(c+(K+\lambda-c)w=F\) and \(K+1-c=C_*\), as claimed.

The source's ideal value \(I_{\rm corr}=4\sqrt{w(1-w)}\) (Eq. (3))
is attainable by the product preparations
\(\sqrt{1-w}|0\rangle\pm\sqrt w|1\rangle\) and measurement in the
\(\{|0\rangle\pm|1\rangle\}/\sqrt2\) basis.
For \(0<w<1/5\) it gives \(D=2\sqrt{w(1-w)}>F\):
\[
 4w(1-w)-F^2=\frac{w(1-5w)(17w^2-17w+4)}{(1-w)^2}>0.
\]
The last quadratic is decreasing on \([0,1/5]\) and is \(32/25\)
at \(1/5\). Also \(F\ge0\) there. This strictly positive gap survives
a small decrease of \(I_{\rm corr}\). At \(w=0\) the ideal
correlator is zero; at \(w=1/5\) this particular perfect-guess
threshold equals the ideal value. Neither endpoint is asserted to
certify positive entropy by this argument.

## 4. Extension of the RWAF moment relaxation

The following is independent of the analytic inequality. For normal
states in the tensor-product model, the dimension-independent
relaxations of RWAF Eq. (13), Appendix A, at any moment level at
which the objective is represented, remain valid with arbitrary
Hilbert dimensions. In particular their upper bounds on the
physical guessing probability extend to normal infinite-dimensional
tensor-product strategies.

Use the binary dilation in §2 for Bob, and a projective optimal Eve
measurement by the binary trace-majorant argument in §1.
Alternatively dilate an arbitrary Eve POVM locally with a pure
qubit as well. This suffices for comparing to the guessing supremum.
If \(S\) is one-dimensional, embed it isometrically in a
two-dimensional \(S\) preserving the vacuum. Extend Bob's projection
by zero on the orthogonal complement if necessary. Choose any unit
\(|1\rangle\perp|0\rangle\) in \(S\), and write
\(P_{\rm s}=|0\rangle\langle0|\), \(Q_{\rm s}=|1\rangle\langle1|\),
\(T_{\rm s}=|0\rangle\langle1|\). In this paragraph only, these are
the source paper's \(P,Q,T\), not the \(P,Q,T\) of §2.
Let \(V_i m=|i\rangle\otimes m\) (\(i=0,1\)).
The source's \(A,B,C\) are respectively
\(V_0^\dagger N V_0,V_0^\dagger N V_1,V_1^\dagger N V_1\).
Set its auxiliary operator
\[
 F_{\rm aux}=N-(P_{\rm s}+Q_{\rm s})N(P_{\rm s}+Q_{\rm s}),
\]
with identity factors implicit. This bounded expression uses no
infinite block sum.

The \(2\times2\) retained block is exactly
\(P_{\rm s}A+T_{\rm s}B+T_{\rm s}^\dagger B^\dagger+Q_{\rm s}C\).
Its complement \(F_{\rm aux}\) is self-adjoint with zero retained
block, so \(O_1 F_{\rm aux} O_2=0\) for any retained matrix units.
The other operator conditions in Eq. (13) follow from the projection
identities, retained matrix-unit multiplication, block compression of
a positive contraction, and tensor-factor commutation. All moments
in \(\{A,B,B^\dagger,C,Z\}^{\le 2\ell}\) have equal expectations for
the two preparations, since they act on \(ME\) only. All positivity
and localizing constraints hold: a linear combination of word
vectors gives an expectation of \(U^\dagger U\), or
\(U^\dagger O_+ U\) for an operator \(O_+\ge0\).
The observed-statistic and energy constraints are those of the
physical strategy (relabel both outcomes if needed to use the signed
correlator in Eq. (13), as in §3). Finally, the objective is the physical success
probability since \(NZ+(I-N)(I-Z)=I-N-Z+2NZ\).
Thus every such physical strategy maps to a feasible SDP point,
with the same statistics and objective, even at a fixed threshold
and without taking any closure of the SDP. This is relaxation
soundness, not convergence or exactness of an infinite hierarchy.
It uses neither a general commuting-operator model nor singular
states. A positive spectral gap of a calibrated Hamiltonian implies
the vacuum assumption if its mean energy above the ground is
bounded by the gap times \(w\); no truncation of the Hamiltonian is
needed to apply the vacuum-based theorems.

### Optional finite-dimensional approximation of the model

For completeness, the finite and normal models have the same closure
of their finite transcript probability vectors at any fixed vacuum
budgets, including fixed exact vacuum populations. This is a
statement about closure, not about finite realization at a given
correlator. For each subsystem choose finite-dimensional local
projections increasing strongly to identity in the separable case.
For a finite list of normal states in an arbitrary Hilbert space one
can instead use the directed family of all finite-rank projections.
On \(S\) include both the vacuum and a fixed excited vector in every
projection (or take the trivial \(S\) case directly). Apply the local
trace-preserving compression-and-replacement channel
\[
 \Phi_J(X)=JXJ+\operatorname{Tr}[(I-J)X]\;|u\rangle\langle u|,
 \qquad u\in\operatorname{ran}J,\quad \|u\|=1.
\]
Choose \(u\) excited on \(S\); elsewhere it is arbitrary. The dual on
\(S\) fixes the vacuum projector exactly. Product local channels
preserve the equality of the two \(ME\) marginals: the new common
marginal is precisely \((\Phi_M\otimes\Phi_E)(\mu_{ME})\).
The product action has a main term \(J_{\rm tot}\rho J_{\rm tot}\)
and positive replacement terms with trace
\(1-\operatorname{Tr}(J_{\rm tot}\rho)\). The trace norm of
\(J_{\rm tot}\rho J_{\rm tot}-\rho\) tends to zero (first prove it
on finite-rank operators, then use trace-norm density).
Compress the original effects to the local finite-dimensional ranges.
They form valid POVMs and all joint transcript probabilities converge.
The same holds for the optimised Eve success probability: the
unnormalised cq blocks converge in trace norm and the explicit
binary trace formula is continuous.

These finite output state pairs are physically preparable: purify
their common \(ME\) marginal in a finite-dimensional preparation
memory, purify each output state, and use the elementary Schmidt
isometry between purifications of the common marginal. Trace out the
extra purifying system after that input-dependent isometry. This is a
finite local channel on the preparation memory; it leaves \(ME\)
unchanged. No compression of Eve's dimension invalidates the
shared marginal constraint.

## 5. What the checks verify

The scalar check substitutes exact rational polynomial identities,
checks the tangency identity and evaluates two rational feasible
certification thresholds. The matrix check independently builds
finite rational models (including both Eve outcomes), checks exact
block positivity and operator identities, and checks the claimed
bound using rational arithmetic and exact comparisons of square
roots. The matrix tests are regression checks; the operator proof
establishes the dimension-unrestricted statements.
