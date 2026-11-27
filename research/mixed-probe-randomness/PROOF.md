# Mixed-probe min-entropy with an independent untrusted detector

Throughout, \(\|\cdot\|_1\) is the trace norm, \(D(\rho,\sigma)=
\|\rho-\sigma\|_1/2\) is trace distance, and fidelity is the *root*
fidelity \(F(\rho,\sigma)=\|\sqrt{\rho}\sqrt{\sigma}\|_1\).
Logs are base two.

## 1. Model

The trusted finite-dimensional signal system \(S\) is prepared in a known
density matrix \(\rho_x\) for test label \(x\). The generation label
is \(x=0\), with \(\rho=\rho_0\). Before the measurement, the joint
marginal of \(S\) and the detector memory \(D\) is \(\rho_x\otimes\tau\)
for a single, unknown \(\tau\) independent of \(x\). The detector
performs the same unknown binary POVM \(N_+, N_-=I-N_+\) on \(SD\),
receiving no label or other source system. Its residual quantum system
and the output are not transmitted to Eve. Eve may know the label and
hold *any* extension of the joint marginal, including its full
purification and a joint measurement across the source-reference and
detector-reference registers. Equality of the product marginal is
all that is assumed about the extension; it need not be given in
product form. Tensor-product quantum models with normal density
operators are intended, not general commuting-operator models.

Write \(M\) for the effect on \(S\) determined by
\[
 \operatorname{Tr}\sigma M
 =\operatorname{Tr}[(\sigma\otimes\tau)N_+]
\]
for all signal densities \(\sigma\). Then \(0\le M\le I\) and
\(p(+|x)=\operatorname{Tr}\rho_x M\). For a bipartite instrument local
to \(SD\), the unnormalized conditional states on Eve depend only on
the detector effects: insert a Kraus decomposition and use cyclicity
of the partial trace for operators acting on the discarded \(SD\).
Thus no generality is lost by ignoring the postmeasurement detector
state. Allowing Eve the full purification can only increase her
single-round optimal guessing probability, since any other extension
is obtained from the reference of a purification by a local channel
(for example, by purifying the extension and applying Schmidt
isometry, then tracing the extra registers).

## 2. A universal binary commutator bound

**Theorem 1.** In the above model,
\[
 P_{\rm g}(B|E,x=0)\ \le\
 G(c):=\frac{1+\sqrt{1-c^2}}2,\qquad c=\|[\rho,M]\|_1 .
 \tag{1}
\]
The bound is independent of the dimensions of \(D\) and \(E\), and
holds for singular signal and detector states.

**Proof.** After appending a private pure qubit to the detector, any
binary Hermitian contraction \(K=2N_+-I\) can be replaced by the reflection
\[
 J=\begin{pmatrix}K&\sqrt{I-K^2}\\\sqrt{I-K^2}&-K\end{pmatrix}.
\]
The displayed blocks are in the new ancilla coordinate. The upper-left
compression is \(K\), and \(J^2=I\) since the two block entries commute.
The measurement \((I\pm J)/2\) with the new qubit in the upper block
preserves Eve's conditional states. Absorb the pure qubit into \(D\)
and keep the symbols \(D,\tau\). Set \(\xi=\rho\otimes\tau\).
In a Schmidt reference of \(\xi\), the difference of the two
conditional states on Eve is \((\sqrt{\xi}J\sqrt{\xi})^{T}\)
(on the support as needed). This follows by expanding
\(\sum_i\sqrt{\lambda_i}|i\rangle|i\rangle\) against the effects
\((I\pm J)/2\). The binary Helstrom formula consequently gives
\[
 2P_{\rm g}^{\rm pur}-1
 =\|\sqrt{\xi}J\sqrt{\xi}\|_1
 =F(\xi,J\xi J).
\]
The last identity follows from
\(\sqrt{J\xi J}=J\sqrt{\xi}J\) and right-unitary invariance of the
trace norm. The upper fidelity--trace-distance inequality gives
\(F(\xi,J\xi J)\le\sqrt{1-D(\xi,J\xi J)^2}\).
Right multiplication by \(J\) gives
\(2D(\xi,J\xi J)=\|[\xi,J]\|_1\).

For a bounded observable \(J\), its effective signal contraction is
\(2M-I=\operatorname{Tr}_D[(I\otimes\tau)J]\) (with the usual dual
definition of this expectation). Cycling the trace locally on
\(D\) yields
\[
 \operatorname{Tr}_D[\xi,J]=[\rho,2M-I].
\]
Partial trace contracts trace norm on this anti-Hermitian operator
(multiply by \(i\) to use the Hermitian trace-norm variational formula).
Thus \(D(\xi,J\xi J)\ge\|[\rho,M]\|_1\), and in particular \(c\in[0,1]\).
Combining the bounds proves (1). If the detector is infinite-dimensional,
all displayed states and commutators are trace-class; the reflection is
bounded, the nonzero support of a density operator is separable, and
the Schmidt, Helstrom and trace-norm identities hold there with
convergence in trace norm. No inverse is used. ∎

**Second proof of the upper bound (no fidelity inequality).**
Still use the private binary reflection dilation. For any Hermitian
contraction \(Q\) on the signal, implicitly tensored with identities
on the detector memory and dilation qubit, set \(C=i[J,Q]/2\).
It is a Hermitian contraction and \(JC+CJ=0\). For a binary Eve
guess, write \(H\) for the difference of Eve's two effects. The
operator \(J\otimes H\) on \(SD:E\) is a Hermitian contraction
anticommuting with \(C\otimes I_E\). If Hermitian contractions
\(U,V\) anticommute, then \((aU+bV)^2\le(a^2+b^2)I\) for real
\(a,b\); in particular \(\langle U\rangle^2+\langle V\rangle^2\le1\)
in every state, by taking \(a=\langle U\rangle,b=\langle V\rangle\).
In the actual joint state these expectations are
\(2P_{\rm succ}(H)-1\) and
\[
 \operatorname{Tr}(\xi C)
 =\frac{i}{2}\operatorname{Tr}([\xi,J](Q\otimes I_D))
 =\operatorname{Tr}(i[\rho,M]Q).
\]
Choose \(Q\) to be the Hermitian sign of \(i[\rho,M]\), taken as
zero on its kernel. The second expectation equals \(c\). Thus
\(2P_{\rm succ}(H)-1\le\sqrt{1-c^2}\) for each guess. This proves
(1) on the undiscarded Eve extension without first passing to a
purifying one. The same operator test loses at most \(2\eta_0\)
in the actual generation expectation under §5's trace-distance
assumption, because \(\|C\|_\infty\le1\).

Here and below \(H_{\min}(B|E,x=0)=-\log_2 P_{\rm g}(B|E,x=0)\).

## 3. Partial probes: an exact criterion for positive certification

Let \(\mathcal M\) be the nonempty set of all effects \(M\) consistent
with the observed test probabilities, including a generation
probability only if actually specified. Each constraint is linear
in \(M\). Set
\[
 c_*=\min_{M\in\mathcal M}\|[\rho,M]\|_1 .
\]
The minimum is attained by compactness. It is an SDP: minimize
\(\operatorname{Tr}Y\) with \(M\in\mathcal M\) and
\(Y\succeq \pm i[\rho,M]\). Indeed the diagonal entries in a
commutator eigenbasis give the lower bound by the sum of absolute
eigenvalues, attained at \(Y=|i[\rho,M]|\).

**Corollary 2.** The data certify positive single-round min-entropy
in this model if and only if \(\mathcal M\) contains no effect
commuting with \(\rho\). If so, the data certify at least
\(-\log_2G(c_*)>0\); the bound on the amount need not be exact.
If there is a commuting effect, diagonalize it with \(\rho\),
say \(M|i\rangle=m_i|i\rangle\). A single private detector flag
\(L\), copied to Eve, chooses threshold-projections
\(P_{L}=\sum_{i:m_i\ge L}|i\rangle\langle i|\) with weights given
by the lengths of the intervals in \([0,1]\) cut by the \(m_i\).
Use any interior point of each positive-length interval, giving at
most \(\dim(S)+1\) flags. Their mixture is \(M\). Eve measures the
generation state's purification in the conjugate eigenbasis to
learn \(i\), and together with the flag she knows the output.
This realizes \(P_{\rm g}=1\) and exactly matches all the data, with
the flag and common detector marginal independent of the signal.

A linear contrast suffices for an explicit certificate without an SDP.
Let \(u,v\) be orthogonal unit eigenvectors of \(\rho\) with eigenvalues
\(a,b\). Probe on \(|u\pm v\rangle=(|u\rangle\pm|v\rangle)/\sqrt2\).
Write \(t=p(+|u+v)-p(+|u-v)=2\operatorname{Re}\langle u|M|v\rangle\).
Then \(\|[\rho,M]\|_1\ge |a-b|\,|t|\). To see this, compress the
commutator to the span of \(u,v\); the compressed anti-Hermitian matrix
has trace norm \(2|a-b||\langle u|M|v\rangle|\), and compression is
trace-norm contractive. For a phase-rotated probe pair the same
argument applies after rephasing \(v\).

For a detector with finitely many outcomes \(b\), one can coarse-grain
to \(b\) against its complement. Eve can map her guessed label to the
same two classes, so her full guessing probability is at most that
of the binary coarse-graining. Consequently, taking
\(c_*=\min_{\{M_b\}\text{ consistent}}\max_b\|[\rho,M_b]\|_1\)
gives (1) as a bound also on the full-label guessing probability.
The minimum is attained, and can be evaluated by the above trace-norm
epigraph, one \(Y_b\) for each \(b\), plus \(\operatorname{Tr}Y_b\le c_*\)
with \(c_*\) treated as the scalar objective variable.
If \(\rho\) has simple spectrum, this is again an exact positivity
criterion: if all effects commute with \(\rho\), they are diagonal
in the same eigenbasis. For eigenvector \(i\) let a detector flag
choose a deterministic output at \(i\) according to the diagonal
probabilities \((M_b)_{ii}\). One can sample the assignments to all
\(i\) from a finite product distribution, independent of the signal,
and share this flag with Eve. Learning \(i\) from the purification gives
perfect prediction. For degenerate \(\rho\) with more than two
outcomes no converse is asserted.

## 4. Exact qubit formula

**Theorem 3.** Let \(S\) be a qubit, \(\rho=(I+rZ)/2\) with
\(0\le r\le1\), and let \(t=p(+|X+)-p(+|X-)\) from the two Pauli
\(X\) eigenstate probes. If only \(t\in[-1,1]\) is fixed, the
maximum guessing probability is \(G(r|t|)\). There is no
assumption of an unbiased effective effect for this contrast-only
projection of the data. Moreover:

1. For every *fixed* unbiased qubit effect
   \(M=(I+tX+yY+zZ)/2\), \(t^2+y^2+z^2\le1\), the maximum is
   \(G(r\sqrt{t^2+y^2})\).
2. If the entire two calibration probabilities are specified and sum
   to one, and optionally also the generation probability is specified,
   the sharp worst-case value over compatible measurements is \(G(r|t|)\).
   The data must be physically consistent in the stated model.

**Proof.** The contrast yields \(r|t|\) in §3. For a fixed unbiased
effect, the commutator norm is exactly \(r\sqrt{t^2+y^2}\): use
\([Z,X]=2iY,\ [Z,Y]=-2iX\) and \((tY-yX)^2=(t^2+y^2)I\).
Set \(s=\sqrt{1-t^2-y^2}\); for \(s>0\) select one of the
projective observable branches
\[
 J_\pm=tX+yY\pm sZ
\]
with respective probabilities \((1+z/s)/2\) and \((1-z/s)/2\).
These are nonnegative and sum to one by \(|z|\le s\).
If \(s=0\) the branches coincide and \(z=0\).
The selection flag is independent of the input, and is known to Eve.
Their average effective observable is \(2M-I\).

On branch \(\pm\), the full-reference Helstrom bias is the trace
norm of \(T_\pm=\sqrt{\rho}J_\pm\sqrt{\rho}\).
Its trace is \(\pm r s\) and determinant is
\(\det(\rho)\det(J_\pm)=-(1-r^2)/4\) since a traceless qubit
reflection has eigenvalues \(+1,-1\). Thus its eigenvalues have
opposite weak signs, and
\[
 \|T_\pm\|_1=\sqrt{(\operatorname{Tr}T_\pm)^2-4\det T_\pm}
 =\sqrt{1-r^2(t^2+y^2)} .
\]
The determinant-zero boundary uses the same formula, including zero
matrix. Since Eve knows the flag she uses the branch Helstrom
measurement. The branch biases are identical, so the average
saturates (1). The observed data can always be matched: for contrast
alone take \(y=z=0\). When \(p(+|X+)+p(+|X-)=1\), this sum
equals \(\operatorname{Tr}M=1\), forcing an unbiased effect.
Feasible data have some \(z\) with \(|z|\le\sqrt{1-t^2}\)
(\(p(+|0)=(1+r z)/2\) when given); replace \(y\) by zero,
which preserves the specified data. This realizes equality also there.
No sharpness is claimed for all fixed *biased* effects, or for
raw probabilities with a calibration sum different from one. ∎

For example, \(r=3/5,\ |t|=4/5\) gives
\(P_{\rm g}=(25+\sqrt{481})/50<47/50\), certifying strictly
more than \(-\log_2(47/50)\) bits in one generation round. At the
limits \(r=0\) or \(t=0\), the contrast alone gives exactly zero
certifiable entropy; \(r=|t|=1\) gives one bit.

## 5. Declared approximate independence

For calibration on the \(X\) eigenstates, suppose instead the joint
marginals \(\xi_x\) obey
\(D(\xi_x,\rho_x\otimes\tau)\le\eta_x\) for a common \(\tau\);
write \(\eta_0,\eta_+,\eta_-\) for the three inputs. Use the same
detector, and let \(t_{\rm obs}\) denote the actual contrast.
Let \(t\) be the contrast on the ideal product marginals using
that same POVM. Then
\[
 |t-t_{\rm obs}|\le\eta_++\eta_-
\]
by the effect variational characterization of trace distance.
Append the pure dilation qubit as before. The reflection trace
distance for the actual generation marginal is bounded below by
\[
 D(\xi_0,J\xi_0J)
 \ge D(\rho\otimes\tau,J(\rho\otimes\tau)J)-2\eta_0
 \ge r|t|-2\eta_0 .
\]
These steps use only the triangle inequality and unitary invariance.
The reference system of the actual state can still be fully purifying,
so the first part of the Helstrom--fidelity proof is unchanged.
With \([v]_+=\max(v,0)\), this proves
\[
 P_{\rm g}^{\rm actual}\ \le\
 G\!\left(\left[r\,[|t_{\rm obs}|-\eta_+-\eta_-]_+-2\eta_0\right]_+\right).
\]
In particular the margin is needed on the **joint** signal/detector
states, not just on the trusted signal. The bound uses true
conditional probabilities or independently valid deterministic
bounds on them. It is not a sampling, smooth-entropy accumulation
or finite-size theorem.
