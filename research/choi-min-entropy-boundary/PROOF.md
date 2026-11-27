# When the Choi conditional min-entropy upper bound is tight

We establish an equality criterion for a unitary mixed with
white noise in arbitrary local dimensions. With a conditioning
qubit this reproduces known white-noise equality. With a
conditioning qutrit there is a simple strict separation.
We also prove equality for local depolarizing composition on
an input or output conditioning qubit, a different noise model.
Without these noise structures the equality can already
fail for **two qubits and two unitary components**: the mixture
of identity and controlled-Z has a strict gap at every
nontrivial mixing weight. The latter statement has an exact
rational 60:40 certificate and a closed formula for the
unconstrained state cost for all weights.

## 1. Normalizations

Take \(A'\simeq A\simeq\mathbb C^d\) and
\(B'\simeq B\simeq\mathbb C^m\).
For a bipartite channel let \(W\) be its normalized Choi
state with systems grouped as \(X=R_AA\), \(Y=R_BB\).
The references \(R_A,R_B\) have dimensions \(d,m\).
Normalized means that the maximally entangled input vector
on each reference/input pair has norm one. Use two trace
costs
\[
 \begin{split}
 c_{\rm st}(W)&=\min\{\operatorname{Tr}D:
                 I_X\otimes D\succeq W,\ D\succeq0\},\\
 c_{\rm ch}(W)&=\min\{\operatorname{Tr}D:
                 I_X\otimes D\succeq W,\ D\succeq0,\
        \operatorname{Tr}_{B}D=(\operatorname{Tr}D)I_{R_B}/m\}.
 \end{split}                                                  \tag{1}
\]
These minima exist: a sufficiently large multiple of the
identity is feasible and, below its trace, the feasible sets
are closed and bounded. They are positive since \(W\) is a
state and \(\operatorname{Tr}D\ge1/d^2\) for any feasible
\(D\).

In the conventions of Badhani--Das arXiv:2604.01217v2,
the state entropy is \(-\log_2c_{\rm st}(W)\), and the
channel entropy is \(-\log_2c_{\rm ch}(W)-\log_2 d\).
Indeed, writing \(D=c\sigma\) with \(\sigma\) a state gives
the state max-divergence optimization; with the last
constraint in (1), \(\sigma\) is a normalized trace-preserving
Choi state. This is the channel optimization of their
Eq. (70) or the normalized form preceding Proposition 10.
Explicitly, their unnormalized Choi operator is
\(\Gamma^\mathcal N=dm\,W\), and their Eq. (70) minimizes
\(\operatorname{Tr}M/m\) under
\(\Gamma^\mathcal N\preceq I_X\otimes M\) and
\(\operatorname{Tr}_B M=(\operatorname{Tr}M)I_{R_B}/m\).
Substituting \(M=dm\,D\) gives (1) with objective
\(d\,\operatorname{Tr}D\); the multiplicative \(d\)
becomes the stated additive entropy term.
Thus equality in the upper bound of their Proposition 1
means precisely \(c_{\rm st}=c_{\rm ch}\), and strict
inequality of costs reverses direction for the entropies.
We prove facts about these finite-dimensional mathematical
quantities, not about experimental quantum devices.

## 2. White-noisy unitaries

Let \(U\) be any unitary from \(A'B'\) to \(AB\), with
normalized Choi vector \(\psi\), and put
\(\tau=\operatorname{Tr}_X|\psi\rangle\langle\psi|\).
For noise probability \(0\le p\le1\), the channel
\((1-p)\mathcal U+p\mathcal R\), where \(\mathcal R\)
fully replaces the output by the maximally mixed state,
has Choi state
\[
 W_p=(1-p)|\psi\rangle\langle\psi|+b I_{XY},
                  \qquad b=p/(d^2m^2).
\]
For \(p<1\), feasibility of \(D\) forces \(D\succeq bI_Y\).
Writing \(D=bI_Y+(1-p)E\) reduces the PSD inequality to
\(I_X\otimes E\succeq|\psi\rangle\langle\psi|\).
The channel trace condition is preserved under this
translation and positive rescaling, because the identity
term satisfies it. Therefore for either cost
\[
 c_j(W_p)=p/d^2+(1-p)c_j(|\psi\rangle\langle\psi|),
                    \qquad j={\rm st},{\rm ch}.             \tag{2}
\]
At \(p=1\), equality holds and both costs are \(1/d^2\):
\(D\succeq bI_Y\) is necessary and the lower endpoint is
channel-feasible.

For the pure Choi vector, the state optimizer is unique:
\[
 E_\ast=(\operatorname{Tr}\sqrt\tau)\sqrt\tau,\qquad
 c_{\rm st}(|\psi\rangle\langle\psi|)
                       =(\operatorname{Tr}\sqrt\tau)^2.     \tag{3}
\]
To verify uniqueness as well as the value, a feasible
\(E\succeq0\) must have support containing that of \(\tau\).
On this support the rank-one dominance condition is
equivalent to \(\operatorname{Tr}(\tau E^+)\le1\), where
\(E^+\) is inverse on the positive support and zero outside.
This follows by conjugating by \(I\otimes (E^+)^{1/2}\)
on the support of \(I\otimes E\). By Hilbert--Schmidt
Cauchy--Schwarz applied to \(E^{1/2}\) and
\((E^+)^{1/2}\sqrt\tau\),
\[
 (\operatorname{Tr}\sqrt\tau)^2
       \le (\operatorname{Tr}E)\operatorname{Tr}(\tau E^+)
       \le\operatorname{Tr}E .
\]
Equality forces the two matrices to be proportional with
nonzero proportionality and hence \(E\propto\sqrt\tau\).
The dominance condition at equality fixes the given factor.
Conversely \(E_\ast\) is feasible and saturates the inequalities.

By (1), existence of optima, and uniqueness of (3), for
\(0\le p<1\)
\[
 c_{\rm ch}(W_p)=c_{\rm st}(W_p)
 \quad\Longleftrightarrow\quad
 \operatorname{Tr}_{B}\sqrt\tau
             =\frac{\operatorname{Tr}\sqrt\tau}{m} I_{R_B}.
                                                               \tag{4}
\]
This is a criterion for the upper bound, not an equality
claim for arbitrary \(W\).

For \(m=2\), the criterion is always satisfied. The input
and output of a unitary Choi state separately have maximally
mixed marginals, so both qubit marginals of \(\tau\) are
maximally mixed. Thus the Pauli expansion of \(\tau\) has
only identity and two-body terms, with real \(3\times3\)
correlation matrix. A real singular value decomposition
with signed diagonal and proper rotations, implemented by
local qubit unitaries on the Pauli matrices, makes that
matrix diagonal. The resulting state is Bell-diagonal:
the commuting \(\sigma_i\otimes\sigma_i\) share a Bell
eigenbasis. Its square root is Bell-diagonal as well, so
its input marginal is proportional to the identity. This
proves (4) in that case and independently recovers the
white-noise statement already recorded by TrureTuring.
It is not claimed as the first proof of that qubit result.

### Orthogonal controlled blocks

For an exact family at higher conditioning dimensions,
partition the \(m\) computational basis labels into nonempty
sets \(I_1,\ldots,I_g\) of sizes \(n_i\). On \(A\), choose
\(g\) unitaries \(U_i\) pairwise orthogonal for the
normalized Hilbert--Schmidt inner product. Let
\[
 U=\sum_i U_i\otimes\sum_{j\in I_i}|j\rangle\langle j|.
\]
Its Choi vector has Schmidt expansion
\(\psi=\sum_i\sqrt{q_i}\,|u_i\rangle|s_i\rangle\), where
\(q_i=n_i/m\), \(u_i\) are the normalized Choi vectors of
\(U_i\), and
\(s_i=n_i^{-1/2}\sum_{j\in I_i}|j\rangle_{R_B}|j\rangle_B\).
The state cost is \((\sum_i\sqrt{q_i})^2\) by (3).
The channel cost is exactly \(g\), as follows.

For a channel-feasible \(E\) of trace \(c\), every
\(\langle jj|E|jj\rangle\le c/m\) by the partial-trace
constraint and positivity. Thus
\(\langle s_i|E|s_i\rangle\le q_i c\), since the
expectation of a positive matrix in a unit vector is
bounded by its trace on the corresponding support.
By scalar Cauchy--Schwarz,
\(\langle s_i|E^+|s_i\rangle\ge1/\langle s_i|E|s_i\rangle\).
All \(s_i\) belong to the support by feasibility. Summing
the feasible inverse inequality gives
\[
 1\ge\operatorname{Tr}(\tau E^+)
       \ge\sum_i\frac{q_i}{q_i c}=\frac{g}{c}.
\]
Conversely \(E=g\tau\) is channel-feasible, since the
given expansion gives \(\operatorname{Tr}_B\tau=I_{R_B}/m\),
and \(\operatorname{Tr}(\tau (g\tau)^+)=1\).
This proves both exact costs; (2) extends them to white
noise. At \(p<1\) they coincide exactly when all sizes
\(n_i\) are equal, by Cauchy--Schwarz for the state cost.

In particular \(d=2,m=3\), controlled \(I,I,Z\) with
blocks of sizes 2 and 1, gives pure costs
\(2\) (channel) and \(1+2\sqrt2/3\) (state). Therefore
there is a strict gap for every \(p<1\). This is a
conditioning-dimension-three limitation, not a
counterexample to the original conditioning-qubit
white-noise statement.

## 3. Local noise by composition on the conditioning qubit

Here the noise is applied **before or after** the unitary,
on the conditioning input or output alone. Namely, with
\(m=2\) let
\(\mathcal D_{B,p}(\eta)=(1-p)\eta+p\operatorname{Tr}(\eta)I_B/2\)
and similarly for the input \(B'\). Then the two costs (1)
coincide for every \(0\le p\le1\) for either channel
\[
(\mathrm{id}_A\otimes\mathcal D_{B,p})\circ\mathcal U,
\qquad
\mathcal U\circ(\mathrm{id}_{A'}\otimes\mathcal D_{B',p}).
\]
This is not the convex mixture of the entire unitary
with a reference product channel that is identity on
\(A\) and a replacer on \(B\).

Indeed choose local bases on \(R_B,B\) so that the pure
unitary Choi marginal \(\tau\) is Bell-diagonal as in §2.
Such local basis changes preserve the channel trace
constraint, and the depolarizing map is covariant under
every single-qubit unitary. Denote the Bell basis by
\(\beta_i\) for \(i\in G=\mathbb F_2^2\), with the labels
chosen as the single-qubit Pauli operators acting on
one side of a maximally entangled vector. In these
coordinates the Choi vector is
\(\psi=\sum_i\sqrt{\lambda_i}\,e_i\otimes\beta_i\),
where the \(e_i\) with \(\lambda_i>0\) are orthonormal
in \(X\). Output depolarization makes the Choi state
a positive mixture of the four pure projectors onto
\[
   \psi_g=(I_X\otimes I_{R_B}\otimes P_g)\psi,\qquad g\in G,
\]
with weights \(1-3p/4\) at \(g=0\) and \(p/4\) elsewhere,
by the Pauli twirl of a qubit. A Pauli operator maps
\(\beta_i\) to \(\beta_{i+g}\) up to a phase. For input
depolarization, the normalized maximally entangled
input transfers each Pauli to its transpose on \(R_B\);
the same label rule holds there as well, up to phases.

For each character \(\chi:G\to\{1,-1\}\), let \(V_\chi\)
multiply \(e_i\) by \(\chi(i)\) on the nonzero Schmidt
support and act as the identity outside it. Let \(W_\chi\)
multiply \(\beta_i\) by \(\chi(i)\) on \(Y\). The product
\(V_\chi\otimes W_\chi\) multiplies each \(\psi_g\) by
\(\chi(g)\), even if some Schmidt coefficients vanish.
Thus it preserves every projector in the noise mixture.
Given any state-feasible \(D\), conjugation by \(W_\chi\)
therefore gives another feasible \(D\) of the same trace.
Averaging over all four characters makes \(D\)
Bell-diagonal by character orthogonality. Its partial
trace is the required \((\operatorname{Tr}D)I_{R_B}/2\).
Apply this to a state minimizer to get equality.

The argument also allows arbitrary probability weights
on the four Pauli conjugations **in the basis** that puts
\(\tau\) into Bell-diagonal form. For isotropic local
depolarization there is no basis choice in the physical
definition of the channel. No claim is made for an
arbitrary local channel in an unrelated basis.

## 4. Mixture of two unitaries on two qubits

Now set \(d=m=2\) and consider
\(\mathcal N=a\,\mathrm{id}+b\,\mathcal{CZ}\), where
\(a,b>0,\ a+b=1\). This is classical randomization
between the two unitary channels. Let \(X_0\) be the
two-dimensional space spanned by the orthonormal
single-qubit Choi vectors of \(I_A,Z_A\); let \(Y_0\)
be the span of \(|00\rangle,|11\rangle\) on \(R_BB\).
Since controlled-Z is
\(I_A\otimes |0\rangle\langle0|_B+
 Z_A\otimes |1\rangle\langle1|_B\),
both normalized Choi vectors are supported in
\(X_0\otimes Y_0\). In the stated basis, ordered as
\(00,01,10,11\) for these two supports,
\[
 W=a\,q q^\ast+b\,r r^\ast,\qquad
 q=(1,1,0,0)^\top/\sqrt2,\quad
 r=(1,0,0,1)^\top/\sqrt2 .
                                                               \tag{5}
\]
All omitted coordinates carry zero weight. We prove
\[
 c_{\rm st}(W)=a/2+b+\sqrt{b^2+a^2/4}
                      < c_{\rm ch}(W) .                     \tag{6}
\]

Let \(t\in(0,1)\) be the unique root of
\(a(1-t^2)=4bt\). This follows from strictly decreasing
left minus right between 0 and 1. Put
\[
 u=\frac{b(1+t)}{(1-t)(1+t^2)},\qquad
     E=\begin{pmatrix}u&ut\\ut&b+ut^2\end{pmatrix}
                         \quad\text{on }Y_0,\qquad
 v=(1,t,-t,1)^\top .                                       \tag{7}
\]
Extend \(E\) by zero outside \(Y_0\). Its restriction there
is positive definite with determinant \(ub>0\).
By \(u(1+t^2)=b+a(1+t)/2\) and the equation for \(t\),
direct multiplication gives
\((I\otimes E)v=Wv\).

To show feasibility, on \(X_0\otimes Y_0\) write (5)
as \(K K^\ast\) with columns \(\sqrt a\,q,\sqrt b\,r\).
The nonzero eigenvalues of the whitened \(W\) relative
to \(I\otimes E\) are the eigenvalues of
\(G=K^\ast(I\otimes E^{-1})K\). One is 1 by the nonzero
null vector \(v\) for the slack. Using
\[
 E^{-1}=\begin{pmatrix}
  1/u+t^2/b&-t/b\\ -t/b&1/b
 \end{pmatrix},
\]
the two diagonal entries of \(G\) are respectively
\(4t/(1+t)^2\) and \((1+t^2)/(1+t)\). Both are
strictly below 1 for \(0<t<1\). Hence the other
eigenvalue is strictly below 1 and \(G\preceq I\).
This proves PSD feasibility on the two supports;
elsewhere the slack is nonnegative since \(W\) is
zero and \(E\succeq0\).

The two \(Y_0\)-row components of \(v\), \((1,t)\) and
\((-t,1)\), are orthogonal and have squared norm
\(1+t^2\). Thus for any state-feasible \(D\),
\[
  (1+t^2)\operatorname{Tr}(\Pi_{Y_0}D)
      =\langle v|I_X\otimes D|v\rangle
      \ge\langle v|W|v\rangle
      =(1+t^2)\operatorname{Tr}E .
\]
It follows that \(E\) minimizes the trace.
If the total trace of \(D\) equals that of \(E\),
all support outside \(Y_0\) vanishes by positivity and
the trace equality. Also a PSD slack with zero
quadratic form on \(v\) annihilates \(v\), so
\((I\otimes D)v=(I\otimes E)v\). The two row
components of \(v\) span \(Y_0\), forcing \(D=E\).
This proves uniqueness. Taking the trace in (7) and
using \(at/2=\sqrt{b^2+a^2/4}-b\) now gives (6)'s
state formula.

However the two diagonal values of \(E\) on
\(|00\rangle,|11\rangle\) differ by
\[
             u-(b+ut^2)=\frac{2bt}{1+t^2}>0 .
\]
The off-diagonal entry between these states vanishes
under the output partial trace. Hence the unique
state optimum violates the channel constraint in (1),
and the achieved channel minimum is strictly larger.
At the two degenerate endpoints \(a=0\) or \(b=0\)
the channel is a single unitary and there is no gap,
by the qubit part of (4).

### An entirely rational 60:40 certificate

For \(a=3/5,b=2/5\), \(t=1/3\) and
\(E=\tfrac1{25}\bigl(\begin{smallmatrix}18&6\\6&12\end{smallmatrix}\bigr)\).
Then \(c_{\rm st}=6/5\). Directly,
\(50(I\otimes E-W)\) on the two supports is
\[
 \begin{pmatrix}
 11&-3&0&-10\\ -3&9&0&0\\ 0&0&36&12\\ -10&0&12&14
 \end{pmatrix}.
\]
Taking a Schur complement in the second and third
diagonal coordinates gives
\(\bigl(\begin{smallmatrix}10&-10\\-10&10\end{smallmatrix}\bigr)\),
which is positive semidefinite. A lower witness
for the state cost is \((3,1,-1,3)^\top\), whose
\(Y_0\) reduced matrix is proportional to identity
and which is annihilated by the slack.

For any channel-feasible \(D\) of trace \(c\),
the diagonal entries on \(|00\rangle,|11\rangle\)
are at most \(c/2\) by the constraint and positivity.
Use \(w=(12,2,-3,8)^\top\). Its two rows have
off-diagonal products \(12\cdot2\) and \((-3)\cdot8\),
which sum to zero. Regardless of the off-diagonal
entries of \(D\), including complex entries, it follows
that \(\langle w|I\otimes D|w\rangle\le c\|w\|^2/2\).
By (5), \(\|w\|^2=221\) and
\(2\langle w|W|w\rangle=1388/5\). Consequently
\[
                   c_{\rm ch}(W)\ge\frac{1388}{1105}
                                            >\frac65 .
\]
This witnesses the strict gap without a numerical SDP
solver. It answers the 60:40 mixed-unitary extension,
which is distinct from the known white-noise conjecture.
