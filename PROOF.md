# Fixed-marginal privacy amplification with a reused seed

## 1. Model and statements

Let \(X_1,\ldots,X_k\) be finite classical registers with common
alphabet \(\mathcal X\), and \(E\) a finite-dimensional quantum side
register, in a normalized joint cq state \(\rho\). A finite random
function \(f:\mathcal X\to[m]\) is drawn with law \(F\), independently
of this entire input state, and reused on all blocks. Write
\(Z_i=f(X_i)\) and let \(\rho^f\) be the post-hash state; its marginal
on \(E\) remains \(\rho_E\). Let \(\tau_m=I_m/m\). Set
\[
 T_k(f)=\tfrac12\|\rho^f_{Z_{\le k}E}
                     -\tau_m^{\otimes k}\otimes\rho_E\|_1.
\]
All relative entropies \(D\) and logarithms \(\ln\) below use
natural units. \(H_{\min}\) uses bits.

For \(B_i=X_{<i}E\), write
\(\rho_{X_i B_i}=\sum_x |x\rangle\langle x|\otimes R_{i,x}\) and
\(\sigma_i=\sum_x R_{i,x}\). Interpret inverse powers of \(\sigma_i\)
on its support and as zero off it. Define
\[
 A_{i,x}=\sigma_i^{-1/4}R_{i,x}\sigma_i^{-1/4},\qquad
 G_i=\sum_x\operatorname{tr}(A_{i,x}^2),\qquad
 G_i(f)=\sum_z\operatorname{tr}\!\left(\sum_{x:f(x)=z}A_{i,x}\right)^2 .
\]
The trace in the last definition is of the operator square.
Assume the seed law is \(\mu\)-almost two-universal:
\(1/m\le\mu\le1\) and \(\Pr[f(x)=f(y)]\le\mu\) whenever \(x\ne y\).
Then let
\[
 B_i^* = m\big(\mu+(1-\mu)G_i\big)-1,\qquad
 L=\sum_{i=1}^k\ln(1+B_i^*).
\]
(The star notation distinguishes the real number \(B_i^*\) from
the conditioning register \(B_i\).)

**Theorem.** The expected relative entropy to the uniform-output
ideal state, with the real side marginal, is at most \(L\).
Moreover
\[
 \mathbb E_f T_k(f)^2\le
 M:=\min\!\left\{\frac L2,\ \frac14\left(\sum_i\sqrt{B_i^*}\right)^2\right\}.
\]
Hence the average trace-distance error (including the public seed)
is at most \(\min\{1,\sqrt M\}\), and
\(\Pr_f[T_k(f)\ge\delta]\le\min\{1,M/\delta^2\}\) for \(\delta>0\).
If \(F'\) is an independent-of-input seed law at total variation
distance at most \(\eta\) from \(F\), the tail is at most
\(\min\{1,M/\delta^2+\eta\}\). If the exact input-dependent pair
collision probabilities are known, each \(\mu+(1-\mu)G_i\) can
instead be replaced by the smaller \(\mathbb E_F G_i(f)\).

In particular, \(G_i\le 2^{-H_{\min}(X_i|X_{<i}E)_\rho}\).
With a common bound \(H_{\min}(X_i|X_{<i}E)_\rho\ge h\) and
\(b=m\mu-1+m(1-\mu)2^{-h}\), the relative-entropy route gives
\(M\le \tfrac{k}{2}\ln(1+b)\). When \(\mu=1/m\),
\(b=(m-1)2^{-h}\). Thus under the unsmoothed minimum-entropy
hypothesis in Equation (6) of Bach–Moreno Babuglia–Brask, a
stronger distance has a tail coefficient growing linearly in
\(k\), as opposed to the quadratic bound in their Equation (7).
This comparison does not require an exchange of their
minimized distance for an equal quantity: their minimized
distance is bounded above by \(T_k(f)\).
All formulas are finite-dimensional and seed independence is
essential. The separate case of an individually smoothed
state for each block need not give one consistent jointly close
input state and is not silently included.

## 2. The local collision estimate

**Standard CQ collision lemma.** At the true side marginal,
\(G_i\) is the raw pretty-good guessing probability and
\(G_i\le2^{-H_{\min}(X_i|B_i)}\). Under \(\mu\)-almost
two-universal hashing, \(\mathbb E_F G_i(f)\le G_i+\mu(1-G_i)\).
The latter is Bach–Moreno Babuglia–Brask Lemma III.16,
Equation (57), written in our raw-prefix notation.

Since \(R_{i,x}\) are positive and sum to \(\sigma_i\), their
supports lie in that of \(\sigma_i\) and
\(\sum_x A_{i,x}=\sigma_i^{1/2}\).
Products of two positive semidefinite operators have
nonnegative trace. Expanding squares gives
\[
 \mathbb E_F G_i(f)
 = \sum_{x,y}\Pr_F[f(x)=f(y)]\,\operatorname{tr}(A_{i,x}A_{i,y})
 \le G_i+\mu(1-G_i).
\]
This also proves the formula using exact pair collisions.
The operators \(M_x=\sigma_i^{-1/2}R_{i,x}\sigma_i^{-1/2}\) sum
to the support projection of \(\sigma_i\), and by cyclicity
\(\operatorname{tr}(R_{i,x}M_x)=\operatorname{tr}(A_{i,x}^2)\).
If \(R_{i,x}\le 2^{-h}\theta\) holds for every \(x\) and one
density operator \(\theta\) on \(B_i\), then
\[
 G_i \le 2^{-h}\operatorname{tr}\!\left(\theta\sum_x M_x\right)
      \le 2^{-h}.
\]
Taking the supremum over feasible \(h\) proves the
conditional min-entropy inequality without any assumption on
commutativity or smoothing. This is also the success probability
of the pretty-good measurement for the ensemble \(R_{i,x}\).

## 3. Relative entropy chain, with the same seed in every term

For each fixed \(f\), the von Neumann entropy chain rule gives
\[
 \begin{split}
 D(\rho^f_{Z_{\le k} E}\;\|\;\tau_m^{\otimes k}\otimes\rho_E)
 &= k\ln m-H_\rho^f(Z_{\le k}|E)\\
 &= \sum_i \bigl[\ln m-H_\rho^f(Z_i|Z_{<i}E)\bigr]\\
 &\le \sum_i D(\rho^f_{Z_i X_{<i}E}\;\|\;\tau_m\otimes\sigma_i).
 \end{split}
\]
Here \(\rho^f_{Z_i X_{<i}E}\) means that only \(X_i\) is hashed.
The inequality follows from data processing on the raw conditioning
register \(X_{<i}E\): hashing its classical part gives the actual
\(Z_{<i}E\) and cannot decrease the conditional von Neumann entropy
of \(Z_i\). The common seed may be reused in this reasoning because
the calculation is done at one fixed seed, with one common
underlying cq state.

The Umegaki divergence is upper bounded by the sandwiched Rényi
divergence of order two. Evaluating the latter for
\(\rho^f_{Z_iB_i}\) and \(\tau_m\otimes\sigma_i\) gives
\[
 D(\rho^f_{Z_iB_i}\;\|\;\tau_m\otimes\sigma_i)
 \le \ln\,\operatorname{tr}
   \left[(\tau_m\otimes\sigma_i)^{-1/4}
         \rho^f_{Z_iB_i}(\tau_m\otimes\sigma_i)^{-1/4}\right]^2
 =\ln(mG_i(f)).
\]
Here the scalar \(m^{1/4}\) occurs twice inside the square,
and the traces sum over the orthogonal \(Z_i\)-blocks.
Every \(mG_i(f)\ge1\) by the Hilbert–Schmidt Cauchy–Schwarz
inequality and normalization, so the logarithms cause no
support or positivity problem. Taking expectations, Jensen
and the local estimate give
\[
 \mathbb E_F D(\rho^f_{Z_{\le k} E}\;\|\;\tau_m^{\otimes k}\otimes\rho_E)
 \le \sum_i \ln(m\,\mathbb E_F G_i(f))
 \le L .
\]
No independence among the random summands is assumed.
Quantum Pinsker in natural units, \(D(\alpha\|\beta)\ge
2(\|\alpha-\beta\|_1/2)^2\), gives the \(L/2\) second-moment
bound. For instance, the constant follows by applying
relative-entropy data processing to the binary Helstrom
measurement, then the classical Pinsker inequality.

## 4. The companion trace bound and tail deductions

Let \(d_i(f)\) be the trace distance of \(\rho^f_{Z_i B_i}\)
to \(\tau_m\otimes\sigma_i\). The usual fixed-marginal
single-block weighted trace estimate follows directly from
Schatten Hölder. Put
\[
 Q_i=(I_m\otimes\sigma_i^{-1/4})
       (\rho^f_{Z_iB_i}-\tau_m\otimes\sigma_i)
       (I_m\otimes\sigma_i^{-1/4}).
\]
Then \(\operatorname{tr}(Q_i^2)=G_i(f)-1/m\), since
\(\sum_z\sum_{x:f(x)=z}A_{i,x}=\sigma_i^{1/2}\) and
\(\operatorname{tr}\sigma_i=1\). Hölder with exponents
\(4,2,4\) shows
\[
 d_i(f)^2\le\frac{m}{4}\operatorname{tr}(Q_i^2)
           =\tfrac14(mG_i(f)-1).
\]
Define \(T_i\) with only the first \(i\) output blocks and the
same \(E\), and \(T_0=0\). The triangle inequality first compares
the actual \(i\)-block state with
\(\tau_m\otimes\rho^f_{Z_{<i}E}\), then replaces that prefix
state with its ideal. The first cost is at most \(d_i(f)\)
by hashing the raw prefix and contractivity; the second cost
is \(T_{i-1}(f)\). Thus \(T_k(f)\le\sum_i d_i(f)\).
Minkowski in \(L^2(F)\) yields the second choice in \(M\).
It is useful for one block and when most \(B_i^*\) are zero.

Cauchy–Schwarz bounds the mean. With the seed as an orthogonal
public classical register, the real and ideal states use the
same seed law, and the trace norm equals the mean fixed-seed
trace norm by the direct-sum identity.
Markov applied to \(T_k^2\) gives the tail. Under an alternative
independent seed law \(F'\) the function \(T_k(f)\) is unchanged
and the mass of the bad-seed event increases by at most \(\eta\).
No conclusion is made about a source adapting to the seed.
As a distinct optional smoothing statement, if **one normalized
joint cq state** \(\widetilde\rho_{X^k E}\) is trace-distance at
most \(\nu\) from the true input and satisfies the collision
bounds, then \(T_k(f;\rho)\le T_k(f;\widetilde\rho)+2\nu\)
for every \(f\), by contractivity for the real and ideal
marginals. Use the smoothed state's \(M\) and replace \(\delta\)
by \(\delta-2\nu\) in the tail when the latter is positive.

## 5. A self-contained classical tightness example

Classical shared-seed block hashing and the order of its
block-count loss were analyzed by Chung and Vadhan.
We include this simple binary example to calibrate the form
of the present CQ bound, not as a new classical lower-bound result.

Let \(t\ge4\) be even, \(N=t^2\), and let the raw inputs be
independent uniform symbols in \([N]\), with trivial \(E\).
Draw uniformly from the binary functions with exactly
\(s=(N+t)/2\) preimages of zero. For any distinct inputs the
collision probability is
\[
 \frac{s(s-1)+(N-s)(N-s-1)}{N(N-1)}=\frac12.
\]
Thus this is a two-universal family. Every seed on every block
gives the same binary output law with bias \(t/(2N)\), and
\(G_i=1/N\). Under the uniform target, write
\(S_k=\sum_{j=1}^k Y_j\), with \(Y_j\) independent Rademacher
variables, and \(\beta=1/\sqrt{N}\).
The likelihood ratio is \(V=\prod_{j=1}^k(1+\beta Y_j)\).
By the orthogonal product expansion,
\[
 \mathbb E(V-1-\beta S_k)^2
   =(1+\beta^2)^k-1-k\beta^2\le e^x-1-x\le x^2,
 \qquad x=k/N\le 1/16 .
\]
The last inequality follows from the exponential series, or
from \(e^x-1-x\le \tfrac12x^2e^x\) and \(e^{1/16}<2\).
Hölder applied to
\(\mathbb E|S_k|^2\le(\mathbb E|S_k|)^{2/3}
(\mathbb E|S_k|^4)^{1/3}\), with the second and fourth moments
\(k,\,3k^2-2k\), implies \(\mathbb E|S_k|\ge\sqrt{k/3}\).
Consequently for every seed
\[
 T_k(f)=\tfrac12\mathbb E|V-1|
 \ \ge\ \tfrac12\big(\sqrt{x/3}-x\big)
 \ \ge\ \tfrac18\sqrt{k/N}.
\]
At threshold \(\delta=\tfrac18\sqrt{k/N}\) every seed is bad
in this abstract example. In particular, a universal conclusion
of form \(g(k)G_i/\delta^2\) for equal local collision terms
cannot have \(g(k)=o(k)\). Indeed take arbitrarily large \(k\)
and even \(t\) with \(N=t^2\ge16k\); that conclusion would be
\(64g(k)/k\) while the true probability is one. This proves
order-optimality in \(k\) for this form of guarantee, not optimal
constants or optimal dependence in every other regime.

## 6. Exact conditional independence and marginal stationarity

This section specializes the assumptions (CI) and (MS) in
Bach–Moreno Babuglia–Brask Equation (129). For \(k\ge2\), suppose
\(I(X_i:X_{<i}|E)=0\) for every \(i\ge2\) and all \(X_iE\) marginals
are the same, identifying copies of \(\mathcal X\).
These conditions are equivalent to a representation
\[
 \rho_{X_{\le k}E}
 =\bigoplus_j p_j\,\left(\sum_x q_j(x)|x\rangle\langle x|\right)^{\otimes k}
             \otimes \theta_j,
\]
where the \(\theta_j\) are normalized states on disjoint orthogonal
sectors of \(E\). Thus conditioning on the sector label, which
can be read from \(E\) without disturbing the state, makes the
raw blocks independent and identically distributed; no independence
of the blocks before conditioning is asserted.

To prove it, apply the equality case of strong subadditivity to
\(X_1,E,X_2\), giving sectors \(E_j=L_j\otimes R_j\) and
\(\rho_{X_1 E X_2}=\bigoplus_j p_j\rho^{(j)}_{X_1 L_j}\otimes
\rho^{(j)}_{R_j X_2}\). Discard zero-weight sectors. Because the
endpoints are classical, each factor is cq (dephasing the
respective endpoint leaves the corresponding marginal unchanged).
Write its subnormalized blocks as \(U_{j,x}\) and \(V_{j,x}\),
with sums \(U_j,V_j\). Equality of the two endpoint-to-\(E\)
marginals says
\(U_{j,x}\otimes V_j=U_j\otimes V_{j,x}\).
Partial traces give \(U_{j,x}=q_j(x)U_j\) and
\(V_{j,x}=q_j(x)V_j\), where \(q_j(x)\) is their equal trace.
Then \(\theta_j=U_j\otimes V_j\). This proves the formula
for two blocks and identifies the common \(XE\) marginal.

For \(i>2\), equality in data processing for conditional mutual
information gives the Petz recovery of \(X_i\) from \(E\), with
the identity on \(X_{<i}\). The map acting on \(E\) alone is determined
by the common \(X_iE\) marginal and \(\rho_E\):
\[
 \mathcal R(Y)=\rho_{XE}^{1/2}
   [I_X\otimes(\rho_E^{-1/2}Y\rho_E^{-1/2})]\,\rho_{XE}^{1/2}.
\]
It is defined on the support of \(\rho_E\), with a trace-preserving
extension if desired. On the normalized sector state
\(\theta_j\) it gives
\(\sum_x q_j(x)|x\rangle\langle x|\otimes\theta_j\), since both
\(\rho_E\) and \(\rho_{XE}\) are block diagonal with respective
sector coefficients \(p_j\) and \(p_jq_j(x)\). Induction now
gives the displayed formula for all \(k\). Conversely this
formula implies stationarity and zero conditional mutual
information for every step by the direct-sum entropy identity
and the conditional tensor products.

For each \(f\), let \(P_{j,f}\) be the pushforward of \(q_j\).
Trace distance for these orthogonal sectors is
\[
 T_k(f)=\sum_j p_j\,\mathrm{TV}(P_{j,f}^{\otimes k},U_m^{\otimes k})
       \le 1-(1-T_1(f))^k \le k T_1(f).
\]
The first inequality takes a product of optimal classical
one-block couplings within each sector, then uses concavity of
\(d\mapsto1-(1-d)^k\) on \([0,1]\).
The result concerns the fixed real side marginal; it does not
claim the corresponding inequality with the one-block trace
distance replaced by an unrelated optimizing ideal marginal.

The entropy requirement of the main theorem is genuinely weaker
than (CI)+(MS) when comparing with a common min-entropy lower
bound. Under (CI)+(MS) the guessing probability in each sector
is the same with or without the raw prefix, since the prefix is
independent of the next output given the readable sector and the
remaining quantum state in the sector is constant. Thus (CI)+(MS)
imply the unsmoothed min-entropy condition with the first block
as reference. For example, trivial \(E\) and the stationary Markov
chain with law \((1/2,1/4,1/4)\) and transition rows
\((1/2,1/2,0),(1/2,0,1/2),(1/2,0,1/2)\) have raw-conditional
guessing probabilities \(1/2\) at every step, but adjacent blocks
are dependent. By contrast mere equality of the marginal
min-entropies does not suffice: the proof always uses \(X_{<i}E\)
as the side register. The linear-in-\(k\) result is a
positive bound under stated conditions, not a claim about
the weakest conditions among all source and seed models.
