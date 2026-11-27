# The joint information-spectrum window for finite-module hashing

Let \(R\) be a finite unital ring and \(M\ne0\) a finite left \(R\)-module. Neither commutativity nor semisimplicity is required. For \(x=(x_1,\ldots,x_m)\in M^m\), let
\[
   (Ax)_i=\sum_{j=1}^m A_{ij}x_j,\qquad
      A\in R^{k\times m}.
\]
The public \(A\) has independent uniform entries, independently of the source \((X,Y)\) with \(X\in M^m\) and finite classical side information \(Y\). Let
\[
 D_A=\mathbb E_Y\,d_{\rm TV}(\mathcal L(AX\mid Y,A),U(M^k)).
\]
The joint distance to the same public \(A,Y\) and an independent uniform output is \(\mathbb E_A D_A\). All assertions concern statistical regularity of this specified hash, not a claim about an operating cryptosystem.

Write \(\mathcal J\) for the set of proper \(R\)-submodules of \(M\), including \(0\), and \(q_J=|M/J|\). For each \(J\), write \(\overline X_J\) for the coordinatewise projection, and define
\[
             I_J(X,Y)=-\log P_{\overline X_J\mid Y}
                           (\overline X_J\mid Y).
\]
All logarithms are natural.

**One-shot theorem.** For any positive \(\gamma\) and any law of \((X,Y)\), define
\[
 B_\pm=\Pr\{\exists J\in\mathcal J:\ I_J(X,Y)<k\log q_J\pm\gamma\}.
\]
Then
\[
 \begin{split}
 D_A&\ge B_- -|\mathcal J|e^{-\gamma}\qquad\text{for every fixed }A,\\
 \mathbb E_A D_A&\le B_+ +\tfrac12\sqrt{|\mathcal J|e^{-\gamma}}.
 \end{split}                                                            \tag{1}
\]
In particular the law of the **joint** vector of quotient self-informations, not just its coordinatewise means or variances, determines the critical window.

**Memoryless theorem.** Let \((X,Y)\) now consist of \(m\) iid copies of a fixed pair \((X_1,Y_1)\). Put
\[
 R_*=\min_{J\in\mathcal J} \frac{H(\overline X_{1,J}\mid Y_1)}{\log q_J},
 \qquad \mathcal J_*=\{J:\ H(\overline X_{1,J}\mid Y_1)/\log q_J=R_*\}.
\]
If \(k/m\) is asymptotically strictly below \(R_*\), then \(\mathbb E_A D_A\to0\); if it is asymptotically strictly above \(R_*\), then \(D_A\to1\) uniformly in \(A\). At \(k=mR_*+b\sqrt m+o(\sqrt m)\), let \(G\) be centered Gaussian with covariance of the one-copy normalized self-information vector
\[
 Z=\left(
 \frac{-\log P_{\overline X_{1,J}\mid Y_1}(\overline X_{1,J}\mid Y_1)}
                   {\log q_J}\right)_{J\in\mathcal J_*}.
\]
At every continuity point \(b\) of the distribution of \(\min_{J\in\mathcal J_*}G_J\),
\[
       D_A\ \longrightarrow\ \Pr\{\min_{J\in\mathcal J_*}G_J<b\}
       \quad\text{in } L^1\text{ over the public matrix}.                 \tag{2}
\]
The same limit holds for the minimal possible distance over all deterministic coefficient matrices. All \(b\) are continuity points if every active coordinate has nonzero variance, even if the covariance matrix is singular. In that case, for \(k=\lfloor mR_*+b\sqrt m\rfloor\) and \(b\) in a fixed bounded interval, (2) has error \(O(\log m/\sqrt m)\) in \(L^1\). When an active quotient has zero dispersion, \(b=0\) can be a genuine exception; the one-shot bounds do not decide that finer critical window.

**Prior and scope.** [Boudgoust–Lapiha, *Leftover Hash Lemma(s) Over Cyclotomic Rings*, §3](https://opencryptology.org/2025/1080/versions/20260428T172000Z.pdf) gives the counting-ideals strong leftover-hash bound from quotient collision bounds, also treating leakage; [ePrint 2024/1695](https://opencryptology.org/2024/1695/versions/20260428T172000Z.pdf) studies entropy lower bounds for discrete Gaussian inputs to this type of hash. The collision analysis below uses the same algebraic principle, written for a finite left module. [Hayashi, *Second order asymptotics in fixed-length source coding and intrinsic randomness*](https://arxiv.org/abs/cs/0503089) gives the ordinary information-spectrum comparison and scalar second-order profile for unrestricted intrinsic randomness. The point here is to apply a single simultaneous cut to all the quotient laws, prove a matching union converse for every matrix, and identify the resulting joint and public-matrix limits. These statements are for fixed finite alphabets, fixed module, and classical side information. We make no statement about quantum side information, growing modules, seed complexity, or security reductions.

## 1. Joint cutoff achievability

Condition first on \(Y=y\) with positive probability. Write \(P_y\) for the conditional source law and \(Q_y\) for its restriction, without normalizing, to the event
\[
       I_J(x,y)\ge k\log q_J+\gamma\quad\text{for every }J.
\]
Let \(g_y=\sum_x Q_y(x)\). For every \(J\) and every quotient vector \(z\), if some retained point projects to \(z\), then \(P_{\overline X_J\mid y}(z)\le q_J^{-k}e^{-\gamma}\). Therefore the projected subprobability \(Q_{y,J}\) satisfies
\[
      \sum_z Q_{y,J}(z)^2\le g_y q_J^{-k}e^{-\gamma}.                    \tag{3}
\]
It is important that the cutoff tests the original conditional projection law instead of a projection of a separately normalized trimmed source.

Put \(C=|M|^k\). For a difference \(v=x-x'\), put \(J(v)=\sum_j Rv_j\). One uniform row of coefficients maps \(v\) uniformly onto \(J(v)\): its image is exactly this submodule and all fibers of the additive group homomorphism have the same size. Thus
\(\Pr_A(Ax=Ax')=|J(v)|^{-k}\).
If \(Q_{y,A}\) denotes the pushforward of \(Q_y\), expansion around the uniform subprobability of mass \(g_y\) gives the exact identity
\[
 C\,\mathbb E_A\sum_u\big(Q_{y,A}(u)-g_y/C\big)^2
   = \sum_{x,x'} Q_y(x)Q_y(x')\big(|M/J(x-x')|^k-1\big).               \tag{4}
\]
A term from \(J(v)=M\) vanishes. Otherwise, dropping \(-1\), group terms by \(J(v)=J\), and enlarge that group to all pairs \(x\equiv x'\bmod J\). Equations (3) and (4) bound the right hand side by \(g_y|\mathcal J|e^{-\gamma}\).

By Cauchy–Schwarz first in the output and then over \(A\),
\[
 \frac12\mathbb E_A\|Q_{y,A}-g_y U\|_1
           \le \tfrac12\sqrt{g_y|\mathcal J|e^{-\gamma}}.
\]
The discarded mass contributes at most \(1-g_y\) in half the \(\ell^1\) distance, since it and \((1-g_y)U\) have equal mass. Average over \(y\) and use \(g_y\le1\). This proves the upper bound in (1).

## 2. Simultaneous support converse

For the same conditional source and each \(J\), let
\[
   S_{y,J}=\{z\in(M/J)^m: -\log P_{\overline X_J\mid y}(z)
                                          <k\log q_J-\gamma\}.
\]
Each point in \(S_{y,J}\) has mass greater than \(q_J^{-k}e^\gamma\), so \(|S_{y,J}|\le q_J^k e^{-\gamma}\). For a fixed \(A\), form a single output set \(E_{A,y}\) consisting of all \(u\in M^k\) whose projection modulo **some** \(J\) is in \(A_J S_{y,J}\), where \(A_J\) is the same coefficient map on the quotient left module. Under uniform output its probability is at most \(|\mathcal J|e^{-\gamma}\) by the union bound. Under the actual output its probability is at least the conditional probability of the union of the bad input events: the maps commute with the quotient projections. Testing \(E_{A,y}\) and averaging over \(y\) gives the lower bound. The argument is deterministic in the matrix. In particular a maximum of individual quotient lower bounds would lose the correlation information retained by this union.

## 3. The public-matrix normal window

For a memoryless source, \(I_J/\log q_J\) is the sum of the \(m\) iid normalized conditional self-informations. They are bounded almost surely in the fixed finite model. The law of large numbers in (1) with \(\gamma\to\infty,\gamma=o(m)\) gives the first-order statements.

For the stated second-order scaling, take \(\gamma=2\log m\). An inactive quotient has its mean a fixed positive amount per copy above \(R_*\), so its lower-tail event in either cutoff has probability \(o(1)\); for bounded \(b\) a Chebyshev bound gives \(O(1/m)\). For the active vector, the multivariate central limit theorem, on its possibly lower-dimensional covariance span, gives a common limit for the two union probabilities at each continuity point. This proves convergence of the bounds in (1) to the same number \(p=\Pr(\min_J G_J<b)\).

Write \(\ell_m\) and \(u_m\) for the lower and upper bounds in (1). Then \(D_A\ge\ell_m\) pointwise, and
\[
          \mathbb E_A|D_A-p|
              \le u_m-\ell_m+|\ell_m-p|.
\]
Thus (2) is an average absolute error bound for the *per-public-matrix* distances. It also squeezes the infimum attained by a deterministic matrix between \(\ell_m\) and \(u_m\).

For the quantitative assertion use the [Bentkus convex-set Berry–Esseen bound](https://doi.org/10.1016/S0378-3758(02)00094-0) on the nondegenerate covariance span, after whitening there. The event that **none** of the active quotients is below its threshold is an intersection of halfspaces, hence convex in that span. The finite third moment gives \(O(m^{-1/2})\) error, uniformly in the thresholds. The cutoff displacements, after normalization by \(\sqrt m\), are \(O(\log m/\sqrt m)\) for each quotient, including the rounding of \(k\). The Gaussian probability in strips of these widths is bounded by \(O(\log m/\sqrt m)\) when all active marginals have nonzero variance, by summing their one-dimensional bounded-density estimates. The first-order inactive and the leftover-hash errors are smaller. Inserting these estimates into the preceding inequality proves the quantitative version. No invertibility assumption on the full active covariance is used.

## 4. A correlated split-ring example

Take \(R=M=\mathbb F_2\times\mathbb F_2\), no side information, with one copy \((B,B+C)\) for independent \(\operatorname{Bernoulli}(p)\) bits \(B,C\), \(0<p<1/2\); addition is modulo two. The low-entropy single-coordinate quotient \(B\) has normalized entropy \(h_2(p)\) in bits, the other coordinate has greater entropy (bias parameter \(2p(1-p)\)), and the joint quotient has normalized entropy \((H(B)+H(C))/(2\log 2)=h_2(p)\). Here \(h_2\) is binary entropy in bits.

Thus \(R_*=h_2(p)\). Let \(N_1,N_2\) be independent normals of variance \(p(1-p)(\log_2((1-p)/p))^2\). The two active Gaussians are \(N_1\) and \((N_1+N_2)/2\), because the joint self-information is the sum of the independent copy informations before division by two. At \(b=0\) the critical TV tends to \(5/8\): in the isotropic \((N_1,N_2)\)-plane the event that both are nonnegative is a wedge of angle \(3\pi/4\), with probability \(3/8\). With two independent \(\operatorname{Bernoulli}(p)\) coordinates without the XOR change, \(R_*\) is the same, yet the corresponding nonnegative event is a right-angle quadrant and the limiting TV is \(3/4\). These finite-algebra examples demonstrate why retaining the correlation of the active quotient informations matters.

**Replay.** Run `python3 verify-module-info-spectrum.py`. It checks exact pair collisions and finite one-shot bounds on small rings and a noncommutative module, and illustrates the two active-constraint binomial limits. No claim relies on a simulation or numerical fit.
