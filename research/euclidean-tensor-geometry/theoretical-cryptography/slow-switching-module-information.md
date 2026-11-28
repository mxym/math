# Two fluctuation scales for finite-module hashing with a slowly switching source

A slowly switching hidden state can make the regularity error of a public linear hash depend on the *occupation time* of an entire block, not just stationary single-letter entropies. When many switches occur, occupation fluctuations still operate at a larger scale than emission fluctuations; at critical rates some quotients sense the former and others the latter. The two Gaussian vectors become independent under the conditions below. Revealing or hiding the sampled state word gives the same limiting error in all the stated windows.

This is a statistical theorem for a fixed finite left module and a specified uniform random coefficient matrix. It makes no assertion about cryptographic hardness, implementations, or general quantum side information. The [one-shot finite-module information-spectrum theorem](https://github.com/mxym/math/blob/e67ae1997061f00436f6a73a50aec04ea4679b7b/research/euclidean-tensor-geometry/theoretical-cryptography/module-information-spectrum.md) applies to arbitrary block laws and supplies the simultaneous quotient achievability and converse; its explicit Gaussian window assumed iid sources. [Nomura–Han (2013)](https://arxiv.org/abs/1106.1879) already gives Gaussian-mixture information-spectrum formulas for static mixtures of iid or Markov sources and unrestricted intrinsic randomness, and [Uyematsu–Matsuta (2017)](https://doi.org/10.1587/transfun.E100.A.2615) studies correlated and mixed sources. [Polyanskiy–Poor–Verdú](https://people.lids.mit.edu/yp/homepage/data/gec.pdf) analyze the related scalar Gilbert–Elliott **channel coding** dispersion, including hidden and revealed states and the strictly static nonergodic case; that is a different task from the quotient hashing here. The extension here is a time-varying shared state with nontrivial random occupation fractions, the two occupation/emission scales at growing horizons, and the resulting joint quotient and per-public-matrix limits.

## 1. Source, hash, and normalization

Fix a finite unital ring \(R\), a nonzero finite left \(R\)-module \(M\), and let \(\mathcal J\) be its finite set of proper submodules. Put \(q_J=|M/J|>1\). Let \(Z(t)\) be a finite-state continuous-time Markov chain of generator \(Q\), with state space \(\mathcal S\). For a block of length \(m\), sample the state word \(W_m=(Z(iT_m/m))_{i=1}^m\). Given the path, the emissions \((X_i,Y_i)\) are independent, with law \(P_s\) on \(M\times\mathcal Y\) at sampled state \(s\), for a fixed finite classical side-information alphabet \(\mathcal Y\). The emission laws depend only on the sampled word. For each \(s,J\), define the one-copy normalized information
\[
 U_{s,J}(X,Y)=-\frac{\log P_s(X+J\mid Y)}{\log q_J},
 \qquad h_{s,J}=\mathbb E_s U_{s,J},\qquad V_s=\operatorname{Cov}_s((U_{s,J})_J).
\]
These variables are evaluated only on their positive-probability outcomes and are uniformly bounded.

Let \(A\in R^{k_m\times m}\) have independent uniform entries, independent of the source. The public hash is \(AX\), with row entries \(\sum_i A_{ji}X_i\). For either side model \(L=Y^m\) or \(L=(Y^m,W_m)\), define the per-matrix distance
\[
             D_A=\mathbb E_L\,d_{\mathrm{TV}}(\mathcal L(AX\mid A,L),U(M^{k_m})).
\]
Each statement below means \(L^1\) convergence over public \(A\) of \(D_A\) to the stated number, and the same limit for \(\inf_A D_A\) over deterministic matrices. The same limits hold in the hidden and revealed side models, which are averaged over their own side distributions. No pathwise statement about typical matrices for a *fixed* continuous-time trajectory is required.

## 2. Fixed horizon: a random occupation profile

Fix \(T_m=T>0\), with arbitrary initial law. Let
\[
 p_s=\frac1T\int_0^T 1_{\{Z(t)=s\}}\,dt,\quad
 h_J(p)=\sum_s p_s h_{s,J},\quad V(p)=\sum_s p_s V_s ,
 \quad J_*(p)=\{J:h_J(p)=r\}.
\]
For \(k_m=mr+b\sqrt m+o(\sqrt m)\), the limit is
\[
 \mathbb E_{\mathrm{path}}\!
 \begin{cases}
   1,&\min_J h_J(p)<r,\\
   0,&\min_J h_J(p)>r,\\
   \Pr\{\exists J\in J_*(p): G_J(p)<b\mid p\},
       &\min_J h_J(p)=r,
 \end{cases}                                                     \tag{1}
\]
where \(G(p)\) is centered Gaussian with covariance \(V(p)\) conditional on \(p\). Assume the threshold is a continuity threshold for the relevant tied Gaussian tests for almost every path: it suffices that whenever the third case occurs, none of its tied marginal Gaussians has an atom at \(b\), almost surely. This permits singular covariance matrices and arbitrary atoms in the *occupation* distribution.

For example, take \(M=R=\mathbb F_2\), no \(Y\), and state \(0\) or \(1\) at stationary probabilities \(1/2,1/2\), with symmetric jump rate \(\lambda>0\) and horizon \(T=1\). Emit \(\operatorname{Bernoulli}(p_0)\) or \(\operatorname{Bernoulli}(p_1)\) with \(0<p_0<p_1<1/2\). Let \(h_j=h_2(p_j)\) in bits and \(\sigma_j^2=p_j(1-p_j)(\log_2((1-p_j)/p_j))^2\). The occupation \(P\) of state 1 has atoms of size \(e^{-\lambda}/2\) at each of 0 and 1. For \(h_0<r<h_1\), (1) is
\(\Pr\{P<(r-h_0)/(h_1-h_0)\}\). The distribution is explicit: condition on \(K\sim\operatorname{Poisson}(\lambda)\), the number of switches; for \(K\ge1\) the \(K+1\) durations are uniform simplex spacings, and summing durations in a given state gives a beta distribution with parameters the numbers of that state's and the other state's intervals. At \(r=h_0\) the answer is \(e^{-\lambda}\Phi(b/\sigma_0)/2\), and at \(r=h_1\) it is \(1-e^{-\lambda}/2+e^{-\lambda}\Phi(b/\sigma_1)/2\), with \(\Phi\) the standard normal cdf. Thus the endpoint atoms have their own Gaussian windows while the interior profile comes from continuous occupation fractions.

## 3. Growing horizons: distinct outer and inner windows

Suppose \(Q\) is irreducible with stationary distribution \(\pi\). Define \(\bar h_J=\sum_s\pi_s h_{s,J}\), \(r_*=\min_J\bar h_J\), and \(\mathcal A=\{J:\bar h_J=r_*\}\). For \(J\in\mathcal A\), put \(f_J(s)=h_{s,J}-\bar h_J\) and solve \(-Qg_J=f_J\) with \(\sum_s\pi_s g_J(s)=0\). The centered occupation Gaussian \(H\) and the centered emission Gaussian \(G\) have covariances
\[
 \begin{split}
 \Sigma^{\rm occ}_{J,K}
   &=\sum_{s}\pi_s\sum_{t\ne s}Q_{st}
       (g_J(t)-g_J(s))(g_K(t)-g_K(s)),\\
 \Sigma^{\rm em}_{J,K}&=\sum_s\pi_s(V_s)_{J,K}.
 \end{split}                                                        \tag{2}
\]
A diagonal entry of \(\Sigma^{\rm occ}\) vanishes exactly when \(h_{s,J}\) is constant in \(s\): irreducibility forces \(g_J\) constant if its nonnegative edge-energy sum is zero, and the Poisson equation gives the equivalence. Divide \(\mathcal A\) into \(\mathcal A_{\rm var}\) and \(\mathcal A_{\rm const}\) accordingly.

**Outer window.** If \(T_m\to\infty\) and \(T_m^{3/2}\log m=o(m)\), then for
\[
                       k_m=mr_*+b\,m/\sqrt{T_m}+o(m/\sqrt{T_m})
\]
the limit is
\[
                          \Pr\{\min_{J\in\mathcal A} H_J<b\}               \tag{3}
\]
when none of the relevant marginal Gaussians has an atom at \(b\). In particular a constant-profile quotient has \(H_J=0\), and may create a jump at \(b=0\).

**Inner window.** If additionally \(T_m\log m=o(\sqrt m)\), the jump is resolved on the smaller scale \(k_m=mr_*+b\sqrt m+o(\sqrt m)\). Take \(H,G\) independent with (2); the limit is
\[
 \Pr\left\{\exists J\in\mathcal A_{\rm var}: H_J<0
                 \quad\text{or}\quad
          \exists J\in\mathcal A_{\rm const}: G_J<b\right\}.              \tag{4}
\]
Assume no atom at \(b\) in the emission marginals for \(\mathcal A_{\rm const}\); the occupation marginals tested at zero are nondegenerate by definition. The sufficient restrictions on \(T_m\) ensure the sampled hidden state's entropy cost is negligible at each displayed scale. The statements do not characterize faster switching or the case of a deterministic tested marginal exactly at the threshold.

For an example of both scales, take \(M=R=\mathbb F_2\times\mathbb F_2\), no \(Y\), the same two-state symmetric chain, and independent emission coordinates given the state. The first coordinate is always \(\operatorname{Bernoulli}(p)\); the second is \(\operatorname{Bernoulli}(p_s)\) in state \(s\), where \(0<p_0<p_1<1/2\) and choose \(p\) with \(h_2(p)=(h_2(p_0)+h_2(p_1))/2\). The first, second, and joint quotients all attain \(\bar h=r_*=h_2(p)\), and at the level of the conditional information observations the joint coordinate is their average (division by \(\log4\)). In (3) write \(b=c\) to distinguish the outer offset. When \(c<0\) the limit is \(\Phi(c/\sigma_{\rm occ})\), where
\(\sigma_{\rm occ}^2=(h_2(p_1)-h_2(p_0))^2/(4\lambda)\), obtained from (2) with a two-state generator. When \(c>0\) it is 1, because the first quotient is constant at the occupation scale. For (4), if the second occupancy fluctuation is negative it alone causes error, whereas if positive only the first quotient's emission matters; their independence gives
\(1/2+\Phi(b/\sigma_p)/2\), where \(\sigma_p^2=p(1-p)(\log_2((1-p)/p))^2\). So one cannot in general describe both windows by a single stationary dispersion.

## 4. The hidden-versus-revealed information comparison

Let \(S^{o}_{m,J}\) be the normalized quotient block surprisal given \(Y^m\), and \(S^{r}_{m,J}\) the same given \(Y^m,W_m\). Bayes's rule on the actual sample gives
\[
 S^o_{m,J}-S^r_{m,J}
   =\frac{\log P(W_m\mid \overline X_J,Y^m)
                    -\log P(W_m\mid Y^m)}{\log q_J},
 \tag{5}
\]
where \(\overline X_J\) is the coordinatewise projected block. The two negative log posterior terms are nonnegative and each has expectation at most \(H(W_m)\), by conditioning reducing the entropy of a finite hidden label. Hence
\[
              \mathbb E\,\max_J|S^o_{m,J}-S^r_{m,J}|
                       \le C_M H(W_m).
 \tag{6}
\]
This uses neither reliable state estimation nor disjoint emission supports.

Let \(B=\max_s(-Q_{ss})\). With \(T_m=o(m)\), the probability of a sampled transition in one tick is at most \(BT_m/m\), even if paths can make multiple jumps and return to the same state. Conditioning on whether the next sampled state changes bounds the conditional entropy of the next state by
\(h_{\rm bin}(BT_m/m)+(BT_m/m)\log(|\mathcal S|-1)\) for large \(m\) when \(|\mathcal S|\ge2\); monotonicity of the small-\(p\) bound gives this from the smaller true probability. The chain rule gives
\[
           H(W_m)=O(1+T_m\log(2+m/T_m)).
 \tag{7}
\]
A single-state chain has entropy zero. At fixed horizon this is \(O(\log m)\); in the growing-horizon regimes it is \(o(m/\sqrt{T_m})\) and \(o(\sqrt m)\), respectively. By (6) and Markov's inequality the lack of a revealed path is negligible in probability uniformly over the fixed quotient set at the required scale.

For each fixed trajectory, the empirical proportions \(p^m_s\) of sampled states differ from its continuous occupation proportions \(p_s(T_m)\) by at most \(2K_m/m\) in total \(\ell^1\), where \(K_m\) is the number of jumps on \([0,T_m]\). Only grid intervals containing a jump can differ, and each such interval contributes at most twice its relative length. When \(T_m=T\), this is \(O_{\rm path}(1/m)\). For growing horizons, \(K_m=O_{\mathbb P}(T_m)\) by bounded rates (or \(\mathbb E K_m\le BT_m\)), so the error multiplied by \(\sqrt{T_m}\) goes to zero under the outer condition. For any constant entropy profile there is no occupancy approximation error in its projected mean.

## 5. Occupation and emission convergence, and the one-shot squeeze

Conditional on the path, the revealed surprise vector is the sum of the independent emission information vectors \(U_{s_i}\). It can be written
\[
       S^r_m=m\Big(\sum_s p_s^m h_s\Big)+\sqrt m\,E_m,\qquad
       E_m=m^{-1/2}\sum_i(U_{s_i}-h_{s_i}).
 \tag{8}
\]
For every fixed real vector \(t\), the conditional characteristic function of \(E_m\) is
\[
       \exp\Big(-\tfrac12 t^\top(\sum_s p_s^m V_s)t+O_t(m^{-1/2})\Big),
 \tag{9}
\]
uniformly over paths, by multiplying Taylor expansions of bounded centered summands and taking logs near one. In the fixed-horizon case \(p^m\to p\) pathwise. The covariance in (9) thus converges conditionally to \(V(p)\). The first-order mean errors in (8) are \(O_{\rm path}(1)\), even at paths tied exactly at \(r\). For each fixed path the signs of nonzero \(h_J(p)-r\) dominate, and the tied components have the indicated Gaussian union limit by marginal continuity. Bounded convergence averages these limits and gives (1) for revealed information. The same argument at \(b\pm\delta\) and then \(\delta\downarrow0\), using (6), proves the same union limit for hidden information. One can choose nearby \(\delta\)'s at continuity thresholds; the only possible atom of a Gaussian marginal is at zero.

For growing horizons, use the ergodic theorem and the Poisson equations in §3. The process
\[
 M_J(T)=g_J(Z(T))-g_J(Z(0))-\int_0^T Qg_J(Z(t))\,dt
\]
is a martingale with bounded jumps. Its normalized predictable covariance at time \(T\) converges to the first line of (2), by ergodicity of the instantaneous jump-variance function. Bounded jumps give the Lindeberg condition after dividing by \(\sqrt T\); the [martingale CLT of Rebolledo](https://doi.org/10.1007/BF00587353), or its scalar version along every linear combination, gives the occupation Gaussian for \(T^{-1/2}\int_0^T f_J(Z(t))\,dt\), since the endpoint \(g_J\) terms are bounded. Sampling does not change that limit by §4. The ergodic theorem also gives \(p^m\to\pi\) in probability, so (9) tends in probability to a deterministic Gaussian characteristic function. Multiplying this bounded conditional characteristic function by that of the scaled occupation variable, which is path measurable, proves joint convergence to *independent* \(H\) and \(G\). This independence is a limiting assertion, not an assumption about hidden-state emissions. In (3) the \(O_{\mathbb P}(\sqrt m)\) emission fluctuation is negligible because \(T_m=o(m)\). In (4), divide each nonconstant active coordinate by \(m/\sqrt{T_m}\), with threshold tending to zero; keep each constant active coordinate on \(\sqrt m\), where its conditional means are exactly \(mr_*\). Inactive averaged coordinates stay above the cut. Equations (6)–(7) make the hidden perturbation negligible on both these scales. The joint Gaussian expressions with strict inequalities now follow from the continuity assumptions.

Finally apply the cited one-shot theorem, (1) of that note, with \(\gamma=2\log m\). Its events test \(S_{m,J}<k_m\pm\gamma/\log q_J\), with the plus/minus errors vanishing uniformly over the fixed \(J\)'s on every displayed scale. Their two union probabilities therefore converge to the same stated \(p\). The theorem gives a lower bound \(D_A\ge l_m\) for every matrix and an average upper bound \(\mathbb E_A D_A\le u_m\) with \(l_m,u_m\to p\). Hence \(\mathbb E_A|D_A-p|\le u_m-l_m+|l_m-p|\to0\); also \(l_m\le\inf_A D_A\le u_m\). This proves all the per-public-matrix and deterministic infimum assertions without replacing the joint quotient cutoff by a maximum of marginal errors.

The companion checker does finite exact checks of posterior ratios even with overlapping emissions, conditional-on-jump two-state occupation mixture moments and the Poisson-equation covariance normalization. The asymptotic conclusions use the arguments above, not a simulated chain or estimation of a hidden trajectory.
