# The Poisson critical window for private-batch ring learning

## 1. Statement

Use the fixed-odd-modulus dyadic wrapped-Gaussian experiment and private-batch blackboard model from the [entropy-scale batch theorem](https://github.com/mxym/math/blob/9c7c903b1aa999d663b8bc4f5b48ad499beb738e/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-batch-communication-entropy-scale.md) and its [fully interactive extension](https://github.com/mxym/math/blob/62d53dfd990045d60be8a89f6272ca5c23f9d1db/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-interactive-blackboard-entropy-scale.md). Namely \(q\ge3\) is fixed and odd, \(d\) grows through powers of two, \(S\) is uniform in \(R=(\mathbb Z/q)[X]/(X^d+1)\), \(b=\beta/d\) with \(\beta>0\) fixed, and each of \(B=B_d\) parties privately observes \(k=k_d\) entire iid coefficient/response rows conditional on \(S\). Parties may repeatedly and interactively write on the public blackboard, each at most \(m=m_d\) bits total. The choice of speaker and timing must depend only on public information; no raw rows are available to the referee. Local and central computation are unrestricted.

Let \(L=\log q\), \(\Lambda=\log B\), and \(\Delta=dL-kdb^2>0\). Assume
\[
 \Lambda\longrightarrow\infty,\qquad \Lambda=o(d^{1/3}),\qquad
 m\sqrt{\Lambda/d}\longrightarrow0,\quad m\ge1,
 \qquad
 \frac{\Delta^2}{4Ld}-\Lambda+\tfrac12\log\Lambda\longrightarrow c
 \tag{1}
\]
for a fixed real \(c\). Write \(\rho=e^{-c}/(2\sqrt{\pi})\).

**Theorem.**
1. For any specified binary property that is as close to balanced under the uniform prior as possible, the supremal success probability, over all such blackboard protocols, tends to \(1-\frac12e^{-\rho}\). More generally, for a sequence of binary properties with majority prior success \(p_d\), the optimal uniform-prior success equals \(1-(1-p_d)e^{-\rho}+o(1)\). An unbounded local decision with one outgoing bit per party, and independent public coins if desired, suffices for the balanced value.
2. The supremal probability of identifying the entire label tends to zero, even with full interaction and the allowed growing bit cap. The same is true for including the true label in any list of size \(\exp(o(d))\).

Since \(q\) is odd, an exactly balanced binary property of uniform \(S\) is not possible: “as close to balanced as possible” means prior bias at most \(1/(2q^d)\). The theorem separates a single specified property from exact label identification. It does not indicate any efficient local decision rule, an exact finite-dimensional optimum, or a conclusion for cryptographic implementations.

## 2. Exact rare-event intensity

Let \(\mathscr L_s\) be the density of a private batch at \(s\) relative to the product full-grid reference from the fixed batch theorem. Under \(P_s\), the law of \(\log\mathscr L_s\) is independent of \(s\) and is the sum of \(d k\) scalar terms \(\ell_b\), where \(\ell_b=\log(f_b/g_1)(E)\), \(E\sim f_b\). By a uniform Taylor expansion, as in the preceding notes,
\[
 E\ell_b=b^2+O_q(b^3),\qquad
 \operatorname{Var}(\ell_b)=2b^2+O_q(b^3),\qquad |\ell_b|\le C_q b.
 \tag{2}
\]
Condition (1) gives \(k b^2\to L\) and \(\Delta\sim2\sqrt{Ld\Lambda}\). For every sequence \(H=o(\sqrt{d/\Lambda})\), we claim
\[
 B\,P_s\bigl(\log\mathscr L_s>d L+H\bigr)\longrightarrow\rho
 \tag{3}
\]
uniformly in \(s\). The following tilted calculation retains the prefactor that a logarithmic moderate-deviation estimate would lose.

Let \(U=\log\mathscr L_s-E\log\mathscr L_s\), \(\sigma^2=\operatorname{Var}(U)=2d k b^2+O(1)\), \(x=dL+H-E\log\mathscr L_s=\Delta+H+O(1)\), \(\theta=x/\sigma^2\), and \(F(\theta)=\log E e^{\theta U}\). By boundedness of the scalar variables and \(dkb^3=O(1)\),
\[
 F(\theta)=\tfrac12\sigma^2\theta^2+O(\theta^3),\quad
 F'(\theta)=\sigma^2\theta+O(\theta^2),\quad
 F''(\theta)=\sigma^2+O(\theta)
\]
uniformly for small positive \(\theta\); these bounds follow from the third centered moment under a one-scalar tilt, uniformly \(O(b^3)\). Under the tilt with density \(e^{\theta U-F(\theta)}\), the \(dk\) scalar variables remain independent with identical distributions. Their centered third absolute moments are \(O(b^3)\) and variances are comparable to \(b^2\). Berry--Esseen therefore gives Kolmogorov error \(O((dk)^{-1/2})\) for \((U-F'(\theta))/\sqrt{F''(\theta)}\) against a standard normal.

Put \(u_0=(x-F'(\theta))/\sqrt{F''(\theta)}=O(\theta^2/\sqrt d)=o(1)\) and \(A=\theta\sqrt{F''(\theta)}\sim\sqrt{2\Lambda}\). Undoing the tilt,
\[
 P(U>x)=e^{F(\theta)-\theta x}
 E_\theta\left[e^{-A(V-u_0)}\mathbf 1_{\{V>u_0\}}\right],
 \qquad V=(U-F'(\theta))/\sqrt{F''(\theta)} .
\]
The bracket as a function of \(V\) has total variation at most 2, so replacing \(V\) by a standard normal changes its expectation by \(O((dk)^{-1/2})=o(\Lambda^{-1/2})\). The normal expectation is
\(A^{-1}\int_0^\infty e^{-w}\phi(u_0+w/A)\,dw\sim(2\pi)^{-1/2}/A\)
by dominated convergence. Also
\[
 F(\theta)-\theta x=-x^2/(2\sigma^2)+o(1)
       =-\Delta^2/(4Ld)+o(1).
\]
For the last equality, changing \(x\) by \(H+O(1)\) costs \(o(1)\) because \(\Delta|H+O(1)|/d=o(1)\); changing \(k b^2=L-\Delta/d\) to \(L\) costs \(O(\Lambda^{3/2}/\sqrt d)=o(1)\). Together these yield
\[
 P(U>x)=(1+o(1))\frac{\exp(-\Delta^2/(4Ld))}{2\sqrt{\pi\Lambda}},
\]
and (1) gives (3). The same limit holds with a non-strict inequality by shifting the raw threshold by an arbitrarily fixed additive amount. Conditional on every \(s\), the number of parties exceeding such a level has law \(\operatorname{Bin}(B,u_d)\), where \(u_d\) is the one-party exceedance probability. It converges to a Poisson random variable of intensity \(\rho\). In particular its mask is independent of \(S\).

## 3. Exact success probability for one property

For the upper bound on any protocol, choose \(H=-(m\log2+4\Lambda)\), which is \(o(\sqrt{d/\Lambda})\) by (1). Condition on the event that no party's true log likelihood exceeds \(dL+H\). The event probability tends to \(e^{-\rho}\) by (3) and does not depend on \(S\). Under this conditioning the batches are again independent conditional on \(S\), with each party's law precisely the normalized clipped law from the fixed batch theorem. Its normalizer \(Z\) tends to one. The positive ideal-projection estimate of that theorem gives
\[
 \lambda_*\le Z^{-1}e^H+O_q(Z^{-2}e^{-\alpha_qd}),
 \tag{4}
\]
uniformly as \(k b^2\to L\); the proper-ideal estimate uses only bounded \(k b^2\). The fully interactive spectral bound with the chosen \(H\) makes the conditional transcript within \(o(1)\) TV of a transcript independent of \(S\): its full-ideal contribution is \(O(e^{-\Lambda})\) after paying \(B2^{m/2}\), and its proper-ideal contribution tends to zero. Thus the conditional success for the specified property is at most its prior majority success \(p_d\) plus \(o(1)\). On the complementary event charge success at most one. This gives at most \(1-(1-p_d)e^{-\rho}+o(1)\).

For the reverse bound use \(H=3\Lambda\), also in the window of (3). For each false label \(s'\), the full unclipped likelihood \(\mathscr L_{s'}\) has expectation at most \(1+O_q(d^{-1})\) under the true batch law, by the proper annihilator ideal calculation in Section 6 of the fixed batch theorem with bounded \(k b^2\). Therefore the probability that any false label in any party has likelihood above \(e^{dL+H}\) is \(O(B^{-2})\), by Markov and a union bound. Each party can send one bit that means “some label above this level disagrees with the prior-majority binary guess”; the referee changes that prior guess if it sees any such bit. Except on the false-positive event, for labels with the majority property it is always correct; for the other labels it is correct exactly when at least one true score exceeds the level, which has probability tending to \(1-e^{-\rho}\). This gives the claimed success. For an asymptotically balanced property one may instead use an independent uniform public bit as the default guess, which gives \(1-\frac12e^{-\rho}+o(1)\) uniformly in the true label. The comparison only asserts existence of an unbounded local bit decision over a finite family of labels, not a way to evaluate it efficiently.

## 4. A blackboard lemma with a bounded number of label-dependent parties

We will need a slight strengthening of Section 2 of the fixed blackboard note. In its notation, suppose a set \(J\) of “marked” parties has arbitrary label-dependent private input laws, with conditional independence of all the party inputs at each label. The other parties obey the centered spectral condition there, with constants \(\lambda_i\) relative to their references \(\nu_i\) and averages \(\bar P_i\). Let \(M_J=\sum_{i\in J} m_i\) be the worst-case total bit cap of the marked parties. Replace only unmarked inputs by independent draws from \(\bar P_i\), keeping \(S\) and all marked input laws unchanged. The joint TV distance between the two \((S,\Pi)\) laws is at most
\[
 2^{M_J}\,\frac{2}{\sqrt2-1}
              \sum_{i\notin J}\sqrt{\lambda_i}(2^{m_i/2}-1).
 \tag{5}
\]

To see this, freeze the public randomness. In the transcript hybrid, keep every marked-party transition at its true conditional law given \((S,\tau)\); the rectangle property guarantees that these transitions are the same whichever laws are used for the independent other inputs. Only replace unmarked transitions. In a prefix already simulated at unmarked slots, its probability at fixed \(s\) has the product of the unmarked averaged local event masses times the product of the marked-party local event masses at \(s\). Discarding the latter product, which is at most one, yields a dominating weight. For every prefix, there is some vector of prescribed bit strings for the marked parties, of total length \(M_J\), extending the marked bits in that prefix. In a protocol with those prescribed bits emitted in local order, without consulting marked inputs, a prefix consistent with them has probability equal to the unmarked product. Thus the preceding dominating weight is at most the sum of these prefix probabilities over the \(2^{M_J}\) scripts. The forced-script protocols have public-dependent scheduling and independent averaged unmarked inputs, so the proof of the original conditional ratio and local tree bound applies for the corresponding unmarked next-bit differences. Grouping by local opportunity yields the bound in that proof, summed over the scripts. The suffix of each hybrid is the same conditional channel given \(S\) and the prefix. This proves (5) after averaging over the public tape. In particular no independence of the label from prefixes containing actual marked bits was assumed.

In the partly simulated experiment of (5), under the uniform prior, a referee guessing a list of length \(D_0\) has success at most \(D_0 2^{M_J}/q^d\). Indeed freeze all unmarked private inputs and the public tape, which are independent of \(S\). The finite vector of marked outgoing bits determines the whole transcript and hence the output list, so at most \(D_0 2^{M_J}\) labels appear in all possible output lists for this freezing. This bound on success is unaffected by how the marked messages were generated or by the dependence of their input laws on \(S\).

## 5. No whole-label identification at finite Poisson intensity

Choose \(K=K_d\to\infty\) so slowly that \(K m\sqrt{\Lambda/d}\to0\), possible by (1), and use the mark event that a party's true score exceeds \(dL+H\) with
\[
 H=-4\Lambda-(2K+1)m\log2 .
\]
This cutoff satisfies the window of (3). Its mask \(J\) is independent of \(S\), and \(P(|J|>K)\to0\) because the expected count remains bounded. Give the mask freely to all parties, which only strengthens them. Conditional on any mask and \(S\), all party inputs are independent; the unmarked laws are the normalized clipped laws with spectrum (4), and the marked laws are arbitrary for the purposes of (5). For \(|J|\le K\), the full-ideal term in (5) is \(O(e^{-\Lambda})\) with this \(H\); indeed it pays at most \(2^{Km}B2^{m/2}e^{H/2}\). The proper-ideal term is \(o(1)\) since \(K m,\Lambda=o(d)\). Hence uniformly over such masks the transcript law is within \(o(1)\) of the partly simulated one. The success there for any list \(D_0=\exp(o(d))\) is at most \(D_0 2^{Km}/q^d=o(1)\), by the preceding lemma. The masks with more than \(K\) marks cost \(o(1)\) additionally. This proves the second assertion.

## 6. Scope and prior methods

The generalized Chernoff tilt with a Berry--Esseen prefactor is classical; the calculation is included to give the exact normalization in (1)–(3), not claimed as new probability theory. The two frozen predecessors already prove the exact proper-ideal spectrum, positive truncation and fully interactive centered contraction away from this window. The contribution here is their use at a finite Poisson rate and the marked-party comparison needed to distinguish a bit from the entire label in the same window. Statistical existence comparisons in the proof have no efficient implementation claim. No deployed inputs, vulnerabilities or actual attack models are considered. The companion checker verifies finite rational probability identities and leading-exponent arithmetic; it is not a numerical verification of the limiting theorem.
