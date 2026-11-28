# Entanglement-assisted one-visit communication limits for classical ring-learning batches

## 1. Model and results

Use the classical wrapped-Gaussian private batches from the
[fixed batch theorem at 9c7c903b1aa999d663b8bc4f5b48ad499beb738e](https://github.com/mxym/math/blob/9c7c903b1aa999d663b8bc4f5b48ad499beb738e/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-batch-communication-entropy-scale.md). Thus \(q\ge3\) is fixed and odd, \(d\) grows through powers of two, \(S\) is uniform in \(R=(\mathbb Z/q)[X]/(X^d+1)\), \(b=\beta/d\) with \(\beta>0\) fixed, and each party receives \(k\) complete classical rows, coefficients included. Batches are independent conditional on \(S\).

In this note the \(B\) parties and a referee can share an arbitrary finite-dimensional entangled state independent of the label and all samples. In a fixed order each party is contacted once: the referee may send an arbitrary quantum or classical question and the party returns a hybrid message of at most \(c\) classical bits and \(r\) qubits. It can use its whole classical batch and local quantum state at that turn; no classical batch is accessed earlier. There is no later contact with that party, and its unsent workspace is not subsequently used. The returned registers have fixed public dimensions bounded by the caps; any data-dependent length information would have to be included in the returned classical register. Except for these outward messages no private batch is accessible to the referee. The referee may keep unlimited quantum side information and perform arbitrary operations and measurements. Public randomness can be included in that state. Write
\[
 m_{\rm e}=c+2r,\qquad \Gamma=2^{m_{\rm e}}.
\]

**Theorem.** The following hold in this one-visit model.
1. If \(k=\lfloor t/b^2\rfloor\) with \(0<t<\log q\) and
   \[
   \limsup_{d\to\infty} \frac{m_{\rm e}\log 2}{d}
             <\min\{\alpha_q,\log q-t\},\qquad
   \alpha_q=\lim_{d\to\infty}d^{-1}\log\min_{0\ne J\lhd R}|J|,
   \]
   then exponentially many parties (with sufficiently small exponent) still give a final referee system exponentially close in trace distance to one independent of \(S\).
2. The precise
   [Poisson critical window at 43e3b8e849b099ac5eb10b924b6944f1ecaabcd4](https://github.com/mxym/math/blob/43e3b8e849b099ac5eb10b924b6944f1ecaabcd4/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-batch-poisson-critical-window.md)
   continues to hold with \(m_{\rm e}\) in place of the classical bit cap. In full, write \(L=\log q\), \(\Lambda=\log B\), \(\Delta=dL-kdb^2>0\) and suppose
   \[
    \Lambda\to\infty,\quad \Lambda=o(d^{1/3}),\quad
    m_{\rm e}\sqrt{\Lambda/d}\to0,\quad
    \Delta^2/(4Ld)-\Lambda+\tfrac12\log\Lambda\to a\in\mathbb R.
   \]
   The optimal averaged success for a specified binary property with prior majority success \(p_d\) is \(1-(1-p_d)e^{-\rho}+o(1)\), \(\rho=e^{-a}/(2\sqrt\pi)\), provided at least one transmitted bit or qubit is allowed. In contrast, including the exact label in a list of size \(\exp(o(d))\) has success \(o(1)\). The upper probability for the binary property is attained by the purely classical, statistically unrestricted one-bit comparisons in the fixed note. No efficient way of evaluating those decisions is asserted.

With product local quantum initialization conditional on shared classical coins and with classical questions only, the same proof uses \(m_{\rm e}=c+r\). These bounds do not address protocols that revisit a party, a referee that sees coefficients for free, coherent access to **input** samples, or unrestricted algorithms. Quantum messages are generated from already **classical** samples; their availability does not give an oracle for an unknown quantum state.

## 2. Sending bounded registers after a classical observation

We use the same general centered spectral condition as in the blackboard theorem. For observation laws \(P_s\ll\nu\) at a finite prior \(\pi\), suppose
\[
 \left\|\mathbb E_s h(s)\,\frac{dP_s}{d\nu}\right\|_{L^2(\nu)}^2
           \le\lambda\|h\|_{L^2(\pi)}^2
 \quad\text{for }\mathbb E_s h(s)=0.
 \tag{1}
\]
Write \(\bar P=\mathbb E_s P_s\). Include all retained systems, including those of unvisited parties, in a global state before the visit. At a fixed state \(\omega\) independent of \(s\), let \(\Sigma(x)\) be the global output after processing observation \(x\), consisting of the new transmitted registers \(C,Q\) and all outside registers \(F\). The visited party's unsent local workspace is discarded permanently. The outgoing register \(C\) is classical of dimension \(C_0\le2^c\); the quantum register \(Q\) has dimension \(Q_0\le2^r\). By no signaling, \(\Sigma(x)_F=\omega'_F\) is independent of \(x\): first the referee performs its observation-independent operation sending the question, and then the party's instrument is trace preserving once the message is disregarded. The marginal \(\omega'_F\) includes all registers outside that local operation, hence any purifying auxiliary registers can be retained as well.

Put
\[
 \tau=(I_C/C_0)\otimes(I_Q/Q_0)\otimes\omega'_F .
\]
For every \(x\),
\[
 0\le\Sigma(x)\le C_0 Q_0^2\,\tau .
 \tag{2}
\]
In fact in each diagonal \(C\)-block \(\Sigma_c\), pinching in a basis of \(Q\) gives
\(\Sigma_c\le Q_0\sum_j |j\rangle\langle j|\otimes(\Sigma_c)_{jj}\).
This follows by Cauchy--Schwarz for the quadratic form of a positive block matrix. Each positive block \((\Sigma_c)_{jj}\) is at most \(\omega'_F\), since the sum of all these blocks is \(\omega'_F\). This proves (2). In the unassisted classical-question model, condition on the classical question (and freeze shared classical coins). Conditional on that question the message is prepared without any quantum share of the outside state, so its density operator is at most \(I_{C Q}\) and (2) instead has factor \(C_0 Q_0\). This product claim continues to hold on any purification of the reference input, since no quantum sender share is present and the question is classical.

Let \(\kappa_0=C_0 Q_0^2\) in the assisted case, or \(C_0 Q_0\) in the unassisted one. We claim, at the fixed input state \(\omega\),
\[
 \frac12\mathbb E_s\left\|\mathbb E_{x\sim P_s}\Sigma(x)
                         -\mathbb E_{x\sim\bar P}\Sigma(x)\right\|_1
  \le \tfrac12\sqrt{\lambda\kappa_0}.
 \tag{3}
\]
All operators can be restricted to the support of \(\tau\) by (2). By duality (1) says a scalar test \(f(x)\) has centered response variance at most \(\lambda\int |f|^2d\nu\); the complex case follows by applying it to the real and imaginary parts. Apply this entrywise to \(\tau^{-1/2}\Sigma(x)\). The joint mean squared Hilbert--Schmidt norm of the weighted difference \(\tau^{-1/2}\Delta_s\) is then bounded by
\[
 \lambda\int \operatorname{Tr}\!\big(\Sigma(x)\tau^{-1}\Sigma(x)\big)d\nu(x)
 \le \lambda\kappa_0 .
\]
For the last step, \(\tau^{-1/2}\Sigma(x)\tau^{-1/2}\le\kappa_0 I\) implies
\(\Sigma(x)\tau^{-1}\Sigma(x)\le\kappa_0\Sigma(x)\) by squaring the positive conjugated matrix. Finally
\(\|\Delta_s\|_1\le\|\tau^{1/2}\|_{\rm HS}\|\tau^{-1/2}\Delta_s\|_{\rm HS}
=\|\tau^{-1/2}\Delta_s\|_{\rm HS}\).
Apply Cauchy--Schwarz in \(s\) to get (3). In particular (3) is independent of the dimension, rank or condition number of \(\omega'_F\).

## 3. Sequential and marked hybrid bounds

At each visit the party's classical batch is fresh relative to all prior quantum operations conditional on \(s\): only earlier parties' batches have been accessed. Its marginal state can depend on earlier entangled operations, but the current classical batch is independent of that state at fixed \(s\). Its observation-dependent instrument can therefore be averaged into a quantum channel using \(P_s\), or using \(\bar P\) for the comparison.

First replace every party's inputs by independent draws from \(\bar P\). A hybrid with independent-prior prefix and real conditional suffix permits (3) at each changed visit, since its global pre-visit state is then independent of \(S\). All later operations, including any questions, are common channels conditional on \(S\); trace distance is contractive. The trace distance between the joint final classical label and all remaining registers is at most \(\frac12 B\sqrt{\Gamma\lambda}\) for a homogeneous bound.

For the critical window, we also need a whole set \(J\) of **marked** visits whose actual local input laws may depend arbitrarily on \(s\) and do not satisfy (1). Again inputs are independent across parties conditional on \(s\) and on the prescribed mask. Compare retaining all these inputs but replacing the other (unmarked) inputs by independent draws from \(\bar P\). Let \(\Gamma_i\) be the domination factor in (2) for that visit, \(\Gamma_J=\prod_{i\in J}\Gamma_i\). Then:
* the joint final trace distance in this partially replaced comparison is at most
  \[
     \frac12\Gamma_J\sum_{i\notin J}\sqrt{\lambda_i\Gamma_i};
     \tag{4}
  \]
* in the partially replaced process, the final state conditional on \(s\) is bounded above in positive-semidefinite order by \(\Gamma_J\) times one fixed normalized state independent of \(s\).

Here is the argument, which accounts for noncommuting label-dependent side information. For the partly replaced prefix, define a second **dummy reference process**: at each marked turn execute the referee's preparation of its question, forget that visited party's registers and put a maximally mixed returned register in their place. At unmarked turns use the averaged observation law as before. This reference is independent of \(s\). At any prefix ending after marked visits \(J'\), the partly replaced state \(\omega_s\) is bounded by \(\kappa\omega\), where \(\omega\) is the dummy reference state and \(\kappa=\prod_{i\in J'}\Gamma_i\). This follows inductively: unmarked common channels preserve the bound, and for a marked turn the conditional real instrument applied to a positive state is dominated by \(\Gamma_i\) times the corresponding dummy channel on that same state, by (2). The no-signaling marginal \(\omega'_F\) makes the dummy operation a genuine channel independent of the batch and label. This proves the second assertion after all visits.

For the changed unmarked turn in the hybrid, the pre-visit state has exactly the bound \(\omega_s\le\kappa\omega\). The inequality (3) alone cannot be applied to \(\omega_s\), because it may already be correlated with the label. Purify the reference \(\omega\), writing \(|\Omega\rangle=\sum_j\sqrt{w_j}|j\,j\rangle\) in an eigenbasis. On the purifying system the effect
\[
 M_s=\kappa^{-1}(\omega^{-1/2}\omega_s\omega^{-1/2})^{\mathsf T}
\]
is between 0 and identity. Applying its associated effect and tracing the purification leaves the subnormalized state \(\omega_s/\kappa\) on the input. To see this directly, choosing the \(j,l\) term of the expansion of \(|\Omega\rangle\langle\Omega|\) contributes \(\sqrt{w_jw_l}\langle l|M_s|j\rangle\), exactly the required entry. The effect acts on a separate register from every real turn, so it commutes with the actual and the averaged turn. Apply (3) at the label-independent purified reference, retaining the purifier among \(F\), and then apply the label-controlled effects. Trace-nonincreasing completely positive maps contract the trace norm of a Hermitian difference (for example, extend the map with a failure flag). This gives at most \(\kappa\sqrt{\lambda_i\Gamma_i}/2\) for the changed unmarked visit. Subsequent conditional channels are again common. Summing and using \(\kappa\le\Gamma_J\) proves (4). Importantly, simply averaging a bound under an assumed independent label after a real marked turn would not give this argument.

For a uniform label with \(N\) possibilities, positive-semidefinite domination at the end makes the success of a list of size \(D_0\) at most \(D_0\Gamma_J/N\) in the partly replaced process: test the joint cq states with the positive event that the output list contains the label. The dummy state's label is independent of its output, so that state's success is at most \(D_0/N\).

## 4. Applying the ring spectrum and the Poisson limits

For the first assertion, use the hard clipping in the fixed batch theorem. Its product input error is at most \(B(1-Z)\) in TV, hence also in trace distance after all quantum operations. The centered parameter is
\(\lambda_*\le Z^{-1}e^{(t+\eta-\log q)d}+O_q(Z^{-2}e^{-\alpha_qd})\)
with \(1-Z\le Ce^{-c'\eta^2d}\) for every sufficiently small fixed \(\eta>0\). The one-visit hybrid costs at most \(\frac12 B \sqrt{2^{m_{\rm e}}\lambda_*}\). Choose \(\eta\) smaller than the strict margin in the rate, then choose the exponent of \(B\) small enough to pay both terms.

For the binary-property converse in the critical window, mark any party whose true score exceeds \(dL+H\) with \(H=-4\Lambda-m_{\rm e}\log 2\). This satisfies \(H=o(\sqrt{d/\Lambda})\). The probability of no mark tends to \(e^{-\rho}\) and the mark mask is independent of \(S\), by the fixed Poisson theorem (its distribution depends only on the classical samples). Conditional on no marks, all parties have the clipped law and \(\lambda_*\le Z^{-1}e^H+O_q(Z^{-2}e^{-\alpha_qd})\). The one-visit hybrid makes the referee's state independent up to trace error \(o(1)\) even with the entanglement. Thus on that event success is at most \(p_d+o(1)\), while outside it success is at most one. The reverse inequality follows from the fixed Poisson theorem's unbounded classical one-bit statistical comparison; a single qubit, if used instead of a bit, can carry an ordinary binary report in an orthogonal basis.

For the exact-label converse, choose \(K_d\to\infty\) slowly with \(K_d m_{\rm e}\sqrt{\Lambda/d}\to0\) and use \(H=-4\Lambda-(2K_d+1)m_{\rm e}\log 2\). The mark count still converges to the same Poisson law and exceeds \(K_d\) with probability \(o(1)\). Supply the mark mask for free. Conditional on it and \(S\) the party inputs are still independent; if it has at most \(K_d\) marked parties, apply (4) with \(\Gamma_J\le 2^{K_d m_{\rm e}}\). The full-ideal term in the error is \(O(e^{-\Lambda})\) by the choice of \(H\); the proper-ideal term remains \(o(1)\) since \(K_d m_{\rm e},\Lambda=o(d)\). In the partly replaced process, the domination bound is at most \(\Gamma_J\) relative to one state independent of \(S\), so the list success is at most \(\exp(o(d))\,2^{K_d m_{\rm e}}/q^d=o(1)\). This is uniform over masks with at most \(K_d\) marks and completes the proof.

## 5. Context and limitations

[Chen–Doosti–Sweke–Wadhwa, arXiv:2609.08864v1, Definition 1.1](https://arxiv.org/html/2609.08864v1) and [Doosti–Sweke–Wadhwa, arXiv:2604.05962](https://arxiv.org/abs/2604.05962) study distributed inference from copies of an unknown **quantum input state** and state certification. The present task takes classical batch inputs, does not solve their testing problems, and allows one question before each bounded response with arbitrary prior multipartite entanglement. The two-qubit-information factor in (2) is familiar from entanglement-assisted communication and leakage; see [Nayak–Salzman](https://doi.org/10.1145/1120582.1120587) and [Lai–Chung](https://arxiv.org/abs/1809.10694). The purification calculation is a standard steering identity in the spirit of [Hughston–Jozsa–Wootters](https://doi.org/10.1016/0375-9601(93)90880-9), not a new quantum primitive. What is used here is the centered ideal-spectrum contraction with this reference-weighted dimension bound, including its validity under the small set of genuinely label-dependent quantum visits in the critical window.

These are bounds for an abstract access and communication model. They give no efficient algorithm, no estimate of deployed Ring-LWE hardness, and no conclusion about coherent data access or repeated contact with one party. The accompanying verifier tests exact finite matrix inequalities and conditional-state constructions, not a particular cryptographic system or the asymptotic proofs.
