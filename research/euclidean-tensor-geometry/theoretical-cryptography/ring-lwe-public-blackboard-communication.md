# Fully public coefficients with arbitrarily interleaved batch communication

The fresh-batch bound with public ring coefficients required that a party was visited only once. We remove that restriction at the same squared accumulation scale for outgoing bits. The key is that one can repair the averaged response density by a tiny common addition, then control a stopped Hellinger sum at *null* transcript prefixes. Repeated access to the same batch is allowed; no local computational bound is used.

## 1. Ring statement

Fix an odd prime \(q\), \(0<t<\log q\), \(\beta>0\), dyadic \(d\), and \(R=\mathbf F_q[X]/(X^d+1)\). As in the [fully public one-visit result](https://github.com/mxym/math/blob/2edde6b2a974ba3a8ed97f8bb6aed08315e34308/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-public-design-communication.md), let \(b=\beta/d\), \(k=\lfloor t/b^2\rfloor\), and give each party \(k\) independent uniform ring rows \(A_i\) and the corresponding noisy responses with a uniform common label \(S\in R\); per scalar coordinate the wrapped noise is \(f_b(y)=\sum_h b^{h^2}e^{2\pi i h y}\). All parties' coefficients are public **before** any communication; the responses remain private to their party. Write \(\nu\) for the product of the scalar grid average \(g_b=q^{-1}\sum_a f_b(\cdot-a/q)\).

Allow a fully interactive public transcript: any party can be revisited at arbitrary interleaved times about its original private batch. At each step the speaker and whether it is queried are determined by public information and independent public randomness or are charged as communication if privately selected. Party \(i\) writes at most \(m_i\) bits in total, in the worst case. Local computation, private independent coins, and public computation are unrestricted. Write \(P\) for the joint law of \(S\), all designs and the transcript, and \(Q\) for the experiment with the same public design and transcript rules but with all private response batches replaced by independent \(\nu\), independent of \(S\).

There are constants \(C,c>0\) such that
\[
 \operatorname{TV}(P,Q)
 \le C P_{\rm act} e^{-cd} + C\sqrt{D_d}+C D_d,
 \qquad D_d=(1+o(1))b^2\sum_i(2^{m_i}-1),                    \tag{1}
\]
where \(P_{\rm act}\) is the number of parties allowed at least one outgoing bit. In particular \(b^2\sum_i(2^{m_i}-1)=o(1)\) implies that the whole transcript and the uniform label become asymptotically independent, despite arbitrary revisits. The same regime is sufficient in the previous fresh-batch theorem. Neither statement establishes necessity of the budget condition or a bound on general computation.

## 2. A Hellinger accumulation lemma for a full public transcript

Consider first fixed public data and a finite label prior \(\pi\). At fixed label \(s\), party \(i\)'s private input has law \(P_{i,s}\), independently across parties. Let \(\bar P_i=\mathbb E_{s\sim\pi}P_{i,s}\) and suppose there is a reference probability \(\nu_i\) and constants \(\lambda_i\ge0\), \(a>0\), such that
\[
 \bar P_i\ge a\nu_i,\qquad
 \mathbb E_s |P_{i,s}(E)-\bar P_i(E)|^2\le \lambda_i\nu_i(E)
                   \quad\text{for every measurable }E.        \tag{2}
\]
We compare the transcript to that generated from independent \(\bar P_i\)'s and an independent label. This time call those joint laws \(P^{\mathrm{tr}}\) and \(Q^{\mathrm{tr}}\).

Fix the public tape; private independent tapes can be included in the private inputs without changing (2) when it is supplied by an \(L^2\) operator bound as below. For a fixed public prefix, the event of reaching it is a product rectangle in the private inputs: each earlier message restricts only its own sender after the public prefix has been fixed. This remains true for arbitrary selection of future speakers from the public transcript. If party \(i\) is next, let \(E\) be its local prefix event and \(E_0,E_1\) the two subevents for its next bit. The real conditional bit law at fixed \(s\) has probabilities \(p_j/p\), with \(p_j=P_{i,s}(E_j)\), \(p=\sum_jp_j\); the null uses \(q_j/q_E\), \(q_j=\bar P_i(E_j)\), \(q_E=\sum_jq_j\). These are versions on every positive-null prefix; on a real zero prefix use any conditional supported on its null support. A zero \(q_j\) implies that \(p_j=0\) at all positive-prior labels, so a child with \(q_j=0\) need not be counted.

Write \(h^2\) for squared Hellinger distance without the \(1/2\) normalization. At every positive-null prefix,
\[
 q_E\, h^2((p_j/p)_j,(q_j/q_E)_j)
      \le 4\sum_j(\sqrt{p_j}-\sqrt{q_j})^2 .                   \tag{3}
\]
For \(p>0\), apply the triangle inequality between the two vectors normalized by their own square-root totals, first using common denominator \(\sqrt{q_E}\); the reverse triangle inequality controls the normalization difference. For \(p=0\), the right-hand side is \(4q_E\) and \(h^2\le2\). Since \((\sqrt p-\sqrt q)^2\le(p-q)^2/q\) at \(q>0\), (2) yields
\[
 q_E\,\mathbb E_s h^2((p_j/p)_j,(q_j/q_E)_j)\le 8\lambda_i/a.    \tag{4}
\]
The expectation is with the **original** label prior, never with a posterior conditioned on the real prefix.

Now average over null prefixes. For fixed \(i\) and its \(r\)-th bit opportunity, freeze the complete inputs of the other parties under the independent null and freeze the public tape. Before this opportunity, a string of the \(r-1\) bits already sent by \(i\) determines the entire global prefix if reached: all other parties' replies and speaker selections are already determined given the history. There are at most \(2^{r-1}\) such strings and the reached local events are disjoint. Each has null mass \(q_E\). Hence (4) bounds the expected squared Hellinger contribution of this opportunity by \((8/a)2^{r-1}\lambda_i\), with zero contribution if not reached. Summing over parties and all opportunities shows
\[
 \mathcal E:=\sum_{\text{steps}}\mathbb E_{\pi,Q\ {\rm prefix}}
         h^2(\text{real conditional},\text{null conditional})
 \le (8/a)\sum_i(2^{m_i}-1)\lambda_i.                           \tag{5}
\]
In this formula the \(Q\) prefix law is exactly the null law. It has independent label even though the prefix itself is highly interactive.

One must still pass from *null* prefix energy to a whole-transcript comparison. Pad to a fixed finite number of steps with input-free bits. For each joint label and prefix, let \(r_s(\tau)=P^{\rm tr}(\tau\mid s)/Q^{\rm tr}(\tau)\). Real transcript probabilities are absolutely continuous with respect to null, because source inputs at fixed \(s\) are absolutely continuous with respect to their finite-label averages. Define \(P'\) by following the real conditionals until the ratio first exceeds 2, and then following the null conditionals for the remaining steps. The ratio of \(P'\) to \(Q^{\rm tr}\) equals the real ratio until stopping and stays fixed at the stopping ratio along each stopped path. The construction is a device for comparing laws, not a change to what any real party sees or knows.

The exact Hellinger affinity chain for finite transcripts sums the conditional \(h^2\) with prefix weight \(\sqrt{P'(\tau,s)Q^{\rm tr}(\tau,s)}\); it follows by subtracting successive prefix affinities. After stopping there is no local difference, and on active prefixes the weight is at most \(\sqrt2\) times the null weight. Thus
\[
 h^2(P',Q^{\rm tr})\le\sqrt2\,\mathcal E .
\]
The chance of stopping is the same under \(P^{\rm tr}\) and \(P'\), by coupling their transitions before stopping. Under \(P'\), on a stopped final path the ratio \(r\) is \(>2\); there \(r\le12(\sqrt r-1)^2\). This gives stopping probability at most \(12h^2(P',Q^{\rm tr})\), by integration under \(Q^{\rm tr}\). Therefore
\[
 \operatorname{TV}(P^{\rm tr},Q^{\rm tr})
       \le 12\sqrt2\,\mathcal E + 2^{1/4}\sqrt{\mathcal E}.
                                                               \tag{6}
\]
Unlike a step-by-step TV hybrid, (6) pays the square root of the accumulated local energy. Conditioning on fixed public data and then averaging is legitimate because the null and real share those data. The same proof works with independent public coins; private tapes enlarge the rectangles but do not add new channel inputs correlated with the label.

## 3. Repairing the mean density without losing the spectral rate

For one public batch with design \(A\), use the positive smooth truncation \(U\le L\) from the linked [public-design spectral theorem, §§2–4](https://github.com/mxym/math/blob/2edde6b2a974ba3a8ed97f8bb6aed08315e34308/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-public-design-communication.md). Here \(L(y)=\prod_j f_b(y_j)/g_b(y_j)\), \(U_s(y)=U(y-As/q)\), \(Z=\int U\,d\nu\), and \(m\) is the average of \(U\) over the full independent response-grid shift group. The theorem supplies
\[
 1-Z\le e^{-c d},\quad 0\le m\le1,\quad
 \|U\|_2^2\le e^{Hd}\ (H<\log q),\quad
 \mathbb E_A\lambda(A,U)=(1+o(1))b^2 .
\]
In its notation \(\lambda(A,U)\) is the squared operator norm from label \(L^2\) to response \(L^2(\nu)\) of \(h\mapsto\mathbb E_s h(s)(U_s-m)\). For any fixed \(A\), replacing \(m\) by \(\bar U_A=\mathbb E_s U_s\) can only decrease the norm: it is composition by projection onto mean-zero label functions.

We also need that the **constant-label** output is exponentially close to the fixed response reference in expected \(L^1\), not just bounded by the \(b^2\) largest spectral group. If \(\Gamma_w\) denotes the squared norm of the \(w\)-sector of \(U\), the exact phase decomposition gives
\[
 \|\bar U_A-m\|_2^2
  =\sum_{w\ne0:\ \sum_i\overline A_i w_i=0}\Gamma_w .
\]
For each word \(w\), let \(J=\sum_i w_i R\). The zero probability is \(1/|J|\) for \(w\ne0\). Full-ideal contributions in expectation are at most \(e^{Hd}/q^d=e^{-\Omega(d)}\). For any proper nonzero ideal \(J\), the projection onto \(J^k\) in the residue domain is positive, because it averages over \((J^\perp)^k\) grid shifts. Since \(0\le U\le L\), this gives
\[
 \sum_{w\in J^k}\Gamma_w\le
 \left(\sum_{v\in J}\prod_j \tau_{v_j}\right)^k,
\]
where \(\tau_0=1,\ \tau_{\pm1}=b^2+O(b^8)\) and the other \(\tau\)'s are \(O(b^8)\) from the product density. No signed monomial or binomial is in \(J\), since they are units in the odd dyadic ring (every residue root has order \(2d\)). Thus the right-hand side is
\((1+O(db^8+d^3b^6))^k=1+O(d^{-1})\).
A nonzero ideal has cardinality \(e^{\Omega(d)}\), and the number of ideals is bounded at fixed \(q\): the CRT factor degrees \(\operatorname{ord}_{2d}(q)\) grow proportionally to \(d\), with no multiplicities in odd characteristic. Summing over proper nonzero ideals gives \(e^{-\Omega(d)}\), as required. Finally \(\int(1-m)=1-Z\) and \(m\le1\). Hence
\[
 \mathbb E_A\|\bar U_A-1\|_1\le e^{-c'd}.                        \tag{7}
\]

Add the same repair \(r_A(y)=(1-\bar U_A(y))_+\) to every label's subdensity, and normalize:
\[
 L'_{A,s}=\frac{U_s+r_A}{Z+\int r_A\,d\nu}.
\]
The denominator is \(\int\max(\bar U_A,1)\,d\nu\), between 1 and 2. Their mean density is pointwise at least \(1/2\), and the distance of each repaired density to \(L(y-As/q)\) in \(L^1(\nu)\) is at most \(2(1-Z+\int r_A)\) uniformly in \(s\). This follows by comparing before normalization and then paying the difference of its mass from 1. In expectation over \(A\) it is exponentially small by (7). The mean repaired density is also exponentially close in expected \(L^1\) to 1 by (7) and the same repair bound. Importantly the common addition changes no centered term, and normalization by at least 1 cannot increase the centered spectral norm.

For fixed design and any event \(E\), duality of that centered operator produces
\(\mathbb E_s |P'_{A,s}(E)-\bar P'_A(E)|^2\le\lambda(A,U)\nu(E)\).
Thus (2) holds with \(a=1/2\). For private coins, replace the event indicator by its conditional probability given the response; its squared norm is at most its mean, giving the same inequality on the product of the reference and the coin law. No floor uniform in the original planted label density is used.

## 4. Apply the full-transcript lemma

Condition on all public designs, couple each active party's actual private input to its repaired law at the outset, and apply (5)–(6) to the independent product of repaired laws conditional on the label. The cost of this initial coupling, averaged over designs and label, is at most \(O(P_{\rm act}e^{-c d})\) by the uniform-label repair bound. This holds even when the repaired party is subsequently queried many times, since its entire input was coupled once. The lemma gives conditional energy at most \(16\sum_i(2^{m_i}-1)\lambda(A_i,U)\); average and use Jensen for the square root. Finally couple the independent null mean-repaired inputs to independent \(\nu\) at the same expected exponential per-party cost. These null inputs are independent of the label by construction, and the protocol is a common channel in the two null experiments. This proves (1).

All private inputs and local conditional likelihoods are used only for the information-theoretic comparison. The conclusion assumes fixed worst-case outgoing budgets and that the public schedule has no free privately chosen side channel. It does not analyze the converse regime, quantum communication, ordinary unrestricted sample access, or computational time.

## 5. Prior and distinction

[Steinhardt–Valiant–Wager, COLT 2016](https://proceedings.mlr.press/v49/steinhardt16.pdf), especially the conditional-prefix approach, and [Acharya–Canonne–Liu–Sun–Tyagi](https://arxiv.org/abs/2007.10976) give earlier interactive inference and communication lower-bound methods; sequential interactivity with fresh users is different from revisiting an old one. The earlier [private-coefficient blackboard proof](https://github.com/mxym/math/blob/62d53dfd990045d60be8a89f6272ca5c23f9d1db/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-interactive-blackboard-entropy-scale.md) uses the same rectangle counting but a linear sum of per-opportunity TV costs. That is effective at an exponentially small private-design spectral scale. For fully public coefficients that sum would give only a weaker range. The new ingredients here are the exponentially cheap conditional-mean repair, and the combination of squared local Hellinger cost with stopped accumulation under the null, removing the freshness condition without degrading the sufficient scale. The public conditional spectral estimate itself is from the linked previous result.
