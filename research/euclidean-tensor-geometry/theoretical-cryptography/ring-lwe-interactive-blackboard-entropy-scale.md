# The entropy-scale ring-learning bound under fully interactive blackboard communication

## 1. Ring application and protocol model

The [fixed one-message-per-batch theorem at 9c7c903b1aa999d663b8bc4f5b48ad499beb738e](https://github.com/mxym/math/blob/9c7c903b1aa999d663b8bc4f5b48ad499beb738e/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-batch-communication-entropy-scale.md) uses fixed odd \(q\ge3\), dyadic \(d\), a uniform label \(S\) in \(R=(\mathbb Z/q)[X]/(X^d+1)\), \(b=\beta/d\) for fixed \(\beta>0\), and \(k=\lfloor t/b^2\rfloor\) rows in each party's private batch. All coefficients and responses are private to their own party until that party reports information about them. The \(B\) batches are independent conditional on \(S\). We keep these distributions, but now allow a **fully interactive public blackboard**: a party may write repeatedly at arbitrary interleaved times, depending on its full private batch and all earlier messages. The referee can select the next speaker and request arbitrary instructions based on the public transcript and its own independent randomness, without any bound on local computation or referee memory. Each party writes at most \(m\) bits in total, in the worst case. Speaker selection at any step is a function only of public history and independent public coins, or else its data-dependent part must be counted as communication. The transcript includes the independent coins used for the public schedule. The referee has no other channel for observing any batch. Each party may have its own independent private coins.

**Theorem.** The same bound as in the fixed one-message theorem holds in this model: if \(0<t<\log q\) and
\[
 \limsup_{d\to\infty}\frac{m\log2}{d}
           <\min\{\alpha_q,\log q-t\}, \qquad
 \alpha_q=\lim_{d\to\infty}\frac1d\log\min_{0\ne J\lhd R}|J|,
 \tag{1}
\]
then there are \(c,c'>0\) such that for \(B\le e^{cd}\) the joint law of \(S\) and the entire transcript is within \(e^{-c'd}\) in total variation of a law in which the transcript is independent of uniform \(S\). This gives the same bounds for exact label and balanced-property guessing as before. All returns to a party are queries about the **same** original batch. The result does not apply to a model giving the private coefficient matrices to the referee for free, to unbounded per-party communication, or to unrestricted time complexity.

The comparison at \(t>\log q\), where a full batch already suffices for unrestricted statistical inference, is unchanged. Thus there is no degradation of the sub-threshold range in (1) from allowing repeated interleaved communication. This does not claim optimality of the communication rate in (1). Section 4 separately identifies the sharp leading deficit scale for subexponentially many parties, allowing \(k b^2\to\log q\).

## 2. General centered spectral-to-blackboard bound

Let \(S\) have any fixed finite prior \(\pi\), and let party \(i\)'s private data law given \(s\) be \(P_{i,s}\). Conditional on \(S\), different parties' inputs are independent. For each party fix a probability reference \(\nu_i\) dominating all its observation laws, and suppose for every centered \(h\in L^2(\pi)\) that
\[
 \left\|\mathbb E_s h(s)\frac{dP_{i,s}}{d\nu_i}\right\|^2_{L^2(\nu_i)}
      \le \lambda_i \|h\|_{L^2(\pi)}^2 .
 \tag{2}
\]
A local private coin tape can be included in both \(P_{i,s}\) and \(\nu_i\) with the same independent law, without changing (2). Write \(\bar P_i=\mathbb E_s P_{i,s}\). Let \(\Pi_{\rm ind}\) be the transcript under the same protocol with all party inputs drawn independently from \(\bar P_i\), independently of the actual label. If party \(i\) uses at most \(m_i\) transmitted bits, then
\[
 \operatorname{TV}\bigl(\mathcal L(S,\Pi),\pi\otimes\mathcal L(\Pi_{\rm ind})\bigr)
 \le \frac{2}{\sqrt2-1}\sum_i \sqrt{\lambda_i}\,(2^{m_i/2}-1).
 \tag{3}
\]
No lower bound on any likelihood ratio is required. The reference need not be the averaged experiment. The distinction between \(\bar P_i\) and \(\nu_i\) is used in the proof.

### A conditional-bit difference

Freeze the public tape. At a given public prefix \(\tau\), the set of private inputs consistent with that prefix is a rectangle \(\prod_i E_i(\tau)\): each emitted bit is a deterministic function of the transmitting party's own input (including its private tape) and the already fixed public prefix. Intersecting the conditions from all messages of party \(i\) defines \(E_i(\tau)\). This remains true when speakers are chosen adaptively using the transcript. Thus for a sender \(i\), its next bit's conditional law under fixed \(s\) is the law under \(P_{i,s}\) conditional on \(E=E_i(\tau)\); under the independent experiment use \(\bar P_i\) instead. Use these latter expressions as versions of the conditional distribution at any prefix (including a prefix impossible under some real \(s\)); select an arbitrary bit probability only when the relevant local denominator is zero.

Let \(F\subseteq E\) be the event that the next bit is 1. For any \(D\), (2) by centered Hilbert space duality gives
\[
 \mathbb E_s |P_{i,s}(D)-\bar P_i(D)|^2 \le \lambda_i\,\nu_i(D).
 \tag{4}
\]
For \(\bar P_i(E)>0\) write \(a=P_{i,s}(F)\), \(b=P_{i,s}(E)\), \(\bar a=\bar P_i(F)\), \(\bar b=\bar P_i(E)\), and \(u_s\) for the real conditional probability (arbitrary in \([0,1]\) at \(b=0\)). We have \(a=b u_s\) even at \(b=0\), and
\[
 \bar b\,|u_s-\bar a/\bar b|
       \le |a-\bar a|+|\bar b-b|.
\]
Averaging over \(s\) with its original prior, Cauchy--Schwarz and (4) show that the one-bit total variation at this prefix is at most
\[
       2\sqrt{\lambda_i}\,\frac{\sqrt{\nu_i(E)}}{\bar P_i(E)} .
 \tag{5}
\]
We do **not** evaluate this expectation with the posterior after a real prefix.

### Sum over the private-input tree of the next sender

Put the null-prefix distribution \(\Pi_{\rm ind}\) on the blackboard. For party \(i\) and an index \(r\) between 1 and \(m_i\), consider its sending opportunity just before its \(r\)-th bit, if this bit is ever sent. Freeze all *other* parties' complete private inputs under that independent experiment, as well as the public tape. Now the entire public prefix before this opportunity is determined by the string of the \(r-1\) earlier bits of party \(i\), with a possible early stop; since all other inputs have been fixed, the schedule, every other bit and every request can be reconstructed from that string up to the next transmission from \(i\). The different reachable strings of length \(r-1\) therefore have disjoint local events \(E\) in the private-input space of party \(i\), at most \(2^{r-1}\) such events. For each reachable string with \(\bar P_i(E)>0\), the event of reaching its full prefix under this freezing is exactly \(E\): any input satisfying the local conditions yields the identical global prefix when the other inputs are held fixed.

The unfrozen private input of party \(i\) still has law \(\bar P_i\). Therefore the expectation of the ratio in (5) at this opportunity, with contribution zero if not reached, is exactly the sum over positive-mass local events of \(\sqrt{\nu_i(E)}\). It is bounded uniformly over the frozen inputs by
\[
  \sum_E\sqrt{\nu_i(E)}
       \le \sqrt{\,2^{r-1}\sum_E\nu_i(E)}\le 2^{(r-1)/2}.
 \tag{6}
\]
This is the step that both removes any comparison of \(\bar P_i\) to \(\nu_i\) and pays the square root of the local number of bit strings. A worst-case bound on \(1/\bar P_i(E)\) would not suffice.

### Transcript hybrid

Pad the finite transcript by input-free symbols after termination to a deterministic upper bound \(\sum_i m_i\) on the number of bit opportunities. Compare consecutive hybrids with a null-generated prefix and a suffix generated by the conditional laws at fixed \(S\) under the real experiment. At any changed bit, the null prefix is independent of \(S\), so (5) averages with the original prior as needed. The remaining suffix is a common channel applied to the prefix and \(S\), so it cannot increase TV. These hybrids include the true transcript and the independent transcript as endpoints; conditional laws on impossible prefixes can be chosen as above. Sum the averaged differences, grouped by sender \(i\) and its local opportunity index \(r\). Equations (5)–(6) give
\[
 \sum_i 2\sqrt{\lambda_i}\sum_{r=1}^{m_i}2^{(r-1)/2}
  =\frac{2}{\sqrt2-1}\sum_i\sqrt{\lambda_i}(2^{m_i/2}-1),
\]
proving (3). The same bound holds after averaging over the public tape.

## 3. Insert the entropy-scale batch estimate

For each party independently conditional on \(S\), use the typical clipped batch from Sections 3–4 of the fixed [batch theorem](https://github.com/mxym/math/blob/9c7c903b1aa999d663b8bc4f5b48ad499beb738e/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-batch-communication-entropy-scale.md). Its label-centered spectrum satisfies
\[
 \lambda_i=\lambda_*\le Z^{-1}e^{(t+\eta-\log q)d}
                       +O_q(Z^{-2}e^{-\alpha_q d}), \qquad
 1-Z\le Ce^{-c\eta^2d},
\]
where \(\eta>0\) is fixed and can be chosen small relative to the strict gap in (1). The exact Fourier sectors of the whole batch and the positive proper-ideal cutoff are those of the fixed theorem. Coupling the original and the clipped private inputs at the start costs at most \(B(1-Z)\) in TV, regardless of how often any batch is revisited; then apply (3) to the clipped laws. The result is
\[
 B(1-Z)+\frac{2}{\sqrt2-1}B(2^{m/2}-1)\sqrt{\lambda_*}.
\]
Both terms are exponentially small for \(B\le e^{cd}\) with sufficiently small fixed \(c>0\) by (1). The null comparison is the output of the same protocol with independently averaged **clipped** inputs, and is independent of \(S\). The hard clipping can assign zero density to some outcomes; (3) applies without any artificial positive floor.

## 4. A sharp subexponential-party deficit scale

The same estimates give a sharp leading threshold when the number of interacting parties is subexponential and the per-party batch size approaches the statistical boundary from below. Let \(B=B_d\) be integers with \(\Lambda=\log B\to\infty\) and \(\Lambda=o(d)\), keep \(b=\beta/d\), and let \(k=k_d\) satisfy
\[
 \Delta_d=d\log q-k d b^2,\qquad
 \frac{\Delta_d}{2\sqrt{(\log q)d\Lambda}}\longrightarrow a,\qquad 0<a<\infty.
 \tag{7}
\]
If \(a>1\), the joint real transcript is within \(o(1)\) TV of a transcript independent of the uniform label whenever \(m=o(\Delta_d)\), even with full blackboard interaction. More generally the converse holds if \((\Delta_d-m\log2)/(2\sqrt{(\log q)d\Lambda})\) has limit inferior greater than 1. If \(0<a<1\), then one outgoing bit per party suffices, without computation constraints, to infer any *specified* binary property of the label with error \(o(1)\), using no interaction. In the latter case, if also \(\log d=o(\Lambda)\), the parties can instead identify the whole label with error \(o(1)\). These upper statements are statistical existence comparisons using unbounded local decisions, not efficient estimators. At \(a=1\) no assertion is made.

For the proof, let \(\mathscr L\) denote the true batch likelihood relative to the fixed reference, and \(\ell=\log(f_b/g_1)(E)\) the one-scalar contribution, where \(E\) has density \(f_b\). Under the true label, \(\log\mathscr L\) is the sum of \(d k\) independent copies of \(\ell\), uniformly in that label. The expansions in the fixed batch note give
\[
 \mathbb E\ell=b^2+O_q(b^3),\qquad
 \operatorname{Var}(\ell)=2b^2+O_q(b^3),\qquad |\ell|=O_q(b).
\]
The variance follows directly from \(\ell/b=2\cos(2\pi E)+O_q(b)\), uniformly, and \(f_b=1+O(b)\). Consequently \(\mathbb E\log\mathscr L=k d b^2+O(1)\). For every fixed \(r\in\mathbb R\), Taylor expansion of the log moment-generating function at \(r\sqrt{\Lambda/d}\) gives, with \(U_d=(\log\mathscr L-\mathbb E\log\mathscr L)/\sqrt{d\Lambda}\),
\[
 \frac1\Lambda\log\mathbb E e^{r\Lambda U_d}\ \longrightarrow\ (\log q)\,r^2 .
\]
In detail, the quadratic part is \(r^2\Lambda(kb^2+O(kb^3))\), with \(k b^2\to\log q\). The cubic remainder is bounded by \(C(dk)b^3|r\sqrt{\Lambda/d}|^3=o(\Lambda)\), and the estimates also hold after differentiating on fixed compact \(r\)-intervals (boundedness of \(\ell/b\) gives the same orders). Chernoff bounds then give the upper rate at every fixed \(z>0\). For the lower rate at \(z\), tilt by \(e^{r\Lambda U_d}\) with \(r=(z+\xi)/(2\log q)\), \(\xi>0\). The tilted \(U_d\) has mean \(z+\xi+o(1)\) and variance \(O(1/\Lambda)\) by the differentiated estimates. Its mass between \(z+\xi/2\) and \(z+2\xi\) tends to one; undo the tilt and then take \(\xi\downarrow0\). This yields
\[
 \lim_{d\to\infty}\frac1\Lambda\log\Pr(U_d\ge z+o(1))
       =-\frac{z^2}{4\log q}.
 \tag{8}
\]
The same rate holds with a strict inequality or a non-strict inequality, by comparison at \(z\pm\varepsilon\).

For \(a>1\), choose the hard cutoff
\[
 H_-=d\log q-m\log2-4\Lambda
\]
on \(\log\mathscr L\). Again \(\Lambda=o(\Delta_d)\). Its distance above \(k d b^2\) is \(\Delta_d-m\log2-4\Lambda\), equal to \(\Delta_d(1+o(1))\) if \(m=o(\Delta_d)\). More generally under the stated limit-inferior condition this distance, divided by \(2\sqrt{(\log q)d\Lambda}\), is eventually bounded below by a fixed constant greater than 1. Thus (8) bounds the deleted probability by \(B^{-a^2+o(1)}\) in the first case and by \(B^{-1-\epsilon}\) for some \(\epsilon>0\) in the more general case. The product clipping error \(B(1-Z)\) is \(o(1)\). The positive proper-ideal argument of the fixed batch note holds for any cutoff and all bounded \(k b^2\), giving
\[
 \lambda_*\le Z^{-1} e^{H_--d\log q}+O_q(Z^{-2}e^{-\alpha_qd}).
\]
Inserting this into (3), the full-ideal term costs \(O(e^{-\Lambda})\), and the proper-ideal term is \(o(1)\) because both \(m,\Lambda=o(d)\). This proves the strengthened converse.

For \(a<1\), use the comparison level \(H_+=d\log q+3\Lambda\). Equation (8) says that the true likelihood exceeds this level with probability \(B^{-a^2+o(1)}\), uniformly in \(s\). For any false label, Section 6 of the fixed batch note shows that its likelihood under the true law has expectation at most \(1+O_q(d^{-1})\): the moment is \(W((vR)^\perp)^k\), and the proper-ideal bound is uniform for bounded \(k b^2\). Markov and the union over all false labels and all parties show that any false label exceeds the level anywhere with probability \(O(B^{-2})\). A party can report one bit indicating that a label above the level has the specified property; on the event with no false positives, only a confident true label can trigger it. If the property is false no party reports 1; if it is true the chance all reports are 0 is at most \(\exp(-B^{1-a^2+o(1)})\) by the independence of the batches at fixed \(s\). This is a statistical existence argument only: the local indicator quantifies over all labels and no method for computing it efficiently is provided. For the full-label statement assign disjoint groups of parties to the \(O(d)\) positions of an injective binary encoding of \(s\); each group makes that one-bit comparison, and the same advance error bound and a union bound give \(o(1)\) because \(B^{1-a^2+o(1)}/d\) grows faster than \(\log d\) when \(\log d=o(\Lambda)\).

## 5. Attribution and scope

The fully interactive communication model and conditional-prefix method are prior ideas. In [Steinhardt–Valiant–Wager, COLT 2016, Proposition 3 and Appendix A.1](https://proceedings.mlr.press/v49/steinhardt16.pdf) the proof simulates a multiparty transcript using conditional probability ratios and controls inverse local prefix probability under a uniform statistical-query tolerance. Their Theorem 11 and Lemmas 13–15 address the more restrictive one-message-per-party spectral setting. [Barnes–Han–Ozgur, JMLR 2020, §3 and Appendix C](https://jmlr.org/papers/v21/19-737.html) use the analogous product factorization for fully interactive Fisher-information bounds; [Acharya–Canonne–Liu–Sun–Tyagi, §I-C](https://ece.iisc.ac.in/~htyagi/papers/ACLST21.pdf) explicitly distinguish sequential access from fully interactive revisits. The argument here is a centered spectral refinement of the conditional-prefix method: include \(\sqrt{\nu_i(E)}\) from (4), take the exact null-prefix average via the local binary tree, and therefore pay \(2^{m_i/2}\) while retaining the clipped wrapped-ring spectral bound. We do not claim optimality of the general inequality (3), novelty of the public-blackboard model, or any implications for a concrete scheme.

The companion verifier checks the rectangle, frozen local events, low-mass and conditional-law cases for finite rational protocols. It does not use real cryptographic systems or attempt to infer a deployed secret.
