# First-cover tags give a relative logarithmic power for pointwise small-radical parity

This replaces the old Cauchy–Schwarz unmarking loss, rather than increasing its number of independent marks. It uses the existing small-radical bounded-residual reflected Type II estimate and ordinary true-prime Bombieri–Vinogradov. It does **not** pay the linear \(\log P\) factor on the most difficult channel of the signed Goldbach kernel.

## 1. Statement

Fix \(B,C>0\), \(0<\delta<.1\), a fixed nondegenerate compact \(J\subset(0,1)\), a sufficiently large prescribed even \(P\) with \(\operatorname{rad}(P)\le(\log P)^B\), and \(I=PJ\). Put \(L=\log P\), \(y=\exp(L^\delta)\), and as in [the smooth-profile theorem](SmallRadicalSmoothProfileParity.md) decompose \(m=a_y(m)b_y(m)\). Let \(\nu_y\) be the true-prime CRT profile model: for every prime \(\ell\le y,\ell\nmid P\), the valuation is zero with probability \(1-1/(\ell-1)\) and \(k\ge1\) with probability \(\ell^{-k}\), all independently; primes dividing \(P\) are absent. For every \(A>0\) and real or complex \(F\) with \(|F|\le L^C\), uniformly in \(P\) and \(F\),
\[
\left|\sum_{\substack{p\in I\\p\ {\rm prime}}}(\log p)
       F(a_y(P-p))\lambda(b_y(P-p))\right|
\ll_{A,B,C,J,\delta} P\mathbb E_{\nu_y}|F|\,L^{-1/200}+ P L^{-A}.
\tag{1}
\]
For instance \(F=1_{\{a_y=1\}}\) gives the old rough-Liouville term with a fixed power of \(L\) relative saving, and choosing profile signs gives its weighted total-variation version. Multiplying by the fixed profile factor \(\lambda(a_y)\) also covers the full Liouville sign. On these layers the replacement of \(\lambda(b_y)\) by \(\mu(b_y)\) costs \(O(PL^{C+1}/y)\), by counting all squareful rough parts before imposing the prime. No range \(L^{-1+\delta}\) is claimed.

## 2. Standalone marked and unsigned profile tools at the larger cutoff

Put \(Y_*=\exp(2L^{.2})\). Two versions of the earlier proof are needed; distinguish the *unsigned* one from the old parity theorem.

**Unsigned profile mass at \(Y_*\).** For every function \(D(a)\) on complete \(Y_*\)-smooth parts, \(0\le D\le L^{C'}\) for a fixed \(C'\), even with all its constraints depending on \(P\),
\[
\sum_{p\in I\ {\rm prime}}(\log p)D(a_{Y_*}(P-p))
=|I|\mathbb E_{\nu_{Y_*}}D+O_M(PL^{-M})
\tag{2}
\]
for any fixed \(M>0\), where \(\nu_{Y_*}\) uses the same local law through \(Y_*\). This invokes no assertion about small-radical parity at \(\delta=.2\) and no marked variance. The proof is precisely the unsigned use of the profile argument: truncate \(a\le\exp(L^\kappa)\) with fixed \(.2<\kappa<1\) by Rankin with \(s=1/\log Y_*\). Both model and actual tails cost \(PL^{O(1)}\exp(-c L^{\kappa-.2})\), counting all integer multiples for the latter. Check exact \(a\) by two Bonferroni polynomials through \(\lfloor L^{.1}\rfloor\) or one more factors. The true modulus is \(a e\), where \(e\) divides \((P-p)/a\); it is \(P^{o(1)}\) and coprime to \(P\). Shared prime factors between \(a,e\) multiply the totient at that prime by \(\ell\), not \(\ell-1\); that gives the stated valuation law. For the full grouped modulus \(q=a e\) there are at most \(\tau(q)\) terms, because \(e\) determines \(a\). Pay this by ordinary BV with arbitrary additional log saving, \(\tau(q)^2\le\tau_4(q)\), \(\sum_{q\le P}\tau_4(q)/q\ll L^4\), and the crude error \(E_q\ll PL/q\). The model's truncation errors are factorial tails with local reciprocal sum \(O(\log L)\) and beat every fixed log power. The profile \(D\) contributes only its sup norm to these error bills. This proves (2) with the larger cutoff.

**Marked signed residual at \(Y_*\).** For an admissible tag family of \(K\) bands as in the repository's small-radical projection, and arbitrary \(G\) of the \(Y_*\)-smooth part with \(|G|\le L^{C'}\), the sum
\[
\sum_{u\in\mathcal T}\sum_{\substack{p\in I\ {\rm prime}\\u h=P-p}}
     (\log p)G(a_{Y_*}(h))\lambda(b_{Y_*}(h))
\ll_M P L^{-M}
\tag{3}
\]
for any prescribed fixed \(M\), by taking sufficiently large fixed \(K=K(M,C',B,J)\). Here \((h,R)=1\) automatically for actual primes in \(I\), \(R=\operatorname{rad}(P)\), and is retained in the analytic expansion. The tag normalizer from the prior theorem is a constant bounded above/below in terms of \(K\), so (3) is also valid unnormalized. This applies even though primes of \(u\) are themselves \(\le Y_*\) and may divide the small part of \(h\): the residual in (3) is a function of **\(h\)**, not of \(u\).

For completeness, the sole modifications of the earlier marked proof are as follows. Use [the arbitrary-bounded-residual reflected comparison](https://github.com/mxym/math/blob/main/research/theory-2026-11-20/strong-goldbach/target_slope_switch/Proof.md) and [its small-radical major bound](https://github.com/mxym/math/blob/main/research/theory-2026-11-20/strong-goldbach/small_radical_projection/Proof.md) in Type II, with the residual divided by \(L^{C'}\); do not split it over \(a\) in that part. In Type I on \(n=d k\), \(d\le P^{.4}\) is \(\exp(L^{.24})\)-rough; first open the old \(k\)-rough test through \(\lfloor L^{.1}\rfloor\) factors \(e\) as before, keeping the new residual intact. Then expand \(h=a h'\), \(a=a_{Y_*}(h)\le\exp(L^\kappa)\), and open the rough test on \(h'\) through the same depth with \(v\mid h'\), \(v\le\exp(O(L^{.3}))\). Truncating \(a\) costs the Rankin tail counted at integer \(m=P-n\) (if \(a\mid h\), it divides \(m\)) and at most polylogarithmic tag multiplicity. After \(h'=v j\), the retained congruence is \(j=P(u a v)^{-1}\bmod de\), \((j,R)=1\). Every nonempty term has \((de,uavR)=1\), because a common prime with any factor of \(uav\) would divide \(P\), whereas \(u,h\) are \(R\)-units, and a factor of \(R\) cannot divide \(P-uh\). No coprimality between \(u,a,v\) is required. For fixed \(u,a,v\) the common endpoints are \(x\asymp_J P/(uav)=P^{1-o(1)}\), and \(deR\le P^{.4+o(1)}<x^{.46}\); use the Liouville BV theorem of [Parity.md, equation (3)](https://github.com/mxym/math/blob/main/research/theory-2026-11-20/strong-goldbach/small_radical_projection/Parity.md). The \(e,d\) are uniquely determined from \(de\) by the old prime-range separation, the at most \(R\) CRT classes are paid by fixed log slack, and \(\log k=\log(P-uavj)-\log d\) has \(O_J(1)\) variation in its nonconstant part. Summation of the progression errors uses \(\sum_a1/a,\sum_v1/v\ll\log Y_*\) and the tag reciprocal mass. The second Bonferroni error is bounded by \(O(P/(u a v d e)+1)\) for the first omitted shell; its reciprocal part has factorial decay and the total floor count is \(P^{.4+o(1)}\). Proper prime powers in the first slot cost \(P^{1/2+o(1)}\). These are precisely the former Type I estimates with a larger, still subpower roughness scale only for the residual. This proves (3).

## 3. Disjoint packet grid and exact first-cover identity

Take packet centres in \([.105,.195]\) with spacing \(h=(\log4)/\log L\). Packet \(i\) is the full set of primes \(\ell\equiv1\bmod4\) in \([\exp(L^{\vartheta_i}),\exp(2L^{\vartheta_i})]\), dropping target primes (none eventually). The packets are disjoint, all their primes belong to \((y,Y_*]\), and each has reciprocal mass \(1/2\log 2+o(1)\in[1/4,1/2]\) uniformly by the prime number theorem modulo 4. There are \(J_0=.09/h+O(1)\ge c\log L\) packets. Let \(\mathscr A\) consist of all \(K\)-subsets of the packet indices with consecutive selected centres separated by at least \(1/(20K)\). Thus every family is analytically admissible, and \(|\mathscr A|\le J_0^K\). Fix a deterministic ordering on \(\mathscr A\).

For an integer \(m\), let \(c_i(m)\) be the number of its **distinct** prime factors in packet \(i\). A family \(H\) covers \(m\) when \(c_i(m)>0\) at all its selected packets. If any family covers \(m\), let \(H(m)\) be the first such family. For the moment assume no packet prime divides \(m\) twice. If \(H=H(m)\), there are exactly \(\prod_{i\in H}c_i(m)\) tag products \(u\in\mathcal T_H\) dividing \(m\). For each such \(u\), put \(h'=m/u\); all packet counts of \(m\) are recoverable from those of \(h'\) by adding one at the packets in \(H\). This is independent of the actual chosen primes of \(u\), even when different admissible families overlap. The rule that \(H\) is the first cover and the reciprocal multiplicity may therefore be applied as functions of \(h'\) alone:
\[
1_{\{m\text{ covered}\}}
=\sum_{H\in\mathscr A}\ \sum_{u\in\mathcal T_H,u\mid m}
 \frac{1_{\{H=\mathrm{first\ cover\ of}\ \mathbf c(m/u)+\mathbf1_H\}}}
      {\prod_{i\in H}(1+c_i(m/u))}.
\tag{4}
\]
The denominator is the same for every \(u\) from the first family; all other families contribute zero. If no family covers \(m\), the right side is zero as well.

In the weighted parity term, \(a_y(m)=a_y(h')\), \(\lambda(b_y(m))=(-1)^K\lambda(b_y(h'))\) since all tags exceed \(y\). Set \(a=a_{Y_*}(h')\); the packet counts, \(a_y(h')\), and the factor \(\lambda(a/a_y(a))\) all depend only on \(a\). The contribution of each fixed family in (4) is therefore exactly a marked residual of the form in (3), namely \(G(a)\lambda(b_{Y_*}(h'))\) where
\[
G(a)=\frac{(-1)^K F(a_y(a))\lambda(a/a_y(a))
          1_{\{H=\mathrm{first\ cover\ of}\ \mathbf c(a)+\mathbf1_H\}}}
             {\prod_{i\in H}(1+c_i(a))}.
\]
It is bounded by \(L^C\) and does not depend on \(u\).

Remove the packet-square exception rigorously after the whole analytic sum: the count of all integers \(m\le P\) having a squared packet prime is \(\ll P\exp(-L^{.105})\). Each original row costs at most \(L^{C+1}\); on the analytically extended marked side, the total absolute multiplicity at one row across **all** families and tags is at most \(J_0^K(L/\log2)^K\), ignoring the denominators and first-cover indicators. Thus even after summing all family errors before comparing, the exceptional total is \(O_M(PL^{-M})\). The entire covered contribution is therefore \(O_A(PL^{-A})\) by (3), taking the analytic saving \(M>A+2\) to absorb \(J_0^K=(\log L)^{O(K)}\).

## 4. Uncovered mass has a genuine fixed log power

If no family covers the occupied packet centres, greedy separation selects at most \(K-1\) centres: take the leftmost occupied centre, then the next at distance at least \(1/(20K)\), and so on. Every occupied centre lies in one of at most \(K-1\) rightward intervals of length \(1/(20K)\) anchored at those selected grid points. Altogether these intervals have length at most .05. For any such choices at least \(.04/h-O(K)\) packet centres outside the intervals must be empty, since the whole grid spans .09. There are at most \(O_K(J_0^{K-1})\) choices. Under \(\nu_{Y_*}\), the variables for disjoint packets are independent, and the probability that a given packet is empty is
\[
\prod_{\ell \text{ in packet}}\left(1-\frac1{\ell-1}\right)\le \exp(-1/4).
\]
The combined model failure probability is therefore at most
\[
O_K(J_0^{K-1})\exp\big(-(.04/h-O(K))/4\big)\ll_K L^{-1/200},
\tag{5}
\]
because \(.04/(4\log4)>1/200\). Here \(K\) is chosen **after** the desired \(A,C,\ldots\), then fixed as \(P\to\infty\). The gap between the two numerical exponents absorbs \((\log L)^{K-1}\) for every fixed \(K\). Hence the explicit exponent \(1/200\) can be fixed independent of \(A\); the large threshold and implied constants do depend on \(K(A,C,\ldots)\).

All packet primes exceed \(y\), so this event is independent in the exact CRT profile model of the original \(a_y\). Apply the unsigned profile identity (2) to \(D(a)=|F(a_y(a))|1_{\{\mathbf c(a)\text{ uncovered}\}}\), then (5). The uncovered signed error is at most this actual absolute mass, namely \(O(P\mathbb E_{\nu_y}|F| L^{-1/200}+PL^{-A})\). Together with the covered cancellation this proves (1).

The main saving comes from **combinatorial coverage**, not the variance of a linear average of marks. The available packet range still has too little harmonic length to reach a relative \(L^{-1+\delta}\) for \(a_y=1\): (1) multiplied by the \(\asymp L\) kernel coefficient gives at best \(O(P S(P) L^{1-\delta-1/200})\) from this proof. True prime complements also have no populated packet, so the uncovered term is genuine. This note is a stronger fixed-target parity estimate and a better input for some bounded or moderately log-growing weights, not a control of the complete signed rough kernel or a proof of Goldbach.
