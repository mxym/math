# Lower bounds on the least common multiple of an odd distinct cover

Research note, 28 November 2026. Let \(\mathcal C\) be a finite set of arithmetic progressions covering \(\mathbb Z\) with pairwise distinct odd moduli greater than one. Let \(Q\) be the least common multiple of the moduli and let \(r=\omega(Q)\).

**Theorem.** Every such covering system satisfies
\[
 Q\ \ge\ 168\,131\,152\,814\,625 .
\]
More specifically, the respective lower bounds for \(r=9,10,11\) are \(168\,131\,152\,814\,625\), \(473\,824\,157\,932\,125\), and \(3\,506\,298\,768\,697\,725\). If \(r\le 11\), then some prime \(p\ge 7\) satisfies \(p^2\mid Q\).

We use two separate prior theorems: Dai–Li–Li–Yi, [*On the moduli of distinct covering systems*, Theorem 1.1](https://arxiv.org/abs/2611.15110v1), proves \(45\mid Q\), and Schroeder, [*Nine Prime Divisors in Odd Distinct Covering Systems*, Theorem 1.1](https://michaelschroeder.ai/research/NinePrimeSupport/companion), proves \(r\ge9\). Our unconditional numerical lower bound is \(17\,325\) times the \(9\,704\,539\,845\) bound in Schroeder's Corollary 1.3. The proof below combines the distortion and scalar comparison of Dai–Li–Li–Yi with selective removal of pure prime-power towers, an approach to initial conditioning used in Schroeder's [rank-seven work](https://michaelschroeder.ai/research/SevenPrimeSupport/companion). The [earlier valuation note](FactorOddCoveringValuationRestrictions.md) used conditioning on the two smallest towers to exploit missing primes; here the key additional steps are finite caps at every position, selective removal at later positions, and monotone replacement of the sorted support. Neither attainment of these bounds nor existence of an odd distinct covering is asserted. In particular, we do not exclude rank nine.

## 1. A finite-support loss bound

Order the primes dividing \(Q\) as \(p_1=3<p_2=5<p_3<\cdots<p_r\), put \(a_j=v_{p_j}(Q)\), and, for the following argument, allow upper caps \(b_j\ge a_j\), including \(b_j=\infty\). Define
\[
 s_j=\sum_{e=1}^{b_j}p_j^{-e}.
\]
Choose in advance a flag \(\eta_j\in\{0,1\}\) for each position, with \(\eta_1=\eta_2=1\). If \(\eta_j=1\), delete from the \(p_j\)-coordinate all the pure \(p_j\)-power classes present in \(\mathcal C\); use the uniform law \(\nu_j\) conditioned on the surviving residues. The union of deleted residues has uniform mass at most \(s_j<1\) by distinctness. If \(\eta_j=0\), use the unconditioned uniform law. In either case, a specified residue class modulo \(p_j^e\) now has \(\nu_j\)-mass at most \(g_jp_j^{-e}\) with
\[
 g_j=(1-s_j)^{-\eta_j}.
\]
These deletions define a nonempty product of coordinate sets under CRT, which the remaining progressions must still cover.

Start with the product \(\nu_1\otimes\nu_2\). The only remaining moduli with largest prime \(5\) are \(3^e5^f\) for \(e,f\ge1\); their union has measure at most
\[
 L_2^{*}=(g_1s_1)(g_2s_2).
\]
For each \(j\ge3\) extend the measure by \(\nu_j\). On a fibre over preceding coordinates \(x\), let \(\alpha_j(x)\) be the \(\nu_j\)-mass covered by the remaining progressions with largest prime \(p_j\). With \(\delta_j\in[0,1/2]\) and \(c_j=(1-\delta_j)^{-1}\), reweight the covered part to mass \(c_j(\alpha_j(x)-\delta_j)_+\) and the uncovered part to its complement, keeping the conditional reference law within each part. A part with zero size is assigned zero mass. The density relative to \(\nu_j\) is at most \(c_j\): above threshold the uncovered density is \(c_j\), below threshold it is \(1/(1-\alpha_j)\le c_j\), and the covered density is at most \(c_j\) in both cases. This preserves all preceding joint marginals. In the final law the \(j\)-th stage has measure \(c_j\,\mathbb E(\alpha_j-\delta_j)_+\), and the conditional cylinder bound in coordinate \(j\) is \(c_jg_jp_j^{-e}\). Use \(c_1=c_2=1\).

Define independent positive integer variables \(D_j\) by
\[
 \Pr(D_j\ge e+1)=c_jg_jp_j^{-e}\quad(1\le e\le b_j),
 \qquad
 \Pr(D_j\ge e+1)=0\quad(e>b_j).
\]
These are valid tails: \(g_1\le2\), \(g_2\le4/3\), and \(c_jg_j\le12/5\) for \(j\ge3\). With \(X_j=\prod_{i<j}D_i\), the scalar comparison gives the bound
\[
 L_j^*=c_j\,\mathbb E\big((g_js_j)(X_j-\eta_j)-\delta_j\big)_+
 \qquad(j\ge3).
 \tag{1}
\]

For completeness, the scalar comparison behind (1) works even when several original congruence conditions on one coordinate coincide or overlap. Take an increasing convex function \(\phi\) of a positive weighted sum of residue-class indicators. On one coordinate, order indicators by increasing exponent, with corresponding weights \(w_\ell\ge0\), and put \(A_\ell=\sum_{i\le\ell}w_i\). The increment when the \(\ell\)-th indicator \(I_\ell\) is added is at most \(I_\ell\big(\phi(A_\ell)-\phi(A_{\ell-1})\big)\), by convexity. With the comparison indicators \(1_{\{D_j\ge e_\ell+1\}}\), equalities hold because the active indicators form an initial segment, and each has probability equal to the applicable conditional upper bound on the original indicator. Exponent zero corresponds to the always-active indicator. Apply this replacement in reverse coordinate order, conditioning on the earlier actual coordinates and the later independent comparison variables, so all weights for the current coordinate are fixed and the conditional bounds apply.

On a \(p_j\)-fibre each modulus \(mp_j^e\) contributes at most \(g_jp_j^{-e}\) times its prefix indicator, and at most one progression has any given pair \((m,e)\). Applying the comparison with \(\phi(z)=(z-\delta_j)_+\), then allowing every exponent vector in the caps, gives \(X_j\) possible prefixes; subtract one if the pure powers have been deleted. Summing the weights over \(e\) gives \(g_js_j\), proving (1). If
\[
 L_2^*+\sum_{j=3}^r L_j^*<1,
 \tag{2}
\]
the final measure assigns positive mass to an uncovered point of the surviving product, which contradicts covering.

## 2. Replace every support position by the smallest possible prime

Fix \(r\), the caps \(b_j\), and the schedule \((\eta_j,\delta_j)\) *by position*. Let \(\pi_1,\dots,\pi_r\) be the first \(r\) odd primes. Since \(p_j\ge\pi_j\), \(s_j\) and \(g_j\) weakly increase when \(p_j\) is replaced by \(\pi_j\), and the tails defining \(D_j\) weakly increase as well. Couple the original and replacement variables independently at each position by the same uniform quantile. The product \(X_j\) can only increase. As \(X_j\ge1\ge\eta_j\), the payoff in (1) is nondecreasing in both \(X_j\) and \(g_js_j\). Consequently the *bound* in (2) only increases on replacement. We do not replace or construct any actual residue class. If the exact exponent vector is \(a\), then also \(\prod_{j=1}^r\pi_j^{a_j}\le Q\).

This yields a finite test for any proposed lower bound \(B\) at rank \(r\): enumerate all vectors \(a_1\ge2,a_2,\dots,a_r\ge1\) with \(\prod_j\pi_j^{a_j}<B\) and prove (2) on their packed support, using \(b_j=a_j\). Every actual \(Q<B\) has such a vector on its replacement support. There is no need to enumerate residue labels, divisors of every \(Q\) or actual supports. Testing the same cap at infinity on some coordinates is also valid, since increasing a cap only increases the loss bound.

## 3. Exact arithmetic

Use the following two schedules, the same for all three ranks and truncated to their length. Here \(\eta_j=1\) means deletion, not absence of the prime.

| Position \(j\) | 3 | 4 | 5 | 6 | 7 | 8 and later |
|---|---:|---:|---:|---:|---:|---:|
| \(\eta_j\) | 1 | 1 | 1 | 0 | 1 | 1 |
| \(\delta_j\), first schedule | 34/200 | 60/200 | 83/200 | 94/200 | 78/200 | 100/200 |
| \(\delta_j\), second schedule | 39/200 | 60/200 | 83/200 | 94/200 | 78/200 | 100/200 |

The [standalone verifier](verify_factor_odd_covering_lcm.py) uses only Python's integer/rational standard library. Remove the mandatory factor \(3\prod_j\pi_j\). For the remaining product, take the budget \(\lfloor (B-1)/(3\prod_j\pi_j)\rfloor\), and by position choose an extra exponent \(k\ge0\) with \(\pi_j^k\) no greater than the current budget, then divide the budget by \(\pi_j^k\) rounding down. This enumerates each admissible vector once. Compute both loss bounds on every vector, take the smaller, then take the maximum over vectors. The full finite product law is evaluated by multiplicative convolution; the probability of \(D_j=d\) is the difference of successive tails. The optional check redoes this with the first moment and the truncated distribution below each loss threshold. It uses \(\mathbb E(X-t)_+=\mathbb E X-t+\sum_{v<t}(t-v)\Pr(X=v)\), retaining masses only through the largest threshold since all factors are at least one. This second recurrence also evaluates infinite caps exactly using the geometric first moment.

| Rank \(r\) | Cutoff \(B\) | Packed vectors strictly below \(B\) | Maximum loss, rounded upward (ppm) |
|---|---:|---:|---:|
| 9 | 168,131,152,814,625 | 667 | 994213 |
| 10 | 473,824,157,932,125 | 211 | 993646 |
| 11 | 3,506,298,768,697,725 | 81 | 948467 |

For \(r\ge12\), the mandatory packed baseline is already \(3\prod_{j=1}^{12}\pi_j=456\,375\,395\,290\,815\). Thus all ranks have the stated unconditional bound. Finally, for \(r=9,10,11\) and caps \((\infty,\infty,1,\ldots,1)\), the first schedule gives maxima bounded by \(911641, 956557, 995164\) ppm, respectively. This proves the repeated-prime assertion.

Replay: run `python3 verify_factor_odd_covering_lcm.py --cross-check` in normal mode. Neither this replay nor the proof above claims a new formalization of either imported theorem.
