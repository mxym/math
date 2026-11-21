# A strictly positive signed marked sector of the subquarter Pan prime–composite row

Fix a large even integer \(P\), \(L=\log P\), \(I=[P/3,2P/3]\), \(X=P/3\), and \(Q=P^v\). We use the genuine long-divisor Pan coefficient with this split:
\[
 B_v(r)=-\sum_{d\mid r,\ d\le Q}\mu(d)\log d,\qquad
 a_v(r)=B_v(r)-\Lambda(r).
\]
On a prime \(p\in I\), \(a_v(p)=-\log p\) if \(v<1\). On a number \(r\) with at least two distinct prime factors, \(a_v(r)=B_v(r)\). When \(p+r=P\) and \(p\nmid P\), \(r\) is coprime to \(P\), so the coefficient on \(r\) that excludes divisors noncoprime to \(P\) agrees. Any exceptional central prime dividing \(P\) costs \(P^{o(1)}\) even with the fixed masks used below.

For an exponent interval \(J=(a,b)\), put \(N_J(r)=\#\{\ell\mid r:\ell\text{ prime},\ P^a<\ell<P^b\}\) and \(\mu_J=\log(b/a)\). Given fixed disjoint intervals \(J_i=(a_i,b_i)\) separated from zero satisfying
\[
 b_i<v,\qquad a_1+a_2>v,\qquad b_1+b_2+v<1/2,                  \tag{1}
\]
set \(W=N_{J_1}N_{J_2}\). These rails are feasible for every \(0<v<1/4\) (take both windows just above \(v/2\)). At **every** even target tending to infinity,
\[
 \sum_{\substack{p\in I\ {\rm prime}\\r=P-p}} W(r)\,a_v(p)a_v(r)
    = (1+o(1))\,X\mathfrak S(P)\,\mu_{J_1}\mu_{J_2}.             \tag{2}
\]
No prime-pair atom is present. The right member is positive although the full prime–composite row, without the marks, is negative. This is a signed weighted contribution, not a count by the sign of each individual summand.

For an explicit bounded subweight take \(v=1/5\), \(J_1=(.070,.125), J_2=(.131,.173)\). The lower endpoints sum to .201, and the upper endpoints plus \(v\) sum to .498. \(W\le24\): with \(n_i=N_{J_i}\) one has \(70n_1+131n_2<1000\), and the largest possible products at \(n_2=1,\ldots,7\) are \(12,20,24,24,20,18,7\). Consequently the actual mask \(0\le W/24\le1\) contributes more than \(X\mathfrak S(P)/150\) per orientation for all sufficiently large even \(P\). Indeed \(\log(125/70)\log(173/131)>.16\); this follows already by the first two positive terms of \(\log y=2(h+h^3/3+\cdots),\ h=(y-1)/(y+1)>0\). The unnormalized \(W\)-mass has coefficient about .16124. Restricting the prime and its marked complement to the central interval accounts for the \(X=P/3\), not \(X=P\); the reversed physical orientation **of this same prime–composite sector** has the same value since both \(a_v^*(p)=a_v(p)\) and \(a_v^*(r)=a_v(r)\) term by term off the discarded \(p\mid P\). This does not transfer the sign to the both-composite or complementary raw sectors.

## 1. The signed local main, with full lcm multiplicities

Write \(M=\ell_1\ell_2\) for one choice of the two prime labels; only \((M,P)=1\) can contribute unless \(p\mid P\). Expand \(d\) in \(B_v\) as \(d=e k\), \(e=(d,M)\mid M,\ (k,M)=1\); \(\mu(d)\ne0\) makes this exact. The joint condition on \(p\) is \(p\equiv P\bmod Mk\), regardless of \(e\). We may require \((k,P)=1\) after the exceptions are removed. By (1), \(Mk\le P^{b_1+b_2+v}<P^{1/2-c}\). For a given modulus \(q=Mk\) the assignments of the two labeled factors and \(e\mid M\) are at most \(4\tau(q)^2\), and their log weight is \(O(L)\). The classical Bombieri–Vinogradov theorem summed with these divisor-bounded multiplicities gives \(O_A(PL^{-A})\) for all fixed \(A\), including both endpoints of \(I\). To see the weight extension, use Cauchy–Schwarz on \(E_q^{1/2}\) and \(\tau(q)^C E_q^{1/2}\), ordinary maximal-residue BV with arbitrary log saving, and \(\sum_{q\le P^{1/2}}\tau(q)^{2C} E_q\ll P L^{O_C(1)}\) by the trivial progression count and divisor moments. Here \(E_q\) is the maximum error for the prime log-weight; replacing the von Mangoldt version by this prime version costs a power in the present strictly subcritical range (even the crude per-modulus \(O(\sqrt P L^2)\) suffices). Removing actual prime divisors of \(P\) from each expanded progression likewise costs only a power-saving error.

For each choice of \(M,e\) the mean inner sum in \(B_v\), including its initial minus sign, is
\[
 -\frac{X\mu(e)}{\phi(M)}
 \sum_{\substack{k\le Q/e\\(k,PM)=1}}
       \frac{\mu(k)(\log k+\log e)}{\phi(k)} .
\]
If \(e=M\) the inner sum is empty. For \(e=1,\ell_1,\ell_2\), the cutoff \(Q/e\) exceeds a fixed positive power of \(P\). The elementary uniform prime-number-theorem estimates in [Global rough transfer, §1 (2)](PanGlobalRoughTransfer.md), applicable to the even integer \(PM\ll P^2\), evaluate the inner sum as \(-\mathfrak S(PM)+O_A(L^{-A})\): the term without \(\log k\) is smaller than every inverse log, even after multiplication by \(\log e\). Explicitly the Dirichlet series is \(\zeta(1+s)^{-1}\) times \(\prod_{q\mid PM}(1-q^{-1-s})^{-1}\prod_{q\nmid PM}(1-q^{-s}/(q-1))/(1-q^{-1-s})\); the tilted-tail/PNT argument in the cited section is uniform in the target and both marked labels. \(\mathfrak S(PM)=\mathfrak S(P)(1+O(P^{-\min a_i}))\), because the marked prime factors change just their two Euler factors. The multiplier after summing \(e\) is exactly \(1-1-1=-1\), not an absolute-value estimate. Mertens gives \(\sum_{\ell_i\in J_i}1/(\ell_i-1)=\mu_{J_i}+o(1)\); restricting to units removes \(O(L P^{-\min a_i})\). Thus the weighted \(B_v\) mean is negative and the raw Pan row has the reversed sign (2). In contrast the corresponding mark mean on the actual prime inputs is positive \(X(\mu_{J_1}\mu_{J_2}+o(1))\) by BV on \(M\). The unmarked prime-weighted \(B_v\) mean is \(X(\mathfrak S(P)+o(1))\) by the same argument with \(M=1\); hence this is also a strictly negative covariance under the ordinary prime measure, of size \(-(2+o(1))\mathfrak S(P)\mu_{J_1}\mu_{J_2}\).

## 2. A literal exact-one-in-each profile, not a weighted mask

For each fixed \(0<v<1/4\) there exist fixed disjoint windows \(J_1,J_2\), and a fixed \(\epsilon>0\), such that the unweighted subset of central prime inputs satisfying all three conditions
\[
 r=P-p\ {\rm squarefree},\quad P^-(r)>P^\epsilon,\quad
 N_{J_1}(r)=N_{J_2}(r)=1
\]
has strictly positive signed Pan contribution \(\gg_v X\mathfrak S(P)\) at **every** sufficiently large even target. The constant is not asserted to equal the explicit \(1/150\) in the unmasked weighted theorem. Other prime factors of \(r\) are allowed, but never in the two windows and never at or below \(P^\epsilon\).

Choose disjoint compact exponent neighborhoods about two points a little above \(v/2\) such that (1) holds with a uniform fixed gap, and also \(2b_1+b_2,\ b_1+2b_2<1/2\) with a fixed gap; the latter is possible since \(3v/2<3/8\). Below windows may be narrowed arbitrarily within those neighborhoods. Write \(z=P^\epsilon\) and \(r\) rough for \(P^-(r)>z\). For one marked pair, in the preceding expansion only \(z\)-rough \(k\) matter. In the joint progression \(p\equiv P\bmod Mk\), sieve \(P-p\) at primes \(\le z\) not dividing \(P\). These remove one unit residue at each prime, with local densities \(1/(s-1)\); all sieve divisors are coprime to \(Mk\). As in [Global rough transfer, §§2–3](PanGlobalRoughTransfer.md), sandwich the unsigned prime count for each \(M,k\) *before* inserting its signed weight, by the two fundamental-lemma sieves at level \(P^\eta\), where \(\eta>0\) is smaller than half all the reserved BV gaps. The sieve product \(V_1=(1+o_\epsilon(1))\mathfrak S(P)e^{-\gamma}/(\epsilon L)\). The relative sieve error is \(O(e^{-\eta/\epsilon})\). BV still covers every \(Mks\) with \(s\) a sieve divisor: \(s\) is the unique small-prime part, and the rough parts have at most the divisor-bounded multiplicities above.

Put \(h=\log e/L,\ u_h=(v-h)/\epsilon\). For an included \(e\), the signed short-divisor factor after the sieve is
\[
 \frac{-1}{\epsilon L}
 \sum_{\substack{k\le P^{v-h},\ P^-(k)>z\\(k,MP)=1}}
     \frac{\mu(k)(\log k+hL)}{\phi(k)}
 \ \longrightarrow\ \int_0^{u_h-1}\rho(t)\,dt-\frac{h}{\epsilon}\rho(u_h)
\]
in the sense that the difference from the displayed continuously varying expression tends uniformly to zero. Here \(\rho\) is Dickman's function. Indeed the first term is the signed prime-factor simplex evaluation (3) of the cited proof; its unweighted alternating simplex series is exactly \(\rho(u_h)\). Fixed compact cutoff ranges give uniformity by a finite grid: the absolute desymmetrized measures converge to continuous cumulative simplex integrals on that compact interval. Discarding nonunits in \(MP\) or replacing \(1/\phi(k)\) by \(1/k\) costs \(o_\epsilon(1)\) after normalization, uniformly by the rough harmonic product and \(\sum_{s\mid MP,s>z}1/s\ll L/z\). The absolute version before taking the fundamental-lemma error is \(O_v(\epsilon^{-2})\) in this normalization, by \(\prod_{z<s\le P^v}(1+1/s)\ll v/\epsilon\). All of these per-mark relative bounds multiply \(\sum_M1/\phi(M)\), i.e. the window masses themselves; the BV remainder is absolute \(o(X\mathfrak S(P))\) for any finally fixed windows.

Let \(\epsilon\) be small relative to the fixed exponent gaps. Since \(h\le v-c\) for every included \(e\), \(\rho(u_h)\le1/\lfloor u_h\rfloor!\) and \(\int_0^\infty\rho(t)dt=e^\gamma\), the normalized signed factor times \(e^{-\gamma}\) tends uniformly to 1. The excluded \(e=M\) has identically zero contribution. Thus the \(W\)-weighted rough prime sum with \(B_v\) is at most \(-.9X\mathfrak S(P)\mu_{J_1}\mu_{J_2}\) for small enough fixed \(\epsilon\) and sufficiently large \(P\). The same choice of \(\epsilon\) serves every pair of finally fixed narrower windows; the \(P\)-threshold need not be uniform in their widths.

Finally \(K=\lfloor1/\epsilon\rfloor\) bounds the number of prime factors of a rough \(r\), hence \(|B_v(r)|\le 2^K L\). The nonnegative difference \(W-1_{N_{J_1}=N_{J_2}=1}\) is at most \(N_{J_1}(N_{J_1}-1)N_{J_2}+N_{J_1}N_{J_2}(N_{J_2}-1)\). These are triples of *distinct* marks; their moduli lie strictly below \(P^{1/2-\eta}\) by the additional rails. BV and the same upper sieve (now without any \(k\) or signed divisor) give their total rough prime log-count
\[
 \ll X\,\frac{\mathfrak S(P)}{\epsilon L}\,
       \mu_{J_1}\mu_{J_2}(\mu_{J_1}+\mu_{J_2})
\]
for all sufficiently large \(P\), with absolute, width-independent implied constant (remove within-window diagonal duplicates for an upper bound). Now fix nonempty windows narrow enough that multiplying the last bound by \(2^K L\) costs less than \(.4X\mathfrak S(P)\mu_{J_1}\mu_{J_2}\). Removing non-squarefree rough \(r\) costs \(P^{1-\epsilon+o(1)}\) in every sum: their possible count is \(\ll P\sum_{l>z}l^{-2}\), and all fixed-rank weights are bounded by a constant times \(L^2\). This proves the positive signed indicator result with no multiplicity left.

**Scope and comparison.** The cancellation comes from a negative conditional mean of the *actual* signed coefficient when two designated factors straddle the divisor cutoff **jointly**. It is not a lower bound for the total Pan remainder: the other sectors can offset it. Conditions (1) do not permit a split at or close to \(P^{1/2}\). The method uses the standard Pan short/long identity as summarized by [Huang–Li, equations (2)–(6)](https://arxiv.org/html/2005.03811v2), classical BV, and the rough Dickman calculation noted above. The two populations in [Rough shifted prime factor tails](RoughShiftedPrimeFactorTails.md) alone do not assign any such sign.

[Arneth’s September 2026 compensation note](https://zenodo.org/records/23016346) gives an explicit compensated example for a different filter and asks for a broader criterion. [Pham’s October 2026 boundary-correlation preprint](https://www.preprints.org/manuscript/202610.3061) also uses multiplicative factor markers, with different weights and boundary correlations. The present cancellation is the exact three-term Möbius mean for this prescribed Pan cutoff and holds uniformly in the target, including for the specified rough indicator. It is not a proof of global compensation or a claim of priority for factor markers.
