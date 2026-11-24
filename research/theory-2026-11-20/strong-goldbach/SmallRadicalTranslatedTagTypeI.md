# Translated tags: multi-offset cover and a paid Type I/II slice

Two results below are unconditional given ordinary prime/known Liouville Bombieri–Vinogradov: the true prime-side uncovered mass for finitely many translated target offsets, and cancellation of every corresponding Vaughan Type I term plus a proper Type II slice. The remaining Type II estimate is **not** claimed, and the old one-variable residual theorem does not apply.

## 1. Setup and a cover that does not exclude prime complements

Let \(P\) be a sufficiently large prescribed even integer, \(L=\log P,\ R=\operatorname{rad}(P)\le L^B\), \(I=PJ\) for fixed compact \(J\subset(0,1)\); put \(m=P-n\) and \(y=\exp(L^\delta)\), \(0<\delta<.1\). Take fixed \(M\ge2\) offsets \(j=2,\dots,M+1\), with translated complement \(m_j=jP-n=m+(j-1)P\). The translated targets \(jP\) still have polylogarithmic radical, but their tag primes need **not** divide \(m\), even when \(m\) is prime.

Use the packet grid, full prime bands \(\equiv1\bmod4\), and admissible \(K\)-subsets \(H\) of centres from [the first-cover proof](SmallRadicalFirstTagCover.md). Centres form a grid in \([.105,.195]\) with step \(h=\log4/\log L\); let \(J_0=.09/h+O(1)\) be the number of packets. Each packet has reciprocal mass at least \(1/4\), and \(H\) is admissible when it has \(K\) centres with gaps at least \(1/(20K)\). The tag set \(\mathcal T_H\) is the products of one prime per selected packet. Fix an ordering on all pairs \((j,H)\). A pair covers \(n\) if every packet of \(H\) contains a prime dividing \(m_j\), and use the first pair if any. Let \(c_{j,i}\) be the number of distinct packet-\(i\) prime factors of \(m_j\).

For a fixed pair \((j,H)\), put
\[
A_{j,H}(n)=
\frac{1_{\{(j,H)\text{ first covering pair for }n\}}}
{\prod_{i\in H}c_{j,i}},
\]
with value zero when numerator is zero. Since there are exactly \(\prod_{i\in H}c_{j,i}\) tags \(u\in\mathcal T_H\) dividing \(m_j\), regardless of multiplicities in \(m_j\), one has the exact coverage partition
\[
1_{\{n\text{ covered}\}}
  =\sum_{j,H}\ \sum_{\substack{u\in\mathcal T_H\\u\mid jP-n}} A_{j,H}(n).
\tag{1}
\]
It is not necessary to discard squareful rows for (1); the denominator is computed from actual counts on \(m_j\). If instead one reconstructs the *one chosen offset's* counts from \(h'=(jP-n)/u\) by adding one per selected packet, this only works away from tag squares. Across all \(M\) shifted variables the number of integer exceptional \(n\in I\) is then \(O_M(P e^{-L^{.105}})\): for each packet prime \(q\) use \(q^2\mid m_j\) and \(\#\le O_M(P/q^2)\) since \(m_j\le(M+1)P\). The total absolute marked multiplicity per \(n\) is at most \(M J_0^K(L/\log2+O_M(1))^K\), ignoring all denominators/selection. Hence with any fixed log weights this alternate reindexing still costs only \(O_A(PL^{-A})\). It does not remove the dependence on the actual \(u\) for the other offsets.

## 2. True prime-side mass of the multi-offset uncovered set

Let \(V_y(P)=\prod_{\ell\le y,\ell\nmid P}(1-1/(\ell-1))\sim e^{-\gamma}S(P)/\log y\). For each fixed \(M,K\), every \(A>0\), and all sufficiently large \(P\) in scope, the uncovered log-prime mass has the unconditional bound
\[
\sum_{\substack{n\in I,\ n\text{ prime},\ P^-(P-n)>y\\
                 n\text{ not covered at any offset}}}\log n
\ll_{A,M,K,B,J,\delta}|I|V_y(P)L^{-M/200}+PL^{-A}.
\tag{2}
\]
For each offset with no covering \(H\), the greedy rule from first-cover says its occupied centres lie in at most \(K-1\) intervals of length \(1/(20K)\) anchored at grid points. Thus at least \(.04/h-O(K)\) centres must be empty at that offset. Fix a choice of such boxes for each offset, and let \(t_i\) be the number of offsets forced to be empty at packet \(i\). Every packet prime \(q\) eventually exceeds **\(M+1\)** and is coprime to \(P\); no bound \(q>MP\) is needed or true. Thus \(jP\bmod q\) are distinct nonzero residues for \(j=2,\dots,M+1\). Conditional on the prime slot taking a reduced residue, its exact local survival under the \(t_i\) packet restrictions is
\[
1-\frac{t_i}{q-1},
\]
not a product of fictitiously independent probabilities at that same prime. Across different primes these restrictions are independent in the CRT model. The rough condition at \(\ell\le y\) gives \(V_y(P)\), and these primes are disjoint from packets. Since each packet has \(\sum_{q\in\mathcal Q_i}(q-1)^{-1}\ge1/4\), the product of packet factors is at most \(\exp(-\sum_i t_i/4)\). Sum over \(O_{M,K}(J_0^{M(K-1)})\) box choices; \(\sum_i t_i\ge M(.04/h-O(K))\), and \(.04/(4\log4)>1/200\). For every fixed \(M,K\) the grid polynomial is absorbed by that strict margin, giving the model bound \(V_y(P)L^{-M/200}\).

This model is an actual upper bound for the prime log mass to an \(O_A(PL^{-A})\) error. For each fixed box choice, apply the two Bonferroni polynomials through depth \(\lfloor L^{.1}\rfloor\) and one more to all bad-prime events. At any selected squarefree modulus \(d\), the number of reduced CRT residues is at most \(D^{\omega(d)}\) with \(D=M+1\) fixed, and \(d\le\exp(O(L^{.3}))=P^{o(1)}\). Pay the ordinary log-prime BV error with this weight using Cauchy–Schwarz, its unweighted sum and \(\sum_{d\le P}D^{2\omega(d)}/d\ll_D L^{D^2}\) (Euler product), together with the crude maximal error \(O(PL/d)\). The model tail is at most a factorial tail with reciprocal sum \(O_M(\log L)\), hence arbitrarily log-small. The number of box choices is only a fixed power of \(\log L\); request extra fixed power saving for it. No unsigned parity theorem is needed for (2).

## 3. Unconditional shifted Type I with the exact joint-profile selector

Fix \((j,H)\), and in (1) consider the genuinely signed marked sum with weight \(\lambda(m)1_{\{P^-(m)>y\}}\log n\) for \(n\in I\) prime. All following estimates are uniform in \((j,H)\) at fixed \(M,K\). Replace the prime log by \(\Lambda(n)1_{\{P^-(n)>z\}}\), \(z=\exp(L^{.24})\); the difference is \(P^{1/2+o(1)}\) by the fixed log tag multiplicity. Retain \((m,R)=1\) explicitly, since \(n\) is \(z\)-rough and \(R\le L^B\).

Use Vaughan's identity with \(U=V=P^{1/5}\), with rounding harmless. The short supported term is absent on \(I\). In each Type I expression \(n=d k_0\), the coefficient on \(d\) is \(O(L)\) (after grouping \(\mu_{\le U}*\Lambda_{\le V}\) using \(\sum_{r\mid d}\Lambda(r)=\log d\)), \(d\le P^{.4}\) is \(z\)-rough, and the possible smooth multiplier is \(\log k_0\). In fact the argument below works for \(d\le P^{.45}\). Open \(k_0\)-roughness with the old depth-\(\lfloor L^{.1}\rfloor\) modulus \(e\) on primes \(\le z\), keeping the joint selector and complementary roughness real at this step. For a tag \(u\mid jP-n\) we have \((de,u)=1\): a common packet prime would divide \(jP\), impossible since it exceeds \(M+1\) and is a target unit. Thus the omitted-shell error counts \(O(P/(deu)+1)\); the usual reciprocal factorial bound and floor \(P^{.45+o(1)}\) give \(O_A(PL^{-A})\). The \(\sum_u 1/u\) mass for a fixed family is bounded in terms of \(K\).

Next split \(a_o\), the complete **packet-prime-supported** part of \(m_o=oP-n\), for each \(o=2,\dots,M+1\). Truncate every \(a_o\le H_*=\exp(L^\kappa)\) for any fixed \(.2<\kappa<1\). Counting all integer \(n\in I\) by \(a_o\mid oP-n\), where \(a_o\le(M+1)P\), costs \(O_M(P/a_o)\) per possible \(a_o\). The total exception count is \(P L^{O(1)}\exp(-c L^{\kappa-.2})\) by Rankin over packet-smooth integers, as in the profile argument. If this truncation is performed after the Type I opening, absolute Type I multiplicities are bounded by a fixed log factor times \(\tau(n)^2\) (choices \(d\) and \(e\) dividing \(n\)), along with at most \(L^{O_K(1)}\) tag multiplicity. Use Cauchy–Schwarz and \(\sum_{n\le P}\tau(n)^4\ll P L^{15}\) (or any fixed divisor-moment exponent) to pay the tail. In each retained profile tuple the joint first-cover weight/denominator depends only on the profiles, and \(u\) is chosen from divisors of \(a_j\), giving at most \(L^K\) multiplicity and no new modulus.

Expand the assertion that \(m_o/a_o\) has no further packet prime by another Bonferroni test, its squarefree modulus \(e_o\) supported on packets. It imposes **\(a_o e_o\mid m_o\)**, allowing \(e_o\) and \(a_o\) to share prime factors. For two different offsets \(o,o'\) the moduli \(a_o e_o,\ a_{o'}e_{o'}\) must be coprime in each nonempty term: a common packet prime would divide \((o-o')P\), contrary to size and \((q,P)=1\). They are each coprime to \(de\), since a common packet prime would divide \(oP\), also impossible. Finally open \(m\)'s \(\le y\) rough condition by \(v\mid m\) of the same truncation depth, choosing only primes not dividing \(R\) (the other primes are already excluded). The modulus \(v\) is coprime to all packet moduli by prime ranges. If a prime divided both \(v\) and \(de\) it would divide \(m+n=P\), contradicting \((v,R)=1\), so this intersection cannot occur. Similarly \(de\) and packet moduli are coprime to \(R\) on nonempty terms.

The successive Bonferroni errors now have bound \(O(P/(de\, v \prod_o a_o e_o)+1)\) for the integer count, with omitted variables set to 1 or kept in their exact base \(a_o\)-condition. Indeed all factors in that displayed product are coprime except the allowed \(a_o,e_o\) within a single factor, whose product is itself an exact divisor; the modulus \(v\) is absent until it is imposed. At any omitted-shell boundary its reciprocal sum is \((O_M(\log L))^{h_0+1}/(h_0+1)!\) with \(h_0=\lfloor L^{.1}\rfloor\). The other reciprocal sums contribute only fixed powers of \(L\), including \(\sum_{a_o}1/a_o\); the coefficients/sign tests and tag multiplicity are bounded by fixed log powers. Every small variable \(e,v,a_o,e_o\) is \(P^{o(1)}\); there are only finitely many slots. Thus the **total** number of floor-error tuples including \(d\le P^{.45}\), and after including all tag choices, is \(P^{.45+o(1)}\). This pays all signed/unsigned truncation errors without assuming independence of memberships at shared primes.

In the retained expression put \(m=v b\), so \(\lambda(m)=\lambda(v)\lambda(b)\). The natural endpoint interval is \(b\in(P-I)/v\), both endpoints fixed by \(I\) and \(v\), of scale \(x\asymp_J P/v=P^{1-o(1)}\). At fixed \(v\), the congruence for \(b\) is \(b\equiv P v^{-1}\pmod{de}\) and \(b\equiv-(o-1)P v^{-1}\pmod{a_o e_o}\) for each offset. These are all reduced classes, including the latter because packet primes exceed \(M+1\) and avoid \(R\). Ensure \(b\) is a target unit by the at most \(R\) unit classes modulo \(R\). The **actual combined modulus** is
\[
q=de\,R\prod_o a_o e_o\le P^{.45+o(1)}<x^{.46}.
\]
For fixed \(v,q\), apart from the explicit \(R\)-classes and \(L^K\) tag factor, multiplicity of groupings is at most \(D_M^{\omega(q)}\): a prime power is assigned to \(de\) or an offset slot; in \(de\) separation at \(z\) uniquely determines the rough \(d\) and small \(e\); within an offset there are at most two choices for its squarefree part in \(e_o\), and then its power in \(a_o\) is determined. No separate factor \(P^{o(1)}\) is spent on arithmetic progression errors. Apply the known Liouville BV to \(x^{.46}\) of [small_radical_projection/Parity.md, equation (3)](https://github.com/mxym/math/blob/main/research/theory-2026-11-20/strong-goldbach/small_radical_projection/Parity.md) with this weighted multiplicity, using the same Cauchy bound as §2 with \(E_\lambda(x;q)\le x/q+1\). Costs from \(R\le L^B\), logs and tag weights are fixed powers. For the \(\log k_0=\log(P-vb)-\log d\) term, partial summation uses the common \(b\)-endpoints and total variation \(O_J(1)\) of the nonconstant part. Both endpoints are \(\asymp_J P/v\), so the actual modulus bound applies at every partial-summation endpoint. Sum the errors in \(v\) via \(\sum_v1/v\ll\log y\).

Thus every exact marked Vaughan Type I term, with the full first-cover selector across offsets, is \(O_A(PL^{-A})\). No translated Type II result was invoked. In particular this gives the whole Type I calculation at the smallest requested \(M=2\), and at every fixed \(M\).

## 4. An additional actual original Type II slice

Consider the original high term \(+\mu_{>U}*\Lambda_{>V}*1\) and restrict its \(\Lambda\)-factor \(r\) to \(P^{1/5}<r\le P^{1/4}\). On \(n\in I\), \(k=n/r\gg_J P^{3/4}>U\), so
\[
\sum_{\substack{d\mid k\\d>U}}\mu(d)=-\sum_{\substack{d\mid k\\d\le U}}\mu(d).
\]
The slice is now an exact short progression expression with \(D=rd\le P^{.45}\); after grouping its coefficient is bounded by \(\sum_{r\mid D}\Lambda(r)=\log D\). The original rough support forces \(D\) rough, and the remaining quotient has the usual independent rough sieve test. Apply the already paid §3 to \(D\) in place of \(d\). This proves \(O_A(PL^{-A})\) on this nonempty **original** Type II slice, with the same exact rough complement and first-cover selector. What remains of the original high term has \(r>P^{1/4}\).

## 5. The needed new input, and only its conditional consequence

After fixing \(u\mid jP-n\) and writing \(h'=(jP-n)/u\), the sign is
\(\lambda(uh'-(j-1)P)\), and the global first cover depends on the other shifted values \(u h'+(o-j)P\). This is a bounded but genuinely **\(u\)-dependent** residual, unlike the previously proved arbitrary one-variable \(b(h')\) comparison. In particular applying the old Type II theorem to it, or assuming independence of residues across offsets at the same prime, would be invalid. A log-small estimate for the remaining \(r>P^{1/4}\) high term against this exact residual for each fixed \((j,H)\) would, with §§3–4, pay the covered sum in (1).

Conditional on only that new estimate, (2) then gives
\[
\left|\sum_{\substack{n\in I,\ n\ {\rm prime}\\P^-(P-n)>y}}
       (\log n)\lambda(P-n)\right|
\ll_A P V_y(P)L^{-M/200}+PL^{-A}.
\]
Take \(M=240\) (or any fixed \(M>200\)), \(K\) fixed large enough for the hypothesized accuracy, and \(A\) large. This would pay the \(\asymp L\) factor on \(a=1,d=1\) of the triangular Goldbach switch: write \(\log(\alpha/m)=\log(\alpha/P)-\log(m/P)\) on \(I\), multiply the sign estimate by the first constant, and bound the second bounded weight by the known rough unsigned mass. Replace \(\lambda\) by \(\mu\) at super-log-small cost using the all-integer rough-square tail. No claim is made for the other rough divisors \(d>1\) or for Goldbach positivity. This is a concrete alternative way to locate a new mixed estimate whose resolution would beat the previous unmarking exponent on this channel, not a resolution of that estimate.
