# Relative parity cancellation conditional on arbitrary small-prime valuation profiles

Builds on [the companion small-radical rough-Liouville proof](SmallRadicalRoughLiouville.md) and the repository's bounded-residual reflected Type II theorem. This is a quantitative statement for actual primes at each fixed small-radical target, with weights depending on the complete small-prime part. It does not allow weights depending on how the remaining rough factors are arranged.

## 1. Statement and model

Fix \(B,C>0\), \(0<\delta<.1\), and a nondegenerate compact interval \(J\subset(0,1)\). Put \(L=\log P\), \(R=\operatorname{rad}(P)\le L^B\) for a sufficiently large prescribed even target \(P\), \(I=PJ\), \(y=\exp(L^\delta)\). Factor \(m=a_y(m)b_y(m)\) by taking the *whole* prime powers at primes \(\ell\le y\) into \(a_y(m)\); then \(b_y(m)\) is \(y\)-rough. Define a product probability measure \(\nu=\nu_{P,y}\) on \(y\)-smooth integers coprime to \(P\): for each prime \(\ell\le y,\ \ell\nmid P\), independently take its exponent to be \(0\) with probability \(1-1/(\ell-1)\), or \(k\ge1\) with probability \(\ell^{-k}\). The excluded primes \(\ell\mid P\) have exponent zero. These laws sum to one.

For any real or complex \(F\) on the small-part integers with \(|F|\le L^C\), even if it depends on \(P\), one has for every fixed \(A>0\)
\[
\left|\sum_{\substack{p\in I\\p\ {\rm prime}}}(\log p)
          \lambda(b_y(P-p))\,F(a_y(P-p))\right|
 \ll_{A,B,C,J,\delta}
 \frac{P\mathbb E_\nu|F|}{\sqrt{\log L}}+P L^{-A}.
\tag{1}
\]
The total unsigned weighted mass with any nonnegative \(F\le L^C\) is
\[
\sum_{\substack{p\in I\\p\ {\rm prime}}}(\log p) F(a_y(P-p))
 =|I|\,\mathbb E_\nu F+O_{A,B,C,J,\delta}(P L^{-A}).
\tag{2}
\]
In particular, for any profile event \(E\), writing
\(C_a=\sum_{p\in I,\ a_y(P-p)=a}(\log p)\lambda(b_y(P-p))\),
\[
\sum_{a\in E}|C_a|\ll P\,\nu(E)/\sqrt{\log L}+O_A(PL^{-A}),
\tag{3}
\]
by choosing \(F(a)=1_E(a)\operatorname{sgn} C_a\) in (1), uniformly legitimate. This gives an actual relative sign saving for any event with density at least a fixed inverse power of \(L\), not merely for a fixed list of events. The sign of the *whole* complement \(\lambda(P-p)\) is equally controlled after replacing \(F(a)\) by \(\lambda(a)F(a)\).

## 2. The exact valuation local factor and long profile tails

For every \(p\in I\) prime, \(p\nmid R\) for large \(P\), hence \((P-p,R)=1\). For a fixed allowed \(a\), the conjunction \(a_y(P-p)=a\) is precisely \(a\mid P-p\) and \(P^-( (P-p)/a)>y\). Expanding the latter by small squarefree \(e\), the true progression modulus is \(a e\), not \(\operatorname{lcm}(a,e)\): the divisibility condition is \(e\mid (P-p)/a\), including at primes shared by \(e\) and \(a\). At \(\ell\mid e\), the ratio \(\phi(ae)/\phi(a)\) acquires a factor \(\ell\) if \(\ell\mid a\), or \(\ell-1\) otherwise. Therefore the model density of a fixed profile is
\[
\nu(a)=\frac{V_y(P;a)}{\phi(a)},\qquad
V_y(P;a)=
\prod_{\substack{\ell\le y,\ \ell\nmid P\\\ell\mid a}}\left(1-\frac1\ell\right)
\prod_{\substack{\ell\le y,\ \ell\nmid P\\\ell\nmid a}}\left(1-\frac1{\ell-1}\right).
\tag{4}
\]
This is exactly the product law above, because for valuation \(k\ge1\),
\((1-1/\ell)/\phi(\ell^k)=\ell^{-k}\). At \(a=1\) the model is the \(V_y(P)\) of the rough-layer theorem. Here \(V_y(P;a)/V_y(P)\) is bounded above and below by absolute positive constants, since for each added prime the ratio is \(1+1/(\ell(\ell-2))\) and \(2\mid P\).

For an arbitrary fixed \(\kappa\in(\delta,1)\) truncate \(a\) at \(H=\exp(L^\kappa)\). The truncation loses only \(O_A(P L^{-A})\) in any real prime-log sum with \(|F|\le L^C\), even with bounded/polylog extra marks as below. Indeed
\[
\sum_{\substack{a>H\\a\text{ smooth}}}\frac1a
\le H^{-s}\prod_{\ell\le y}(1-\ell^{-1+s})^{-1}
\ll (\log y)e^{-L^{\kappa-\delta}},\qquad s=(\log y)^{-1}.
\]
The Euler product comparison to the ordinary reciprocal harmonic product costs \(O(1)\) in its logarithm: with \(s\le1/4\) and \(\ell^s\le e\), the local change is \(O(s\log\ell/\ell)\), and \(\sum_{\ell\le y}\log\ell/\ell\ll\log y\). Count all multiples of large smooth \(a\) up to \(P\) before prime weighting, to get the bound \(P L^{C+1}\sum_{a>H}1/a\); any extra tag polynomial changes only a fixed power of \(L\). The model tail is also super-log-small: by (4), \(0\le\nu(a)\ll1/\phi(a)\ll(L/a)\) for \(a\le P\); for all smooth \(a\), the factor \(a/\phi(a)\le\prod_{\ell\le y}(1-\ell^{-1})^{-1}\ll\log y\), so the displayed reciprocal tail suffices. Thus the cutoff can be used in proofs without changing their main terms.

## 3. Marked signed bound, with \(F\) not restricted to one profile

Apply exactly the tagged proof of [the companion rough-Liouville note](SmallRadicalRoughLiouville.md). Its tag primes exceed \(y\). In \(P-n=u h\), the small part \(a_y(P-n)=a_y(h)\) is unchanged under the mark \(u\), and \(\lambda(b_y(P-n))=(-1)^K\lambda(b_y(h))\). For the reflected Type II comparison, the residual can be
\[
b(h)=\lambda(b_y(h)) F(a_y(h))\,1_{(h,R)=1}\,1_{a_y(h)\le H}.
\]
Divide by \(L^C\) in the arbitrary-bounded-residual theorem and request extra log savings. Do **not** split the Type II sum by \(a\); the uniform per-box estimate applies to this single residual and gives \(O_A(P L^{-A})\).

For Type I, after the old \(z\)-rough test on \(k\) is opened, split the residual by \(h=a h'\) with \(a\le H\) the exact full \(y\)-smooth part, and open \(h'\) rough by the second Bonferroni truncation \(v\mid h'\), with at most \(h_0=\lfloor L^{.1}\rfloor\) small factors. Thus the test variable becomes \(h'=v j\) and the coefficient is \(F(a)\lambda(v)\lambda(j)\). All retained nonempty terms have \((de,uavR)=1\) by the same unit argument, even if \(a,v\) themselves share primes: they both divide \(h\), so a shared prime with \(de\) would divide \(P\), contradicting \(h\) being a unit. The congruence after substitution is \(j\equiv P(uav)^{-1}\pmod{de}\), \((j,R)=1\).

For fixed \(u,a,v\) the actual common scale is \(x\asymp_J P/(uav)=P^{1-o(1)}\); \(deR\le P^{.4+o(1)}<x^{.46}\). Coefficients, reduced CRT classes modulo \(R\), grouping \(de\), and the \(\log k\) partial summation are as before. The extra \(a\)-sum is paid by \(\sum_{a\text{ smooth}}1/a\ll\log y\); the signed factor \(F(a)\) costs at most \(L^C\). For the second Bonferroni error, its reciprocal part also gains \(1/a\) (by counting progressions of length \(O(P/(uavde)+1)\)) and keeps the factorial \((C'\log L)^{h_0+1}/(h_0+1)!\); its floor count remains \(P^{.4+o(1)}\) since \(H=P^{o(1)}\). The first rough replacement is done before expanding \(a\), so only the original bounded residual error is used there. This proves for each admissible mark \(W_j\), and all \(F\) in scope, a marked signed bound \(O_A(P L^{-A})\).

## 4. Weighted unmark via a signed depth-independent BV bill

For \(G(a)\ge0\), \(G\le L^C\), use the weighted actual prime measure \(M_G(H_0)=\sum_{p\in I\ {\rm prime}}(\log p)G(a_y(P-p))H_0(P-p)\). With the same \(J_0\asymp_K\log L\) disjoint families, \(\bar W=J_0^{-1}\sum_j W_j\), the three moments satisfy
\[
\begin{aligned}
M_G(1)&=|I|\mathbb E_\nu G+O_A(P L^{-A}),\\
M_G(W_j)&=|I|\mathbb E_\nu G\,c_j+O_A(P L^{-A}),\\
M_G(W_jW_k)&=|I|\mathbb E_\nu G\,c_{jk}+O_A(P L^{-A}),
\end{aligned}
\tag{5}
\]
with the same \(c_j=1+O(e^{-c L^{.1}})\), \(c_{jk}=c_jc_k\) across distinct families, \(c_{jj}=O_K(1)\).

To verify the modulus bill in (5), use the Bonferroni upper and lower polynomials for \(P^-( (P-p)/a)>y\) through \(h_0,h_0+1\), for every allowed \(a\le H\), weighted by \(G(a)\ge0\). A tag modulus \(s_0\) is coprime to \(ae\) since its primes exceed \(y\); its tags have the same bounded lcm multiplicities as before. The prime progression is \(p\equiv P\bmod q\) with \(q=s_0 a e=P^{o(1)}\), a reduced class. Unlike the case \(a=1\), \(ae\) need not determine \(a,e\) individually. There are at most \(\tau(q)\) possible \(e\)'s dividing the small part of \(q\), and once \(e\) is chosen the small part determines \(a\). All absolute coefficients grouped by \(q\) are therefore \(O_K(L^C\tau(q))\). Ordinary uniform prime-log BV pays this weighted bill: if \(E_q\) is its absolute maximal prime error, trivially \(E_q\ll P L/q\) for \(q\le P\) by counting integers and bounding \(q/\phi(q)\ll L\); then
\[
\sum_q\tau(q)E_q
\le(\sum_q E_q)^{1/2}(P L \sum_{q\le P}\tau(q)^2/q)^{1/2}
\ll_A P L^{-A},
\]
using BV with larger log saving, \(\tau(q)^2\le\tau_4(q)\), and \(\sum_{q\le P}\tau_4(q)/q\ll L^4\). The extra \(L^C\) is paid by another fixed log power. Actual endpoints of \(I\) are common for these prime progression counts; even endpoint inclusions can be handled via the exact maximal error.

For each \(a\) the model has the \(\phi(a)\) factor and the two \(\ell\)-probabilities of (4), and \(\phi(s_0)\) separates exactly. Each model Bonferroni error is super-log-small uniformly in \(a\), by \(\sum_{\ell\le y}1/(\ell-1)=O(\log L)\) and the factorial tail. Summation uses \(\sum_{a\text{ smooth}}1/\phi(a)\ll(\log y)^2\), a fixed power of \(L\); the tag factors \(c_j,c_{jk}\) are bounded. This proves (5), including \(|I|\mathbb E_\nu G\) as the correct main mass. Consequently
\[
M_G(|\bar W-1|^2)\ll |I|\mathbb E_\nu G/J_0+O_A(P L^{-A}).
\]
Take \(G=|F|\). Averaging the marked signed estimate and applying Cauchy with weight \(G\) bounds its unmarking error by
\((M_G(1)M_G(|\bar W-1|^2))^{1/2}\).
Using (5) and requesting a larger fixed \(A\) in the intermediate errors (note \(\mathbb E_\nu G\le L^C\)), this is
\(O(P\mathbb E_\nu|F|/\sqrt{\log L}+P L^{-A})\). This gives (1) and (2) simultaneously and completes the proof.

For examples, \(F\) may specify any exact small prime power pattern, a prescribed count or multiset of small factors, or a signed small-divisor weight with at most polylogarithmic height. The relevant saving is relative to the model first absolute moment of that weight, not to its sup norm. A weight depending on which rough factors exceed a moving divisor threshold does not meet this hypothesis; most of the old signed divisor kernel is of that kind. This theorem does not establish rank-one prime-opposite positivity.
