# A polynomial large-radical band of genuine ordinary minor arcs for the short-prime mixed marker

Research note, 2026-11-24. This pays essentially all **prime denominators in one genuine polynomial dyadic band**, with their full reduced numerators and ordinary \(1/P\)-scale neighborhoods. It leaves generic minor frequencies, composite denominators, and a small exceptional prime set unpaid. It is separate from [the subexponential small-radical arc result](SmallRadicalSubexponentialArcs.md).

## 1. Statement

Let \(P\) be large even, \(\operatorname{rad}(P)\le L^B,\ L=\log P\), \(I=PJ\) fixed interior, \(y=e^{L^\delta}\) with \(0<\delta<.1\), \(z=e^{L^{.24}}\). Let \(D=P^{1/2}e^{-L^{3/5}}\), \(0<\sigma<1/4\), and \(\mathcal P\) any subset of actual primes in \((P^\sigma,D]\). Set
\[
s(n)=\sum_{\substack{p\in\mathcal P\\p\mid n}}1,\qquad
f(n)=1_{n\in I}(\log n)s(n)R_z(n)\lambda(n),\qquad
g(m)=1_{m\in P-I}R_y(m)\lambda(m).
\]
The product Fourier integral is exactly [the unmarked aggregate G23 mixed statistic](SmallRadicalG23CoreBilateral.md). Define \(f_C(n)=C_{>1}(n)f(n)\) using the actual translated first selector with \(M\) fixed offsets.

There is a sufficiently small **fixed** \(\eta>0\), depending at most on \(\sigma\) and absolute zero-density/analytic constants, such that for each \(P\), all but \(O(P^{.4\eta})\) primes \(q\in[Q,2Q]\), \(Q=P^\eta\), are good. For any fixed \(J_0>0\), let \(\mathfrak B\) be the union, over good \(q\) and **all** its reduced numerators, of arcs
\[
\alpha=a/q+\beta,\qquad |\beta|P\le L^{J_0}.
\]
Then
\[
\int_{\mathfrak B}|S_f(\alpha)S_g(\alpha)|\,d\alpha =O_A(PL^{-A})\qquad(A>0).
\tag{1}
\]
With the exact marked \(f_C\), the bound has additional error
\[
O\big(P L^{.88-\delta/2-M/400}+P^{.57}\big).
\tag{2}
\]
Thus for \(M\ge800\) this same actual marked frequency band costs \(o(PV_y(P)/L)\). Alternatively, whenever one uses the already proved **global** deletion of \(C_{>1}\) (e.g. \(M\ge400\)), (1) applies directly to the unmarked equivalent target. The stronger \(M\ge800\) choice is for carrying the mark on **this absolute frequency integral**, not for total deletion.

Prime denominators here have radical \(q\asymp P^\eta\), so these are not in the small-radical arcs. There are \(\asymp Q/\log Q\) true good prime denominators by PNT and the power smaller exception set. Their full reduced-arc measure has order \(Q^2 L^{J_0}/(P\log Q)\), with disjoint arcs for large \(P\); it is polynomially larger than a purely polylog-major set while still a proper restricted region.

## 2. Good large-radical prime moduli: primitive power saving

Fix \(\kappa=1/1000\) and \(T=P^{100\eta}\). Call a prime \(q\in[Q,2Q]\) bad if some primitive character modulo \(q\) has a zero with \(\Re s\ge1-\kappa\), \(|\Im s|\le2T+1\). The classical log-free Dirichlet density theorem, as stated in [Klurman, Mangerel and Teräväinen, Lemma 7.3](https://londmathsoc.onlinelibrary.wiley.com/doi/10.1112/plms.12546), gives
\[
\sum_{r\le 2Q}\sum_{\chi\bmod r}^{*} N(1-\kappa,2T+1,\chi)
\ll [(2Q)^2(2T+1)]^{3\kappa}
\ll P^{.4\eta}.
\]
Here 3 is a deliberately weakened exponent from \(12/5+\varepsilon\). Every bad prime is counted at least once; for prime \(q\) all nonprincipal characters are primitive. The statement thus allows real zeros without claiming effective exclusion at any individual bad \(q\).

For a good \(q\), any \(\chi\ne\chi_0\bmod q\) has uniformly
\[
\sum_{n\le X}\lambda(n)\chi(n)\ll X P^{-50\eta}
\quad(P^{.2}\le X\le 2P),
\tag{3}
\]
after \(\eta\) is made sufficiently small. For completeness, at height \(|t|\le T\), take a disk of radius \(\kappa/2\) about \(1+\kappa/8+it\) in the zero-free box. The usual convexity/polynomial growth gives \(\log|L|\ll\log(q(T+3))\) there; the Euler series bounds a chosen logarithm at the center. Borel--Carathéodory and Cauchy give \(L'/L=O_\kappa(\log(q(T+3)))\) on the central half disk. Choose a fixed \(h<\kappa/16\) with \(C_\kappa h<1/5\) after this derivative constant, and integrate horizontally from \(1+h+it\) (where the reciprocal Euler product is bounded in terms of \(h\)). This gives uniformly \(1/L\ll_h (q(T+3))^{C_\kappa h}\ll_h P^{25\eta}\) on \(\Re s\ge1-h\) up to the Perron start line; to the right of the local interval the Euler product suffices. Truncate Perron at height \(T\) and a neighboring half-integer endpoint, using the exact series \(L(2s,\chi^2)/L(s,\chi)\), whose numerator is bounded absolutely on this contour. Horizontal errors are \(O(XP^{25\eta}/T)\) and the bounded-coefficient truncation error \(O(X L^2/T)\). The vertical is \(O(X X^{-h}P^{25\eta}\log T)\). Choose \(\eta<.2h/100\), and smaller than \(\sigma/2\). All are \(O(XP^{-50\eta})\) for large \(P\). The principal/zeta input below is only the standard arbitrary-log \(\lambda\) bound, not a fictitious constant zero-free strip for zeta.

## 3. Keep the real rough coefficients by a global \(L^2\) substitution, not by claiming power-size rough tails

For \(w=y\) or \(z\), the exact Euler convolution gives
\[
\lambda(n)R_w(n)=\sum_{\substack{v\mid n\\v\ {\rm squarefree},\ P^+(v)\le w}}\lambda(n/v).
\]
Let \(b_w(n)\) be this sum truncated at \(v\le P^{1/10}\). This cutoff is in terms of the actual target \(P\), kept fixed within all true source boxes. If \(w=e^{L^\nu}\), with \(\nu=\delta\) or \(.24\), the absolute pointwise error is at most \(E_w(n)\), the number of omitted divisors. On every polynomial interval prefix \(X\le P\),
\[
\sum_{n\le X}E_w(n)\ll X e^{-c L^{1-\nu}},\qquad
\sum_{n\le X}E_w(n)^2\ll X e^{-c' L^{1-\nu}}.
\tag{4}
\]
The first follows by \(\lfloor X/v\rfloor\le X/v\) and Rankin at \(1/\log w\) on the squarefree smooth reciprocal product. The second follows from \(E_w\le\tau\) and \(\sum E_w^2\le(\sum E_w)^{1/2}(\sum \tau^3)^{1/2}\), with a harmless fixed log moment. These are **stretched exponential in log**, not polynomial savings.

Set \(g_b(m)=1_{m\in P-I}b_y(m)\). Also expand \(f\) by \(n=p k\), \(p\in\mathcal P\); since \(p>z\), the coefficient is exactly \(-(\log n)\sum_{p\in\mathcal P,p\mid n}\lambda(k)R_z(k)\). Define \(f_b\) by substituting \(b_z(k)\). We have
\[
\|g-g_b\|_2\ll \sqrt P e^{-cL^{1-\delta}},\qquad
\|f-f_b\|_2\ll \sqrt P e^{-c L^{.76}}.
\tag{5}
\]
Indeed the \(f\) square uses \(s(n)\le1/\sigma\) and (4) on \(k\le P/p\), then \(\sum_{p\in\mathcal P}1/p=O_\sigma(1)\); the extra use of \(\log n\) is absorbed. Since the original \(\|f\|_2\ll\sqrt P L\), \(\|g\|_2\ll\sqrt P\), the same holds for the truncations. Parseval and Cauchy now transfer the integral of the absolute product on **any** frequency region between these two pairs, at \(O_A(PL^{-A})\) error. This is why (4) need not absorb a polynomial Gauss cost: it is not used in any pointwise twist on that band.

## 4. The true short-prime slot at a good prime denominator

For good \(q\) and either \(w=y,z\), let \(X\ge c_J P^{1/2}\) be the scale of \(m\) or of \(k=n/p\) in the corresponding interval. Consider \(\sum b_w(n)e(a'n/q)e(\beta' n)\) on an actual interval at scale \(X\), \((a',q)=1,\ |\beta'|X\ll L^{J_0}\), with optional smooth log weight of size \(O(L)\). All prime factors of \(v\) in the convolution truncation are below \(w<q\).

On the multiples of \(q\), the exact relation \(b_w(qj)=-b_w(j)\) holds, since every retained \(v\) is coprime to \(q\). The rational phase is 1 there. Open the retained \(v\)-sum and use the unconditional \(\lambda\) arbitrary-log estimate at the true endpoint \(X/(qv)\gg P^{.4-\eta}\), plus \(\sum_v1/v=O(\log w)\) and partial summation. The result is \(O_A((X/q)L^{-A})\), paying all nonunit residues directly. The full unphased sum (with the slow archimedean weight) is \(O_A(XL^{-A})\) by the same argument at \(X/v\); thus so is the sum over units.

On units expand the rational additive phase in characters modulo \(q\). Its principal coefficient is exactly \(-1/(q-1)\) by the prime-modulus Ramanujan sum; its nonprincipal coefficient absolute sum is at most \(\sqrt q\) by Parseval on the unit group. The principal part is therefore \(O_A((X/q)L^{-A})\). For each nonprincipal \(\chi\), after opening \(v\le P^{1/10}\), (3) applies at \(X/v\gg P^{.4}\). Dirichlet twists multiply exactly, the reciprocal \(v\)-sum is fixed-log, and the slow-phase \(\beta'\) and log weight cost only fixed log powers in variation. Even after the complete Gauss loss \(\sqrt q=P^{\eta/2+o(1)}\), the upper is \(O(XP^{-40\eta})\), negligible compared with \((X/q)L^{-A}\). This yields the common bound \(O_A((X/q)L^{-A})\) for the true truncated rational sum uniformly over all numerators.

For \(g_b\), \(X=P\), \(a'=a\), \(\beta'=\beta\). For \(f_b\), each **actual** \(p\in\mathcal P\) is greater than \(q\), so the fixed prime-slot phase has numerator \(a'=ap\bmod q\) still reduced and archimedean phase \(\beta'=p\beta\) at \(X=P/p\), with exactly the same \(|\beta'|X\le L^{J_0}\). Sum over these true short prime slots by their bounded reciprocal mass; use \(\log(pk)\) as the optional log multiplier. Thus on the whole good band
\[
|S_{f_b}|+|S_{g_b}|\ll_A (P/q)L^{-A}.
\]
For each \(q\) there are at most \(q\) numerators and interval width \(2L^{J_0}/P\). Their integrated product is \(O_A(P q^{-1}L^{-A})\), after requesting extra log saving, and \(\sum_{Q\le q\le2Q}1/q=O(1)\). Together with (5) this proves (1) for the actual original coefficients. No prime BV in an arbitrarily chosen subset \(\mathcal P\) is assumed.

## 5. Cost of retaining the exact translated source selector

For actual integers \(n\in I\) with \(R_z(n)=1\), use the elementary one-variable Selberg upper sieve with its baseline root \(0\bmod\ell\) for all \(\ell\le z\). On a noncover witness add the \(jP\bmod\ell\) forbidden residues at the forced-empty packet/offset slots. These residues are distinct and nonzero, since all packet primes exceed \(M+1\) and avoid \(P\). As before the greedy witness saves \(L^{-M/200}\) relative to the baseline \(\kappa_z\asymp L^{-.24}\), with actual floor \(P^{.11}\) after taking divisor level \(P^{1/40}\) and all witness choices. Thus the source set on which \(f_C-f\ne0\) has size \(\ll P L^{-.24-M/200}+P^{.11}\). We use **no** reflected rough filter on this source \(\ell^2\) estimate. Since \(|f|\ll_\sigma L\) and \(\|g\|_2^2\ll P L^{-\delta}\) by elementary one-variable rough sieve, Parseval gives on any frequency region
\[
\int |S_{f_C-f} S_g|
\ll P L^{.88-\delta/2-M/400}+P^{.57}.
\]
This is (2). It measures the genuinely marked frequency product, not just the additive total at \(P\). The remaining generic minor set may contain large actual signed contribution; no estimate there is implied.
