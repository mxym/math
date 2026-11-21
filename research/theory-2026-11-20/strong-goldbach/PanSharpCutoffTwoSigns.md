# Two signed masses exceeding the natural main scale by a log-log factor

Fix \(0<v<1/6\), \(Q=P^v\), \(L=\log P\), \(I=[P/3,2P/3]\), \(X=P/3\). Write \(S(P)=2C_2\prod_{s\mid P,s>2}(s-1)/(s-2)\) for the even binary singular series. Put
\[
 B(r)=-\sum_{d\mid r,\ d\le Q}\mu(d)\log d,\qquad a(r)=B(r)-\Lambda(r).
\]
The asymmetric long Pan coefficient agrees with \(a\) on inputs coprime to \(P\). At **every sufficiently large even \(P\)** there are two disjoint, explicitly described classes of \(p\in I\) prime with \(r=P-p\) squarefree composite, each with at least
\[
 \gg_v S(P)P\,\frac{\log\log P}{(\log P)^2}
\]
prime inputs. On the first, \(B(r)<-.99\log Q\); on the second, \(B(r)>.99\log Q\). In both \(P^-(r)\ge\exp(c_v\sqrt{\log P})\). In particular the positive and the negative parts separately of the **actual prime–composite raw Pan sum**, per orientation, are both
\[
 \gg_v X S(P)\log\log P.
\]
Indeed \(a(p)=-\log p,\ a(r)=B(r)\) on these classes. This is a lower bound on each unsigned part, not on their difference. The full signed prime–composite row remains of order \(XS(P)\), and no conclusion on the prime-pair atom follows. The cutoff is a fixed sub-sixth exponent, not the near-square-root split.

## 1. Disjoint shells with deterministic coefficients

Choose a fixed \(s>2\) such that \(v(1+s)<1/2\). Fix a sufficiently small positive \(\kappa<.02\), with \(v(1+s+\kappa)<1/2\); it will be made small relative to the positive sieve constants below. For every dyadic \(y=2^{-j}\) with \(L^{-1/2}\le y\le y_0\) let \(z_y=Q^{2y}\), where \(y_0<.005\) and \(y_0\ll\kappa\) is fixed sufficiently small. Use exponents \(x_\ell=\log\ell/\log Q\). Mark one of:
* type I: one prime \(\ell\), \(1-x_\ell\in[y,2y)\);
* type II: two prime labels \(\ell_1,\ell_2\), with \(x_{\ell_1}\in[.40,.43]\) and \(1-x_{\ell_1}-x_{\ell_2}\in[y,2y)\). In particular \(x_{\ell_2}\in(.56,.61)\).

Let \(M\) be the product of the marked labels. Count \(r=P-p\) divisible by \(M\) which have no other prime factors \(\le Q\) except in \((z_y,Q^\kappa]\). The distinct prime factors in that allowed interval are called small. Require at least two small primes and \(\sum_{\ell\ {\rm small},\ell\mid r}x_\ell<.3\). Factors above \(Q\) are unrestricted. The large labels are now the *unique* large labels up to \(Q\), and \(M\) determines its shell. Thus the events are disjoint across all shells and types.

Every subset of the small labels fits below \(Q\); in type II it also fits with either single large label. For at least two distinct small labels, their full subset sums weighted by \((-1)^{|T|}\) cancel both a constant and a linear form in the labels. In type I the only short divisor using the one large label is that label itself: \(M z_y>Q\). In type II the only short divisor using both is \(M\) itself, for the same reason. Consequently **exactly**
\[
 B(r)=+\log M\quad\text{(I)},\qquad B(r)=-\log M\quad\text{(II)} .
\]
This argument uses distinct labels because \(\mu\) ignores repeated prime powers, and does not initially assume squarefreeness. \(\log M\ge(1-2y_0)\log Q\).

## 2. Uniform arithmetic counting in a shell

Suppress the harmless central \(p\mid P\) exceptions: they cannot affect the final bounds (there are \(O(\log P)\) of them), and in expanded progressions their removal costs a fixed power saving. For unit marked products \(M\), the base condition is \(p\equiv P\bmod M\). The forbidden primes \(t\le Q\) lie in \([2,z_y]\cup(Q^\kappa,Q]\), excluding \(t\mid PM\). A prime dividing \(P\) does not divide \(r\) when \(p\nmid P\). At each forbidden prime \(t\) remove one unit residue of \(p\); the sieve density is \(1/(t-1)\). The prime 2 divides \(P\) and is excluded from this product. Write \(V_y(M)\) for the product of the corresponding \(1-1/(t-1)\). Uniformly over all these shells and labels,
\[
 V_y(M)=(1+o(1))\,S(P)e^{-\gamma}\frac{\kappa}{2y\log Q},\qquad
 V_{\rm all}(M)=(1+o(1))\,S(P)e^{-\gamma}/\log Q,                 \tag{1}
\]
where the second product forbids all primes through \(Q\) except the divisors of \(PM\). Indeed the factors up to \(z_y\) divided by \(\prod_{t\le z_y}(1-1/t)\) give \(S(P)(1+o(1))\); the exceptional tail costs \(O(L/z_y+1/z_y)\). On \((Q^\kappa,Q]\) one gets the ordinary Mertens ratio \(\kappa(1+o(1))\); omitting the at most two prescribed large primes changes this by \(1+o(1)\). All errors are uniform since even the smallest \(z_y\) is at least \(\exp(2v\sqrt L)\).

Use the dimension-one upper and lower linear sieves at level \(D=Q^s\) for all counts here. Their main multipliers relative to the appropriate \(V\) may be bounded by fixed numbers \(0<c_s<C_s<\infty\): the lower function \(f_1(s)>0\) for every \(s>2\) and the upper \(F_1(s)<\infty\). The dimension bound is uniform: on each interval \([w,t]\) the inverse local product is bounded by the corresponding full product over odd primes, which is \((\log t/\log w)(1+O(1/\log w))\) by Mertens and the summable \(O(l^{-2})\) corrections (enlarge the constant for small \(w\)). These are the usual [linear sieve main-sum bounds, Friedlander–Iwaniec, *Opera de Cribro*, Ch. 11](https://www.ams.org/books/coll/057/); choose \(c_s\) below \(f_1(s)\) and \(C_s\) above \(F_1(s)\) for all large \(Q\). For the lower and upper applications the very same \(s,v\) work.

Specifically, fix \(M\), impose its divisibility, and optionally mark one more small prime \(k\) in the allowed interval. The log-prime main term before sieving is \(X/\phi(Mk)\), with \(k=1\) if not marked. Each additional sieve divisor \(d\le D\) has \((d,MkP)=1\) and gives \(p\equiv P\bmod Mkd\); main \(X/\phi(Mkd)\). All moduli are at most \(Q^{1+\kappa+s}\le P^{1/2-c_v}\). The total absolute Bombieri–Vinogradov remainders are \(O_A(PL^{-A})\) for any fixed \(A\), *summed over the marked labels*, including the two interval endpoints. Indeed a modulus has at most \(\tau(q)^3\) ways to select its up to three labeled prime factors and the remaining sieve divisor is forced. The shell is determined by \(M\). Sieve coefficients have absolute value at most 1 (or a fixed divisor bound suffices). Weighted maximal-residue BV follows from ordinary BV and Cauchy–Schwarz, using the trivial progression estimate and divisor moments for the extra weights. The per-modulus cost to omit prime powers or prime divisors of the target, even using \(O(\sqrt P L^2)\) for the former, retains a power saving in this strict range, with all multiplicities. One can alternatively use this total error for each individual shell, still negligible after their \(O(\log L)\) sums. The model approximations made in (1) are *relative* to each shell main, not merely absolute errors of order \(X\).

Let \(H_y=\sum_M 1/\phi(M)\) in the shell restricted to units, for either fixed type. Then \(H_y\asymp y\) uniformly. For type I use prime harmonic summation on \([Q^{1-2y},Q^{1-y}]\). For type II, first fix \(x_{\ell_1}\in[.4,.43]\); the harmonic sum in the second window is between two absolute positive multiples of \(y\), then the first window contributes a fixed positive mass. The ordinary Mertens estimate with error \(O(1/\log T)\) at these large endpoints gives \(O_v(1/L)=o(y)\) even on the thinnest windows (a prime on a boundary costs a negligible reciprocal). Omitting target divisors has exponentially small cost on these ranges. The labels have disjoint exponent ranges, hence are not overcounted.

Write \(T_y=X\sum_M V_y(M)/\phi(M)\asymp X S(P)\kappa/\log Q\). By the lower sieve, the log-weight of all candidates before imposing the two restrictions on the small-prime labels is at least \(c_s T_y-O_A(PL^{-A})\). For the total small exponent mass use one extra mark \(z_y<k\le Q^\kappa\), of weight \(\log k/\log Q\le\kappa\); the upper sieve has the same product and gives an upper bound \((C_s+o(1))\,\kappa T_y+O_A(PL^{-A})\), since \(\sum (\log k)/((k-1)\log Q)\le\kappa+O(1/\log Q)\). Markov charges at most this divided by .3 for the loss with exponent mass \(\ge.3\). Choose \(\kappa\) sufficiently small that this costs \(<c_s T_y/4\), apart from the stated arithmetic remainder.

If there are zero small labels, upper-sieve *all* primes through \(Q\) except those dividing \(PM\). If there is exactly one, sum over the possible additional marked \(k\); sieve all except divisors of \(PMk\), changing \(V_{\rm all}(M)\) by \(1+O(1/z_y)\). The positive counts may be bounded even allowing powers of \(k\). The relative price of both cases together, *relative to \(T_y\)*, is at most
\[
 (C_s+o(1))\frac{2y}{\kappa}\bigl(1+\log(\kappa/(2y))+o(1)\bigr)
\]
plus the same absolute BV remainder divided by \(T_y\). This follows from (1) and prime harmonic summation for \(k\); its additive error tends uniformly to zero because \(z_y\ge\exp(2v\sqrt L)\). Fix \(y_0\) so small relative to \(\kappa,c_s,C_s\) that this costs \(<c_s T_y/4\) throughout. The stated \(o(1)\) factors multiplying the log term are bounded uniformly, and \(y\log(1/y)\to0\).

There remains \(\gg_v XS(P)/\log Q\) prime log-weight in *each* shell and each type. There are \(\gg\log L\) disjoint shells of the indicated dyadic sizes. All their remaining squareful \(r\) have a square of a prime \(>\exp(2v\sqrt L)\); in the **already identified disjoint classes**, where \(|B(r)|=\log M\le\log Q\), removing all of them costs in signed mass at most \(O(PL^2\exp(-2v\sqrt L))\). The log-count cost uses just \(L\) in place of \(L^2\). This argument does not multiply the squareful count by a general maximum of the divisor function. Summing the shell counts and using \(\log M\asymp\log Q,\ \log p\asymp L\) proves all assertions. Either orientation of this particular prime–composite row gives the same result, since \(p,r\) are both units modulo every prime divisor of \(P\).

**Comparison.** The isolated-divisor idea at a sharp Möbius cutoff is classical. In particular [Granville–Koukoulopoulos–Maynard, *Sieve weights and their smoothings*, §1.1, (1.2)–(1.6)](https://arxiv.org/pdf/1606.06781) use Ford's exactly-one-divisor interval bounds to show failure of sharp weights as sieve majorants on unrestricted integers, and study their even moments. No priority is claimed for the underlying discontinuity. Here two explicit opposite signs of the *logarithmic* Pan coefficient are certified separately on prime reflections at every target, with a common-atom-free physical set in each shell. The conclusion obstructs an absolute-error budget of main-term size at this fixed split. It does not estimate the cancellation between these growing masses, move the split to the square root, or solve Goldbach.

[Pham’s October 2026 boundary-correlation paper](https://www.preprints.org/manuscript/202610.3061) analyzes a different sharp boundary, with coefficient moments and a limitation on a row-wise absolute majorant. The present divergence concerns the signs of actual raw Pan terms, not a derived absolute character majorant, and uses a different short-cutoff range.
