# Absolute progression distribution to exponent .512 for a genuine long prime slot

## Statement and scope

Write \(L=\log x\), and allow fixed positive constants in \(MT\asymp x\). Let \(a\) be any nonzero integer with \(|a|\le Cx\), and suppose
\[
x^{.5123}\ll T\ll x^{.5129},\qquad x^{.499}\ll Q\ll x^{.512}.
\tag{1}
\]
The implicit constants specifying these ranges are fixed. Let \(|\alpha_m|,|\beta_n|\le1\) be supported on \([M,2M]\), \([T,2T]\), respectively. The support of \(\beta\) consists of **primes \(n\nmid a\)**. Assume its primitive Siegel–Walfisz property: for every fixed \(B,C_1>0\),
\[
\max_{\substack{1<f\le L^B\\\chi\bmod f\ {\rm primitive}}}
\left|\sum_n\beta_n\chi(n)\right|\ll_{B,C_1} T L^{-C_1}.
\tag{2}
\]
Then, uniformly in \(a\) and these scales,
\[
\sum_{\substack{Q<q\le2Q\\(q,a)=1}}
 \left|\sum_{m,n}\alpha_m\beta_n
 \left({\bf1}_{mn\equiv a\ (q)}
        -\frac{{\bf1}_{(mn,q)=1}}{\varphi(q)}\right)\right|
 \ll_A xL^{-A}
\quad(A>0).
\tag{3}
\]
All constants also allow the constants in (2). Neither fixed small \(a\), prime \(q\), nor a factorization of \(q\) is required. The coefficients in a rectangle are independent of \(q\); \(\alpha\) need not satisfy (2) or be supported on primes. Real or complex coefficients are allowed. An archetypal \(\beta\) is the indicator of primes on any subinterval of \([T,2T]\), or that indicator multiplied by \(\log n/L\) and a fixed bounded-variation weight on the slot. Removing the prime divisors of \(a\) changes (2) by \(O(\log(2|a|)/\log T)=O(1)\), uniformly in \(a\) (in fact at most one here for large \(x\)). Do not leave these divisors in the dispersion proof.

For two prime slots, (3) extends to the sum over all \(q\le x^{.512}\), to fixed divisor-power weights in this sum, and to physical interval restrictions on \(mn\asymp x\). Details follow the proof. This is a progression distribution theorem, not a prime-pair assertion or an evaluation of a two-prime correlation. A weighted almost-prime sieve application is not used here.

## The dispersion square and its normalization

Use \(e(z)=e^{2\pi i z}\) and \(\widehat\psi(t)=\int \psi(u)e(-tu)\,du\). Choose fixed nonnegative smooth functions \(\psi,\varpi\), supported in \((1/2,3)\), \((1/2,5/2)\) respectively and at least 1 on \([1,2]\). Write
\[
w(q)=\varpi(q/Q){\bf1}_{(q,a)=1},\quad B_0=\sum_n\beta_n,\quad
b_q(c)=\sum_{n\equiv c\ (q)}\beta_n .
\]
Thus \(w\) is a dimensionless majorant of the indicated dyadic modulus range, **not** an averaging probability or a factor \(1/q\). For all moduli in its support, \(q<T\) for sufficiently large \(x\). Each \(n\) is a prime greater than \(q\), hence is a unit modulo \(q\). For a unit \(m\) the discrepancy in (3) is obtained from \(b_q(a\bar m)-B_0/\varphi(q)\), and is zero for a nonunit \(m\). Cauchy–Schwarz first on \(q\), then on \(m\) with \(\psi\) a majorant, bounds the square of (3)'s left side by
\[
O(MQ)\sum_q w(q)\sum_{\substack{m\in\mathbb Z\\(m,q)=1}}
 \psi(m/M)\left|b_q(a\bar m)-B_0/\varphi(q)\right|^2
 =O(MQ)\bigl(W-2\Re V+U\bigr).
\tag{4}
\]
Here \(W,V,U\) are the \(b\bar b\), \(b\overline{B_0}/\varphi\), and \(|B_0|^2/\varphi^2\) terms, with common weights as in (4).

For a unit class \(c\bmod q\) use
\[
\sum_{m\equiv c\ (q)}\psi(m/M)=\frac Mq\sum_{h\in\mathbb Z}\widehat\psi(hM/q)e(hc/q).
\tag{5}
\]
For \(W,V\) truncate at \(H=(Q/M)x^\epsilon\), with fixed \(\epsilon>0\) small. As \(q\asymp Q\), the omitted sum, even with the crude polynomial bounds on the number and size of all other coefficients, is \(O_D(x^{-D})\) for every fixed \(D\); use arbitrary Schwartz decay with \(\epsilon\) fixed. For \(U\), use
\[
\sum_{(m,q)=1}\psi(m/M)=\frac{M\varphi(q)}q\widehat\psi(0)+O_\psi(\tau(q))
\]
by Möbius inversion and the uniform one-dimensional Riemann sum. This costs \(O_\epsilon(x^\epsilon T^2/Q)\) in (4)'s inner expression, since \(q/\varphi(q)\ll 1+\log\log(3q)\). All powers \(x^{O(\epsilon)}\) below have absolute indicated-order exponents, independent of \(A\); the implicit constants may depend on \(\epsilon\), the smoothings, and fixed range constants.

### The joint zero mode

The three zero modes in \(W-2\Re V+U\) combine exactly to
\[
M\widehat\psi(0)
 \sum_q\frac{w(q)}q
   \sum_{\substack{c\bmod q\\(c,q)=1}}
       \left|b_q(c)-B_0/\varphi(q)\right|^2 .
\tag{6}
\]
In particular, they are not three separately discarded principal terms. By character orthogonality the inner variance is \(\varphi(q)^{-1}\sum_{\chi\bmod q,\chi\ne\chi_0}|\sum_n\beta_n\chi(n)|^2\). An induced character contributes exactly its primitive short sum: **every** \(n\) is a unit modulo \(q\), not only modulo the conductor. For a conductor \(f\), \(\sum_{q\le (5/2)Q,\ f\mid q}1/\varphi(q)\ll L/\varphi(f)\), by \(\varphi(fj)\ge\varphi(f)\varphi(j)\). The primitive multiplicative large sieve on \(f\asymp F\) gives the variance summed over all these \(q\), from this conductor band, \(\ll L(T^2/F+TF)\). For \(F\le L^{B_1}\) use (2), choosing its exponent after \(B_1\); for larger \(F\) sum the dyads. This bounds the summed variance by \(O_A(T^2L^{-A}+TQ L^2)\), after increasing the log reserve in (2) as needed. Multiplication by \(O(M^2)\), from (4) and (6), gives the normalized bound \(O_A(L^{-A}+(Q/T)L^2)\) on dividing by \((MT)^2\).

### The \(W\)-diagonal

The \(n_1=n_2\) contribution to \(W\) before Poisson is bounded by \(O_\epsilon(x^{1+\epsilon})\): for a physical pair \(m,n\) in the supports, the possible \(q\)'s divide \(mn-a\), and \(mn-a\ne0\) because \(n\nmid a\). Its magnitude is \(O(x)\), so it has \(O_\epsilon(x^\epsilon)\) divisors. The corresponding zero mode is \(O(MT)\), simply summing \(M/q\) over \(q\asymp Q\). We already used its zero mode in (6), so its nonzero part costs \(O_\epsilon(x^\epsilon Q/T)\) in the normalized square. Counting all formal diagonals as \(O(QT)\) would not suffice above the root.

### The \(V\)-term

For a fixed \(0<|h|\le H\) and prime \(n\) in the support, additive reciprocity gives
\[
e(ah\bar n/q)=e(-ah\bar q/n)e(ah/(qn)).
\tag{7}
\]
Here \(n\nmid ah\): by assumption \(n\nmid a\), and \(H<T\) for large \(x\). In the outer \(q\)-sum, extract \(MT/Q^2\) using \(|B_0|\le T+1\), \(M/q\), and \(1/\varphi(q)=q^{-1}(q/\varphi(q))\). Write the last arithmetic ratio as \(\sum_{d\mid q}\mu^2(d)/\varphi(d)\), and the unit restriction as \(\sum_{e\mid a,e\mid q}\mu(e)\) (divisors of \(|a|\) throughout). For \(q\) a multiple of \([d,e]\) that occurs, \([d,e]\le (5/2)Q<n\). Completion modulo the prime \(n\), with the incomplete range of \(q/[d,e]\) of length \(<n\), bounds the reciprocal sum for any interval by \(O(\sqrt n\log n)\) via the Weil bound for the complete Kloosterman sums. The zero additive Fourier coefficient is bounded by the corresponding complete Ramanujan sum, so entails no exceptional term. The extra smooth factors in \(q/Q\) and \(\widehat\psi(hM/q)e(ah/(qn))\) have sup norm plus total variation \(\ll x^{O(\epsilon)}\) over the support, since \(|a|H/(QT)\ll x^\epsilon\). Partial summation, \(\sum_{d\le (5/2)Q}1/\varphi(d)\ll L\) and \(\tau(|a|)\ll_\epsilon x^\epsilon\) give
\[
 |V_{\ne0}|\ll_\epsilon x^{O(\epsilon)}
       \frac{MT^{5/2}H}{Q^2}.
\tag{8}
\]
This is \(O_\epsilon(x^{O(\epsilon)}T^{1/2}/M)\) in the normalized square.

### The \(W\)-off-diagonal: the complementary modulus and trilinear sum

For \(n_1\ne n_2\), the support condition in \(W\) is \(q\mid n_1-n_2\); the residue for \(m\) is \(a\bar n_1\bmod q\). Set
\[
r=(n_1-n_2)/q,\qquad 0<|r|\ll T/Q,\qquad q=(n_1-n_2)/r.
\tag{9}
\]
The two prime slots here are separate copies of the same coefficients. Since these primes are distinct, \((n_1,n_2)=1\), and since \(q<n_1\) also \((q,n_1)=1\). Applying (7) with \(n_1\), and using \(rq\equiv-n_2\bmod n_1\) so that \(\bar q\equiv-r\bar n_2\bmod n_1\), changes the oscillating phase to
\[
e(ahr\bar n_2/n_1)\,e(ah/(q n_1)).
\tag{10}
\]
This is valid for either sign of \(r\). The second factor will be kept in the smooth cutoff, not discarded. Open \({\bf1}_{(q,a)=1}=\sum_{e\mid a,e\mid q}\mu(e)\) **before** decoupling. For fixed \(r,e\) with \(e\le(5/2)Q\), the exact joint arithmetic condition, apart from occurrence \(q>0\) in the smoothing, is
\[
n_1\equiv n_2 \pmod{|r|e}.
\tag{11}
\]
In particular (11) enforces integrality of \(q\) as well as \(e\mid q\). Do not impose any assumed distribution of primes in those classes.

Partition each interval \([T,2T]\) into half-open boxes of length \(|r|Q\) (with an end box if necessary). The condition \(Q/2<q<(5/2)Q\) pairs each box with \(O(1)\) boxes for the other slot, with the order prescribed by \(\operatorname{sgn}r\). There are \(O(T/(|r|Q))\) such pairs, as \(|r|Q\ll T\). This means **fine subintervals**, not substituting their length for \(T\) in a theorem whose denominators have size \(T\). In each box pair, restrict both sequences to one common class \(j\bmod |r|e\); for a single class the product of their \(\ell^2\) norms is \(\ll 1+Q/e\). Summed over common classes and box pairs this is
\[
\ll \frac{T}{|r|Q}\,|r|e\,(1+Q/e)\ll T.
\tag{12}
\]
The estimate includes \(e\asymp Q\), when the boxes can have only a bounded number of points per class. Splitting these classes uses coefficient support, and introduces no additional outside phase.

Write \(M/q=(M/Q)/(q/Q)\). For frequencies \(h\) of one sign in one dyad \(|h|\asymp A_1\le H\) (truncated prefix for the last dyad), retain as a smooth real-variable multiplier
\[
\frac{\varpi(q/Q)}{q/Q}\,\widehat\psi(hM/q)\,e(ah/(q n_1)),
 \qquad q=(n_1-n_2)/r.
\tag{13}
\]
It is extended by zero away from \(q/Q\in(1/2,5/2)\). Its mixed first-order derivatives in each of \(n_1,n_2,h\) are \(\ll x^{O(\epsilon)}\) after normalization by the interval lengths \(|r|Q,|r|Q,A_1\): differentiating \(q\) on those scales costs \(O(Q)\), \(hM/q=O(x^\epsilon)\) with the same scaled derivative bounds, and the phase in (13) costs at most \(|a|H/(QT)\ll x^\epsilon\). This proves the needed variation for ordinary three-dimensional partial summation, treating (13) as a factor in front of a supremum of trilinear prefix sums; it does not assume separability of (13).

Use [Bettin–Chandee, Theorem 1, equation (1.2)](https://arxiv.org/abs/1502.00769) on the prefix sums as follows: variable \(m_{\mathrm{BC}}=n_2\), variable \(n_{\mathrm{BC}}=n_1\), frequency index \(a_{\mathrm{BC}}=|h|\), parameter \(\vartheta=ar\operatorname{sgn} h\). The two coefficient vectors are the indicated restricted copies of \(\beta\), conjugating the second copy as appropriate; the third is an interval/prefix indicator with norm \(O(\sqrt{A_1})\). The theorem's \((m_{\mathrm{BC}},n_{\mathrm{BC}})=1\) omits exactly the unwanted prime diagonals. In particular, there is **no use of a long modulus \(re\)** as a denominator of this theorem. Both denominator/numerator-variable scales are \(T\), the independent frequency scale is \(A_1\), and
\[
|\vartheta|A_1/T^2\ll |a|(T/Q)H/T^2\ll x^\epsilon
\]
because \(MT\asymp x\). The estimate is
\[
\ll_\epsilon x^{O(\epsilon)}\|\beta_1\|_2\|\beta_2\|_2
      \sqrt {A_1}\bigl(A_1^{7/20}T^{19/20}
                     +A_1^{1/2}T^{7/8}\bigr).
\tag{14}
\]
The signed weights in \(\mu(e)\) can now be summed absolutely, using \(\tau(|a|)\ll_\epsilon x^\epsilon\); the sign of \(r\) and the frequency sign cost constant factors, and the dyads at most a log. By (12) and the \(O(T/Q)\) actual \(r\)'s, the off-diagonal nonzero part of \(W\) is at most
\[
O_\epsilon\left(x^{O(\epsilon)}\,\frac M Q\,\frac{T^2}{Q}
          \sqrt H (H^{7/20}T^{19/20}+H^{1/2}T^{7/8})\right).
\tag{15}
\]
Multiplying by \(MQ/(MT)^2\) gives \(x^{O(\epsilon)}\bigl(H^{17/20}T^{19/20}/Q+HT^{7/8}/Q\bigr)\).

## Directed exponent checks

Put \(b=\log T/L,\ c=\log Q/L\). Constants in (1) only shift these exponents by \(O(1/L)\); \(M=x^{1-b+O(1/L)}\). The following exponents exclude \(x^{O(\epsilon)}\) or logarithmic factors; \(H\) contributes \(c+b-1\) before its \(x^\epsilon\) buffer.

| Term in \(\Delta^2/(MT)^2\) or auxiliary check | Exponent | Worst directed end | Upper bound |
|---|---:|---:|---:|
| \(Q/T\) (zero modes, \(W\) diagonal, \(q<T\)) | \(c-b\) | \(c=.512,b=.5123\) | \(-.0003\) |
| \(U\) floor | \(b-1\) | \(b=.5129\) | \(-.4871\) |
| \(V\) nonzero | \(3b/2-1\) | \(b=.5129\) | \(-.23065\) |
| \(W\) nonzero, first term | \(9b/5-17/20-3c/20\) | \(b=.5129,c=.499\) | \(-.00163\) |
| \(W\) nonzero, second term | \(15b/8-1\) | \(b=.5129\) | \(-.0383125\) |
| \(H<T\) | \(c-1\) | \(c=.512\) | \(-.488\) |
| \(H>1\) (lower bound, no buffer) | \(c+b-1\) | \(c=.499,b=.5123\) | \(+.0113\) |

Choose \(\epsilon\) sufficiently small compared with the fixed margins, then choose the SW reserve after \(A\); (3) follows from (4). The companion exact rational checker computes these maxima/minima at the corners and works unchanged under optimized Python.

## Two prime slots and physical cutoffs

Suppose also that \(\alpha\) is supported on primes, with no SW assumption on their bounded weights. We may extend (3) to \(q\le x^{.499}\) by the primitive large sieve. Open the centered discrepancy in nonprincipal Dirichlet characters. The \(\beta\) sums at imprimitive characters equal their inducing primitive sums since \(n>q\); on the \(\alpha\) side the discrepancy on replacing by the primitive sum is \(O(1)\), since \(M\gg x^{.4871}\) and any such \(q\) has at most one prime factor \(\ge M\). Its total error is
\[
 \ll\sum_{q\le x^{.499}}\bigl(T/\sqrt q+\sqrt T\bigr)
 \ll T x^{.499/2}+x^{.499}\sqrt T\ll x^{.763},
\]
using character Cauchy and the trivial bound \(O(1+T/q)\) for the number of long-slot integers per residue. Now the induction weight \(O(L/\varphi(f))\) from (6) lets one apply primitive character Cauchy and the large sieve on each conductor band \(f\asymp F\). The bound with no SW savings is
\[
\ll L\sqrt{MT}\,\frac{\sqrt{(M+F^2)(T+F^2)}}{F}.
\]
All but the term \(O(LMT/F)\) save a fixed power, since \(F\ll x^{.499}\) and \(M,T\) are both polynomial. Sum for \(F>L^{B_1}\); for \(F\le L^{B_1}\) use (2) on the long slots, choosing reserves in that order. This proves the claimed low-modulus extension. The boundary of the two ranges can be covered with dyads overlapping by a fixed factor, since (1) has fixed-factor slack.

Let the two primes \(m,n\) have sizes in the corresponding full bands \(m\asymp x/n,\ x^{.5123}\ll n\ll x^{.5129}\), with a common physical restriction \(mn\) in any one interval \(I\subset[c_0x,C_0x]\) for fixed \(0<c_0<C_0\). Partition into rectangles with relative steps \(1+L^{-B_2}\), using at most \(L^{O(B_2)}\) rectangles. The long slot is restricted to an interval, so its true prime indicator or \(\log n/L\) continues to obey (2), uniformly in the endpoints. Arbitrary short-slot weights may be retained. Each retained rectangle has \(MT\asymp x\), and an omitted boundary rectangle can contribute only pairs with \(mn\) in an \(O(xL^{-B_2})\) interval around a physical endpoint. The number of such integer pairs in the bands is \(O(xL^{1-B_2}+x^{.49})\) by fixing the short factor and counting the other. Partition at any prescribed separate prime-size cutoffs rather than approximating those cutoffs. To bound the total omitted discrepancy, use
\[
\sum_{\text{boundary pairs }(m,n)}\tau(|mn-a|)\ll
\bigl(\#\text{boundary pairs}\bigr)^{1/2}
        \left(\sum_{\substack{y\asymp x\\ y\ne a}}
          \tau(y)\tau(|y-a|)^2\right)^{1/2}
\ll \bigl(\#\text{boundary pairs}\bigr)^{1/2} \sqrt{x}\,L^{O(1)}.
\]
The last step follows by Cauchy from ordinary divisor moments on intervals contained in \([1,O(x)]\). The modeled boundary error is at most \(O(L)\) times the number of pairs. Again \(mn=a\) is excluded at the source; no divisor bound is used at zero. Choose \(B_2\) large, then apply (3) and the low-modulus estimate with sufficient log reserve to all retained rectangles.

Finally for a fixed nonnegative integer \(K\), if \(E_q\) denotes any of those actual discrepancies, then
\[
\sum_{q\le x^{.512}}\tau(q)^{2K}|E_q|\ll_K x L^{O_K(1)}.
\tag{16}
\]
Indeed the occurrence part is at most \(\sum_{y\asymp x,\ y\ne a}\tau(y)\tau(|y-a|)^{2K+1}\), and the modeled part is bounded by \(O(xL)\sum_{q\le x^{.512}}\tau(q)^{2K}/\varphi(q)\), each \(xL^{O_K(1)}\) by elementary divisor moments. Cauchy between (16) and the unweighted absolute discrepancy proves the analogue of (3) with \(\tau(q)^K\) in the full sum. In the two-prime application, one can therefore replace the reduced-residue principal numerator by the full source mass, at an error smaller than any required log order: the long prime cannot divide these moduli, and a deleted short prime \(p\gg x^{.4871}\) contributes at most \(O(x/p)\) physical products, with
\[
 \sum_{\substack{q\le x^{.512}\\p\mid q}}\frac{\tau(q)^K}{\varphi(q)}
       \ll_K \frac{L^{O_K(1)}}{p}.
\]
Sum this over the short primes (even over integers \(p\ge c x^{.4871}\)). This replacement is not an assertion for the arbitrary short integer coefficients in (3).

Thus for an even target \(a=x=N\), a literal balanced source with a long prime in \(N^{[.5123,.5129]}\) and \(mn\) in a fixed central interval has an absolute distribution estimate for reduced classes \(mn\equiv N\bmod q\) with \((q,N)=1\) to this level. This is a genuine source for reflected sieve questions; the distribution theorem alone does not evaluate which reflected partners are primes.

## Sources and comparison

The only trilinear estimate imported is the established [Bettin–Chandee theorem](https://arxiv.org/abs/1502.00769). Complementary-modulus dispersion and additive reciprocity are standard, and also appear in [Fouvry–Radziwiłł, §4](https://arxiv.org/abs/1812.00562v2). [Wright, August 2026, *Trilinear Kloosterman fractions II*, Theorem 2.2](https://arxiv.org/html/2608.27732v1#S2) also uses subdyadic intervals, and its **stated** range for more general real divisor-bounded coefficients with a Siegel–Walfisz long slot covers the real archetypal prime-slot application above in the overlap \(1\le |a|\le X=MT\): its lower \(Q\)-exponent \(34b-17\) is at most \(34(.5129)-17=.4386<.499\), and its upper exponent \(b\) is at least \(.5123>.512\). Both leave room for the theorem's fixed \(\varepsilon\). No priority is claimed in that overlap. Here the restricted **true long-prime slot**, prime diagonals, and the complete treatment of \(e\mid a\) give an independent direct proof with the original trilinear inequality; neither the proof nor the theorem claimed by Wright is used as an input, and we do not claim his general coefficient range. Allowing the actual moving macroscopic residue \(a\) is explicit in (7), (9)–(15), including when \(|a|\) is a fixed multiple of \(MT\).
