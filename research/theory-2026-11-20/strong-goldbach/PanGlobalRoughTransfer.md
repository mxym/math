# A global signed roughness transfer for Pan's actual binary Goldbach remainder

Fix \(0<v<1/2\), let \(P\) tend to infinity through even integers, and set \(Q=P^v\), \(z=P^\epsilon\), \(0<\epsilon<v\). For \(n+r=P\) define
\[
 a_Q(n)=\sum_{d\mid n,\ d>Q}\mu(d)\log d,\qquad
 a_Q^*(r)=\sum_{d\mid r,\ d>Q,\ (d,P)=1}\mu(d)\log d .
\]
Write \(R_Q\) for the sum of their products, \(R_{Q,z}\) for that sum with **both physical inputs** free of prime divisors \(\le z\), and \(G\) for the ordered sum of \(\log p\log q\) on true prime pairs \(p+q=P\). Use the usual even Goldbach singular series \(\mathfrak S(P)=2C_2\prod_{l\mid P,l>2}(l-1)/(l-2)\), \(C_2=\prod_{l>2}(1-1/(l-1)^2)\); Euler-product letters are primes. Put
\[
 u=v/\epsilon,\quad s=(1/2-v)/(2\epsilon),\quad
 b(u)=e^{-\gamma}\int_0^{u-1}\rho(t)\,dt ,
\]
where \(\rho\) is the Dickman function, not a probabilistic approximation to a signed divisor weight.

**Theorem.** For \(s\) greater than an absolute constant,
\[
 \frac{R_Q-R_{Q,z}}{P\mathfrak S(P)}
 =-(1-b(u))^2+O(u^4e^{-s})+o_{v,\epsilon}(1).                  \tag{1}
\]
The numerical constant in the big O is absolute. In particular for *any* fixed \(v<1/2\) and tolerance \(\eta>0\), choose \(\epsilon>0\) sufficiently small depending on \(v,\eta\), then (1) gives absolute signed loss less than \(\eta P\mathfrak S(P)\) for every sufficiently large even \(P\). Each of the two remaining inputs has at most \(\lfloor1/\epsilon\rfloor\) prime factors counted with multiplicity. There is no sum of absolute values of omitted terms in (1). This is a global physical statement, not an assertion restricted to certain modulus columns or to the mean over targets.

In each orientation the signed prime–composite row on the rough set, divided by \(P\mathfrak S(P)\), equals \(-b(u)+O(u^2e^{-s})+o_{v,\epsilon}(1)\). The signed both-composite row there equals \(b(u)^2+O(u^4 e^{-s})+o_{v,\epsilon}(1)\). The unmasked counterparts are \(-1+o_v(1)\) in each orientation and \(+1+o_v(1)\), respectively. These are signed asymptotics up to a controlled fixed-sieve-level error, **not** sign estimates for the remaining full rough sum, which retains the original prime-pair atom. In particular the result is consistent with this atom being zero; it is not a proof of Goldbach. The order of parameters is fixed \(v\), then sufficiently small fixed \(\epsilon\), then \(P\to\infty\); no numerical fixed-rank bound is claimed at \(v=1/2\) or a varying \(v\to1/2\).

## 1. The full signed rows at the changed cutoff

Denote by \(B(n)=-\sum_{d\mid n,d\le Q}\mu(d)\log d\) and \(B^*(r)\) the corresponding negative short sums (the latter excludes divisors noncoprime to \(P\)). If \(r_c\) is the maximal divisor of \(r\) coprime to \(P\), then **exactly**
\[
 a_Q(n)=B(n)-\Lambda(n),\qquad a_Q^*(r)=B^*(r)-\Lambda(r_c).
\]
For fixed \(v\) and any fixed \(A>0\) we shall use the following three uniform sums, with \(L=\log P\), \(T\) between fixed positive powers of \(P\), \(m\le P^{O(1)}\):
\[
 \sum_{d\le T,(d,m)=1}\frac{\mu(d)\log d}{d}
 =-m/\phi(m)+O_A(L^{-A}),\quad
 \sum_{d\le T,(d,P)=1}\frac{\mu(d)\log d}{\phi(d)}
 =-\mathfrak S(P)+O_A(L^{-A}),\quad
 \sum_{d\le T,(d,P)=1}\frac{\mu(d)}{\phi(d)}=O_A(L^{-A}).        \tag{2}
\]
Here as usual constants may depend on the fixed power ranges. For the first formula use the convolution of \(\mu(d)/d\) with \(1_{k\mid m^\infty}/k\). The latter harmonic Euler product is \(m/\phi(m)\); its tilted absolute sum with tilt \(k^{1/\log L}\) is bounded by a power of \(L\), uniformly: split the primes dividing \(m\) at \(L^2\), using \(p^{1/\log L}\le e^2\) below that threshold and \(O(L)\) primes above. For the other two formulas convolve \(\mu(d)/d\) with the coefficients of the Euler product
\[
 H_P(w)=\prod_{l\mid P}(1-l^{-1-w})^{-1}
 \prod_{l\nmid P}\frac{1-l^{-w}/(l-1)}{1-l^{-1-w}} .
\]
The coefficients of the second product are absolutely summable even with fixed tilt \(1/4\): the absolute sum of its nonconstant local coefficients is \(O(l^{-2+1/4})\) with this tilt. The first product has the preceding polylog tilted bound. Thus coefficients of either convolution factor past \(k>\sqrt T\) can be lost with arbitrary-log saving, also with a fixed number of log weights. Apply the classical PNT/Mertens partial summation estimates \(\sum_{n\le Y}\mu(n)/n=O_H((\log Y)^{-H})\), \(\sum_{n\le Y}\mu(n)\log n/n=-1+O_H((\log Y)^{-H})\) on \(Y=T/k\ge\sqrt T\). This gives (2), since \(H_P(0)=\mathfrak S(P)\). It also proves the first formula without log with zero main.

CRT gives \(\sum_{n+r=P}B(n)B^*(r)=P\mathfrak S(P)+O_A(PL^{-A})\): fix the right divisor \(e\), \((e,P)=1\). The left divisor \(d\) must satisfy \((d,e)=1\); otherwise the common prime would divide \(P\). A compatible residue contributes \(P/(de)+O(1)\), so the total counting error is \(O(Q^2 L^2)\). Apply the first formula of (2) with \(m=e\) and the second with \(T=Q\). Also \(\sum\Lambda(n)B^*(r)=P\mathfrak S(P)+O_A(PL^{-A})\) by the maximal-residue Bombieri–Vinogradov theorem and (2). The ordinary sum \(\sum B(n)\Lambda(r)\) has that same value: discard true prime powers of a prime dividing \(P\) at cost \(P^{o(1)}\); for the rest all contributing \(d\mid P-r\) are coprime to \(P\).

For the required asymmetric sum \(\sum B(n)\Lambda(r_c)\), write \(r=g m\), \(g\mid P^\infty,(m,P)=1\). Terms \(g>P^\xi\), fixed \(0<\xi<\min(v/2,(1-2v)/2)\), cost \(P^{1-\xi/2+o(1)}\): use the divisor maximum and
\(\sum_{g>P^\xi,g\mid P^\infty}1/g\le P^{-\xi/2}\prod_{l\mid P}(1-l^{-1/2})^{-1}=P^{-\xi/2+o(1)}\).
For smaller \(g\), every squarefree divisor \(d\le Q\) of \(P-gm\) can be written \(d=h e\) with \(h\mid\operatorname{rad}(g),(e,P)=1\), since a prime dividing \(d,P\) must divide \(g\). Conversely the congruence after these choices imposes only \(m\equiv P g^{-1}\pmod e\) (and the already imposed unit condition on \(m\)); here the inverse is taken modulo \(e\). BV at scale \(P/g\) applies since \(e\le Q\) is below its square root by a fixed power margin, uniformly in \(g\) and the cut \(e\le Q/h\). Removing \((m,P)>1\) from its prime-power estimate costs \(O(L^2)\) per modulus and hence altogether \(O(P^{v+\xi+o(1)})\). The main for each \(g\) is
\[
 -\frac Pg\sum_{h\mid\operatorname{rad}(g)}\mu(h)
 \sum_{e\le Q/h,(e,P)=1}\frac{\mu(e)(\log h+\log e)}{\phi(e)}.
\]
It vanishes to the required accuracy unless \(g=1\), by (2) and \(\sum_{h\mid\operatorname{rad}(g)}\mu(h)=0\) for \(g>1\). The BV and (2) errors, with their log weights, sum with loss \(\sum_{g\mid P^\infty}\tau(g)/g=(P/\phi(P))^2\ll(\log L)^2\). Therefore the asymmetric sum also equals \(P\mathfrak S(P)+O_A(PL^{-A})\).

Finally \(\sum\Lambda(n)\Lambda(r_c)=G+O(P^{1/2+o(1)})\): for a prime input not dividing \(P\) the other input is coprime to \(P\); primes dividing \(P\) and genuine higher prime powers cost the displayed error. This proves \(R_Q=G-P\mathfrak S(P)+O_A(PL^{-A})\) at the changed cutoff directly. In each physical prime–composite row, apart from prime labels \(\le Q\), higher prime powers and prime divisors of the target (total \(O(P^{\max(v,1/2)+o(1)})\)), the composite coefficient equals \(B(r)=B^*(r)\), whereas \(B\) vanishes on large true primes. The two orientation sums equal \(-P\mathfrak S(P)+O_A(PL^{-A})\) by the just-proved prime BV estimate. Subtraction, or the short–short identity and the nonunit calculation, gives \(+P\mathfrak S(P)+O_A(PL^{-A})\) for both-composite. These unlocalized identities are standard short-divisor algebra of the kind underlying [Pan, as summarized by Huang–Li, (2)–(6)](https://arxiv.org/html/2005.03811v2#S1); no novelty for them is asserted.

## 2. Sifted model on genuine fixed residue classes

In the two-sided rough physical sum all nonunits can be discarded at power-saving cost: any common prime with \(P\) must exceed \(z\), so at most \(O(PL/z)\) inputs are exceptional and each weight is \(P^{o(1)}\). Thus the true asymmetric weight on the rough row can be treated as the symmetric one throughout. In the short–short calculation we may use the ordinary symmetric short divisors \(d,e\) coprime to \(P\), dropping physical nonunits as just justified. If one imposes only these divisor restrictions while counting, the reintroduced physical nonunits have the same negligible cost. Likewise both short-versus-prime orientations coincide up to negligible exceptions; their proper-power and prime-input-below-\(Q\) errors are as in §1.

Set \(D=P^{(1/2-v)/2}=z^s\). Use the upper and lower beta sieve weights of level \(D\), bounded by one and supported on squarefree products of primes \(\le z\). For local densities \(g(l)\) of dimension at most 1 or 2 below, the [fundamental lemma, e.g. Friedlander–Iwaniec, *Opera de Cribro*, Lemma 6.11; stated with the dimension condition in Kurlberg–Lester–Rosenzweig, Thm 2.2](https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/superscars-for-arithmetic-point-scatters-ii/3CCB969E058792C1803466AE0EF29136) gives
\(\sum_t\lambda_t^\pm g(t)=V(1+O(e^{-s}))\), \(V=\prod_{l\le z}(1-g(l))\), for large absolute \(s\). All constants are uniform: for \(3\le l\nmid P\) the worst densities are \(1/(l-1)\) and \(2/l\), at \(l\mid P\) the respective densities are \(0\) and \(1/l\). Since \(2\mid P\) there is no missing-residue obstruction at 2. The worst factors at primes at least 3 are majorized by the corresponding Mertens products of dimensions 1 and 2 times local factors 1+O(1/l²). The product over w≤l<z is therefore at most (log z/log w)^κ(1+O(1/log w)), as in the cited (2.5); the finitely many smallest primes have uniformly bounded local factors.

*Prime versus short.* For a fixed \(z\)-rough \(d\le Q,(d,P)=1\) in the composite short sum, count prime log weights \(p<P\), \(p\equiv P\pmod d\), subject to \(P-p\) being \(z\)-rough; prime inputs \(p\le z\) may be removed with negligible total cost. At \(l\le z,\ l\nmid P\) the one forbidden unit class is \(P\bmod l\); at \(l\mid P\) there is none among units. One may initially discard the prime labels dividing \(P\), which have negligible weighted cost. For squarefree sieve divisors \(t\) composed of the remaining primes the joint class is the single unit \(P\bmod dt\) with \((d,t)=1\); the main for sieving is \(P/\phi(d)\) with \(g(t)=1/\phi(t)\). Summing all sieve remainders against \(|\mu(d)\log d|\) costs \(O_A(PL^{-A})\) by BV on the weighted primes themselves: \(dt\le QD<P^{1/2-c_v}\), with unique rough-times-smooth factorization of the modulus. No modulus is being used beyond the level of distribution. Treating primes dividing \(P\) directly in the BV step costs at worst \(QD L^{O(1)}\). We can apply the positive-count sandwich **for each \(d\)** before inserting its signed coefficient.
   
*Short versus short.* For \(z\)-rough \(d,e\le Q,(de,P)=1\), compatibility requires \((d,e)=1\). On the class \(n\equiv0\bmod d,\ n\equiv P\bmod e\), sieve out \(l\mid n(P-n)\) for every \(l\le z\). This has density \(g(l)=2/l\) for \(l\nmid P\), and \(1/l\) for \(l\mid P\). For squarefree sieve divisor \(t\), the CRT progression count is \(Pg(t)/(de)+O(2^{\omega(t)})\). The **sum** of all remainders, bounded by \(Q^2 D L^{O(1)}\), is power-saving since \(2v+(1/2-v)/2<1\). Again sandwich each unsigned count before multiplying its coefficient of either sign.

Define \(V_0=\prod_{l\le z}(1-1/l)\); let \(V_1,V_2\) be the preceding respective sieve products. Direct local division gives, **uniformly in the true target**,
\[
 V_1=(1+o_\epsilon(1))\mathfrak S(P)V_0,\qquad
 V_2=(1+o_\epsilon(1))\mathfrak S(P)V_0^2,\qquad
 V_0\sim e^{-\gamma}/\log z .
\]
Indeed the ratios in both cases have local factor \((1-1/(l-1)^2)\) away from \(P\) and \((1-1/l)^{-1}\) on \(l\mid P\), including 2; the omitted latter factors above \(z\) cost \(O(L/z)\) in their logarithm.

## 3. Signed rough-divisor mean and absolute errors

Put \(H=\log z\) and
\[
 W=-\sum_{d\le Q,\ P^-(d)>z}\frac{\mu(d)\log d}{d}.
\]
Then, as \(P\to\infty\) at fixed \(u=v/\epsilon>1\),
\[
 W/H\longrightarrow B(u):=\int_0^{u-1}\rho(t)\,dt.               \tag{3}
\]
Indeed label the distinct prime factors of a squarefree \(d\) and divide by the factorial of their number \(j\le u\). Partial summation of primes shows product harmonic measures in the exponent coordinates \(x_i=\log l_i/H\) converge on boxes to \(\prod dx_i/x_i\) over \(x_i\ge1,\ \sum x_i\le u\); simplex ties and boundary planes have zero measure. Repeated labels in the independent product measures cost \(O_u(\sum_{l>z}1/l^2)=o_u(1)\). The weight \(\log d/H=\sum x_i\) lets us distinguish one coordinate which cancels its factor \(1/x_i\). The sum over the remaining \(j-1\) labels after that integral has alternating signs:
\[
 \rho(t)=\sum_{k=0}^{\lfloor t\rfloor}\frac{(-1)^k}{k!}
 \int_{y_i\ge1,\ \sum y_i\le t}\prod_{i=1}^k\frac{dy_i}{y_i}\quad(t\ge0),
\]
with empty term 1; integration of the distinguished variable from 1 to \(u\) gives (3). This really is Dickman's function: multiplying the derivative by \(t=\sum y_i\) on each moving face and distinguishing a coordinate yields \(t\rho'(t)=-\rho(t-1)\) for \(t>1\), with \(\rho=1\) on \([0,1]\). Extending by zero on \(t<0\) gives \(t\rho(t)=\int_{t-1}^t\rho(w)dw\) for \(t\ge1\); the first-zero argument proves positivity, the derivative then gives monotonicity, and iteration gives \(\rho(t)\le1/\lfloor t\rfloor!\). Its Laplace transform, obtained by summing the absolutely convergent integrated series at \(h>0\), is \(h^{-1}\exp(-\int_1^\infty e^{-hy}dy/y)\). The standard exponential integral at 0 gives limit \(e^\gamma\). In particular \(b(u)\uparrow1\).

The absolute harmonic mass of all squarefree rough divisors is at most \(\prod_{z<l\le Q}(1+1/l)\ll u\) by Mertens, with an absolute constant for fixed \(u\) and sufficiently large \(P\). Hence log-weighted absolute mass is \(O(u^2 H)\). For \(d\) rough squarefree the factor \(d/\phi(d)=1+O_u(1/z)\), and the absolute harmonic cost of removing \(d\) not coprime to \(P\) is \(O(u\sum_{l\mid P,l>z}1/l)=O(u L/z)\). For the double sum, dropping the constraint \((d,e)=1\) costs at most \(O(u^4 H^2\sum_{l>z}1/l^2)=o_u(H^2)\) by marking a common prime in both divisors. These estimates prove that the main coefficients in §2 are \(W+o_u(H)\) and \(W^2+o_u(H^2)\), **with their actual Möbius signs**.

The relative errors in the separate positive sieve counts of §2, summed with unsigned coefficients, are thus at most \(O(P V_1 u^2 H e^{-s})\) and \(O(P V_2 u^4 H^2 e^{-s})\). This is where roughness of the *divisors*, as well as of both physical inputs, is essential: a log-power loss depending on \(P\) could not be paid for by the fixed \(e^{-s}\). Combining with (3) and the exact product constants gives the two rough-row evaluations in the theorem. The two-sided rough prime-pair term is \(G+O(z L^2+Q L^2)\); subtract the rough total from the full signed rows in §1 to get (1).

**Limits.** The nonempty polynomial sieve window is bought by taking the short split strictly before the square root; merely sieving the original \(Q_0=\sqrt P/(\log P)^{20}\) in this proof would violate BV and the CRT error condition. The result estimates a genuine signed sum on the complement of the two-sided rough mask at every target; it does not make individual bad profiles small or yield a strict signed lower bound on the surviving prime-sensitive correlation. Positive density obstructions to negative-only budgeting at other parameters are not assertions of fixed-target positivity here.

For comparison, [Pham's October 2026 boundary-correlation preprint](https://www.preprints.org/manuscript/202610.3061) estimates unsigned rough pairs and fixed reflected prime–rough comparisons in its own ranges. [Bahbouhi's November K-correction note](https://www.preprints.org/manuscript/202611.0975) has exact one-prime/rough-complement identities above the cube-root cutoff. This calculation is instead a signed estimate for the omitted part of both physical inputs of Pan’s two-sided remainder, with both short-divisor weights retained. No conclusion about its surviving sign or priority over all rough-sieve methods is claimed.
