# Full signed cancellation on an actual unbalanced semiprime-shift block

Consider the true prime relation \(p+s q=N\), with \(s,q\) genuine primes and \(\log_xs\in[.10,.14]\), \(x=N/2\). Expand the reflected \(\Lambda(p)\) by Vaughan. This note proves a fixed-target **arbitrary-log saving for one actual selected part of its \(\mu_{\le U}*\log\) term**, in which the Möbius divisor has one specified real prime factor. It is not a carrier of composite \(n\) with additional imposed labels (other than the genuine semiprime \(n=sq\)): the extra label is in the prime-detection expansion of the **reflected side**. No estimate is claimed for the whole shifted-prime count or the remaining Vaughan terms.

## 1. Original block and Cauchy normalization

Put \(L=\log x\), \(I=(x/2,x]\), \(J=N-I\). In the block
\[
   s_{\rm lab}\sim S\ {\rm prime},\quad q_{\rm lab}\sim x/S\ {\rm prime},
   \quad p=d h=N-s_{\rm lab}q_{\rm lab}\in J,\quad
   \log_xd\in[.459,.461],
\]
the intervals are actual integer ranges, chopped into dyads as needed. Thus \(h\) lies at exponent \([.539,.541]+o(1)\). Impose that the Möbius divisor \(d\) has exactly one distinct prime factor \(c\) in
\[
                          x^{.159}\le c\le x^{.161}.
\tag{1}
\]
The \(\mu(d)\) in the numerator automatically removes repeated \(c^2\). This is a genuine positive fixed log-width subfamily of \(d\), not a proxy for \(\mu(d)\). For example its proportion among \(d\) in a full dyadic interval is bounded below: the mark reciprocal sum tends to \(\log(.161/.159)>0\), and subtracting multiples of two such primes or their squares costs at most the square of this small reciprocal sum times the interval scale plus \(O(x^{.322+o(1)})\), which is \(o(D)\).

Use any bounded fixed log-power label weights \(\kappa_{s_{\rm lab}}\), any log-bounded quotient weight \(\eta(q_{\rm lab})\) supported on \(q_{\rm lab}\ll x/S\), and any smooth \(\Psi(dh/x)\) supported inside \(J\) with fixed log-power derivatives after normalization. In particular \(\eta\) may be the actual prime indicator (or prime-log weight). The exact \(K_{P_3}(s_{\rm lab}q_{\rm lab})\) on the semiprime cell can also be retained: it is \((1-t)(1-2t)^2\) with \(t=\log(s_{\rm lab})/\log(s_{\rm lab}q_{\rm lab})\). Split its finite polynomial into powers of \(\log s_{\rm lab}/L\) in \(\kappa\) times the corresponding smooth reciprocal powers of \(\log(s_{\rm lab}q_{\rm lab})/L=\log((N-dh))/L\) in the normalized product weight. The sharp \(J\) endpoints can be imposed by log-width smooth approximation below.

The result for each box is
\[
 T_N=\sum_{N-dh=s_{\rm lab}q_{\rm lab}}
      \kappa_{s_{\rm lab}}\eta(q_{\rm lab})\mu(d)\log h\,
      \Psi(dh/x)\,1_{\{d\ {\rm marked\ by}\ (1)\}}
                     \ll_B xL^{-B}
\tag{2}
\]
for every \(B\), uniformly in each fixed even \(N\). Here \(D H\asymp x\) for the dyadic \(d,h\)-scales. One can also keep an independent smooth normalized cutoff on \(h\) in its dyad. This is literally part of Vaughan \(\mu_{\le U}*\log\), e.g. \(U=x^{.462}\). The ordinary BV bound for \(q_{\rm lab}\) in \(q_{\rm lab}\equiv N\bar s_{\rm lab}\pmod d\) would need \(d\le x^{(1-\log_x s_{\rm lab})/2-o(1)}\le x^{.450+o(1)}\). Our exponent is \(>.459\), so the block is not discarded by that use of ordinary BV. Other exact identities or larger distribution inputs are not ruled out.

In the prime/prime application, first discard \((s_{\rm lab}q_{\rm lab},N)>1\): there are \(O(1)\) prime divisors of \(N\) in either factor band, and fixing one of them costs \(O(x^{o(1)}(x/S+S))\), using the divisor bound on the number of \(d,h\) representations and \(\log h\ll L\). For the general log-bounded \(\eta\) in (2), assume it is supported on \((q_{\rm lab},N)=1\) (as in the application after this disposal). Thus all resulting row products \(m=N-s_{\rm lab}q_{\rm lab}\) are units modulo \(N\).

In a dyad \(s_{\rm lab}\sim S\), Cauchy in the actual quotient gives
\[
                      |T_N|^2\ll (x/S)L^C\,\mathcal Q_N,
 \qquad
 \mathcal Q_N=\sum_{u>0}\left|
          \sum_{\substack{N-dh=A u\\ A\sim S\ {\rm prime}\\(dh,N)=1}}
           \kappa_A\mu(d)\log h\,\Psi(dh/x)\,1_{d\ {\rm marked}}
                           \right|^2 .
\tag{3}
\]
The positive \(\mathcal Q_N\) has **all** integer quotients \(u\) in its bounds; this is an enlargement only after using the original actual quotient weight in Cauchy. An \(xS L^{-B}\) bound for it for all \(B\) proves (2). No cancellation of \(\eta\) is assumed.

We can smooth sharp product and free-coordinate endpoints at width \(L^{-F}\) in their normalized variables. Each edge sequence has absolute coefficient \(O(L^C\tau_2(m))\) and support size \(O(xL^{-F}+x^{.461+o(1)})\), by counting the possible pairs \(d,h\) in the edge. Its squared mass is \(O(xL^{-F/2+C'})\) by Cauchy and the elementary fourth divisor moment (or the analogous stronger power at very short edges). For any such sequence \(c(m)\), using the fact a positive \(N-m\ll x\) has only \(O(1)\) prime divisors in \(A\sim S\),
\[
      \sum_u\left(\sum_{A\sim S,\ A\ {\rm prime}} |c(N-Au)|\right)^2
                        \ll S\sum_m |c(m)|^2 .
\]
The same inequality for the full coefficient and Cauchy bound the change in \(\mathcal Q_N\) with any prescribed log reserve. Choose \(F\) sufficiently large. The divisor, marker and primality restrictions are left sharp.

## 2. Exact determinant and elementary tails

In a pair of dyadic boxes after opening (3), let
\[
    m_1=d h=N-Au,\quad m_2=r h'=N-Bu,\quad
    j=B-A,\quad D H,\ R H'\asymp x .
\]
Both \(A,B\) are actual primes in the **same** \(S\) dyad, with \(.10\le\log_x A,\log_xB\le.14\); \(d,r\) are in the same stated exponent band and marked as in (1). Diagonal \(A=B\) costs only \(O(x^{1+o(1)})\): for \(A,u\) there are \(O(S)\cdot O(x/S)\) pairs, and the squared factorization coefficients are \(x^{o(1)}\) pointwise. This is power small relative to \(xS\). On \(A\ne B\), the exact determinant is
\[
 B d h-A r h'=Nj,\qquad
 (m_1,m_2)=(j,m_1)=(j,m_2),\quad
 g=(B d,A r)=(d,r)\mid j .
\tag{4}
\]
Indeed a prime factor of a common divisor of the two \(m_i\)'s cannot divide \(u\), since \(m_i\) is a unit modulo \(N\). Conversely \(m_1\equiv m_2\bmod j\). The cross gcd is just \((d,r)\) because \(A\nmid d\), \(B\nmid r\): \(A\nmid m_1\) and \(B\nmid m_2\) follow from the unit relation \(m_i=N-A_i u\). In particular \(g\) is coprime to \(A B N\). Conversely (4)'s determinant forces the two congruences mod \(A,B\) and equality of their quotients; their positivity follows from \(m_i<N\).

Here is a uniform reduced-progression second moment sufficient for the discarded physical gcd tail. If \(A_i\) is prime, \(A_i<x_0^{1/4}\) with a fixed exponent reserve, and the residue is a unit, then
\[
 \sum_{\substack{m\asymp x_0\\m\equiv a\bmod A_i}}\tau_2(m)^2
                        \ll (x_0/A_i)(\log x)^C .
\]
Use \(\tau_2^2\le\tau_4\), choose the largest of four factors, and sum the other product \(v_0\ll x_0^{3/4}\) with multiplicity \(\tau_3(v_0)\). The last factor in its progression has \(O(x_0/(A_i v_0)+1)\) choices and the endpoint is absorbed by the exponent reserve. If \(v\mid (m_1,m_2)\), \(v\mid j\), and \(u\equiv N\bar A\bmod v\), so \(m_i/v\) runs in a reduced class modulo \(A_i=A,B\) at scale \(x_0\asymp x/v\). In this application \(v\ll S\le x^{.14}\), so \(A_i\le x^{.14}<x_0^{1/4}\) with fixed slack. Cauchy over \(u\) gives the absolute cost per \(A,B,v\) at most \(x/(vS)\,\tau_2(v)^2L^C\). At most \(O(S(S/v+1))\) ordered integer pairs \(A,B\) satisfy \(v\mid B-A\), hence the total for \(v>L^K\) is
\[
   O\!\left(xL^C\sum_{v>L^K}^{O(S)}\tau_2(v)^2(S/v^2+1/v)\right)
                            \ll_B xS L^{-B}
\]
at sufficiently large fixed \(K\). In particular we may impose \((j,r)\le L^K\) and \(g\le L^K\), without imposing an extra cut \((j,d)\le L^K\) in the inner signed variable.

Write \(d=g d_1,\ r=g r_1,\ q=A r_1,\ C=Nj/g\). The determinant is \(B d_1 h-q h'=C\), with \((d_1,q)=1,\ (B,q)=1\). Include outside restrictions \((g,ABN)=1,\ (d_1r_1,N)=1\); if \(\mu(g)=0\) the signed term vanishes, and \(\mu(d),\mu(r)\) retain the remaining squarefree tests. Given these restrictions, the only unit test left is \((h,N)=1\), equivalently \((h',N)=1\). Expand it by \(f\mid(h,N)\), coefficient \(\mu(f)\); then automatically \(f\mid h'\), and \(C/f\) is an integer. We may truncate \(f\le\exp(L^\beta)\), fixed \(0<\beta<1\), with arbitrary log-power error in the physical equality. For \(f\le x^{.4}\), all \(m_i\) are multiples of \(f\) and hence \(f\mid u\), with each \(m_i/f\) a reduced progression modulo \(A_i\) at scale \(x/f\): now \((x/f)^{1/4}\ge x^{.15}>A_i\). The same second moment bounds the absolute cost by \(x/(fS)\tau_2(f)^2 L^C\) per pair. Sum \(\sum_{f\mid N,f>\exp(L^\beta)}\mu(f)^2\tau_2(f)^2/f\ll_B L^{-B}\) by harmonic Rankin (choose a fixed \(\eta<\beta\) and bound the Euler product by \(\exp(O_\eta(L^\eta))\)). For \(f>x^{.4}\) there are at most \(O(x/(S f))\) positive \(u\ll x/S\) divisible by \(f\), **without** an additive 1; the pointwise divisor bound and \(\tau(N)=x^{o(1)}\) finish the discard. This counts all factorizations once, so no extra multiplier for the choices of \(g\) is incurred. These tails were estimated at the genuine physical equality, not in a Fourier surrogate.

## 3. Poisson: the true zero term and all nonzero terms

Since \(c\) in (1) exceeds \(g\), write \(d_1=c n\), with \(n\) devoid of primes in the whole marking band. Here \(n\) has exponent in \([.298,.302]+o(1)\). The smooth \(h\)-weight includes \(\log h\), both original product and free windows, and the actual dependence of the second free coordinate:
\[
 \frac{h'}{H'}=\lambda \frac hH-\gamma,\qquad
 \lambda=\frac{B d_1 H}{qH'},\quad \gamma=\frac C{qH'},
 \qquad \lambda\asymp1,\quad |\gamma|\ll1 .
\]
As in [FarAnglePoissonDescent.md](FarAnglePoissonDescent.md), the exact progression Poisson sum has summand
\[
   \frac{H}{f q}\ \widehat W_{\rm ph}\!\left(\frac{\ell H}{f q}\right)
       e_q\!\left(\ell(C/f)\overline{B c n}\right).
\tag{5}
\]
The test \(W_{\rm ph}\) is the actual compactly supported smooth normalized product above, with log-power derivatives uniformly in the normalized \(n\)-coordinate; it is unrelated to the earlier flexible carrier.

At zero frequency, fix the actual \(A,B,r_1,g,f,c\). On coprime \(n\) the signed first divisor coefficient is \(-\mu(g)\mu(n)\), with \(n\) also avoiding the marker band. Uniform maximal coprime Mertens for \(\mu(n)\), with coprimality to \(E\le x^{O(1)}\) (here \(g q N\)), gives any log reserve on its \(x^{.30+o(1)}\) scale. To impose marker avoidance, note \(n<x^{.302+o(1)}<x^{.318}\), so it has at most one such prime divisor \(c'\). Subtract the terms \(n=c'v\); the lengths \(v\) are at exponent \([.137,.143]+o(1)\), \(\mu(n)=-\mu(v)\) holds when \(c'\) is admissible, and \((c',E)>1\) is excluded. Apply the same uniform Mertens there and sum \(\sum_{c'}1/c'\ll1\). The coprime Mertens bound follows, for instance, from ordinary Mertens convolved with the indicator of integers supported on primes dividing \(E\): split the harmonic convolution at the square root of the active variable's length, using trivial counts and a Rankin tail for the larger part, as in (6) of the previous Poisson note. Partial summation with \(\widehat W_{\rm ph}(0)\) costs log powers. The aggregation of the true zero term is \(O_B(xS L^{-B})\) by \(N\)-scale \(D H\asymp x\), both \(A,B\) counts, and harmonic sums in \(r_1,f,g\).

For nonzero frequency put \(s_0=(C/f,q)\le L^K\) (the retained \((j,r)\) cut), \(q_*=q/s_0\). The modulus \(q_*\) has exponent in \([.559,.601]+o(1)\). Since \(q\) is coprime to \(N\), \(s_0\mid j/g\), and the phase in (5) is exactly
\[
               e_{q_*}\left(\frac{N}{f}\,
                      \frac{\ell(B-A)}{g s_0}\,\overline{B c n}\right).
\tag{6}
\]
The true natural frequency length satisfies \(f q/H\le x^{.062+o(1)}\). All \(|\ell|>x^{.064}\) are power-small to any order by rapid decay of the smooth Fourier transform and the fixed exponent reserve .002. It therefore suffices to use the signed dyads of \(\ell\) through \(x^{.064}\).

Fix \(g,f,s_0\), and a modulus dyad \(q_*\asymp Q_*\). Each \(q_*\) has \(O(1)\) actual outer representations \(s_0q_*=A r_1\) with \(A\) prime in the stated band: choose \(A\) among its product's prime divisors of exponent at least .10; \(r_1\) is then determined. Fix one representation. **Do not fix \(B\).** Take the signed integer fractions
\[
                              \frac{\ell(B-A)}{g s_0 B c}.
\tag{7}
\]
Writing the numerator as \(\ell(B-A)/(g s_0)\) affords denominator \(Bc\), and it is already reduced: \(B\nmid B-A\), \(c>|B-A|\), and \(|\ell|<\min(B,c)\), with \(B,c\) distinct primes in disjoint bands. The actual \((B c,q)=1\) is retained. Two such fractions representing the same residue mod \(q_*\) have the same signed rational value, since their cross-products have magnitudes \(\ll x^{.064+.140+.140+.161+o(1)}=x^{.505+o(1)}<q_*/2\). Then the exact denominator \(Bc\) determines both \(B,c\), and the numerator determines \(\ell\). This is a genuine injectivity for the **outer-varying actual primes** \(B\), not a full rectangular bound that would lose its short label. Conditions \(g\mid B-A\), \(s_0=(C/f,q)\), and \((B,q)=1\) can all be tested on that joint \(B\)-side, independently of \(n\) for fixed outer labels; \(q=A r_1\) does not involve \(B\). Any further coprimality for \(n\) is in its own fixed-modulus coefficients.

In one dyad for \(c,n,\ell\), write \(C_0,Z_0,T\) for their magnitudes. The smooth test in (5) is separated only in \(n/Z_0\) versus the joint \((B,c,\ell)\) labels, by Mellin inversion with log-power \(L^1\) cost. The normalized \(n\)-derivatives act on its smooth \(W_{\rm ph}\) with all other labels fixed; the separable Fourier coefficients have uniform log-power decay under repeated integration by parts. The original sharp \(g c n\) dyadic/exponent interval may be inserted by truncated Perron between half-integer endpoints (as in [FarAngleLowReciprocalPrimeSlice.md](FarAngleLowReciprocalPrimeSlice.md)); its mixed \(c,n\) dependence is multiplicatively separated with log cost and arbitrary power-small errors. A similar sharp \(r\) restriction is already outer. Restricting \(c\) and \(n\) to individual subdyads costs only log factors. Thus the resulting coefficient on the range of (7) can be arbitrary log-bounded and depends on all the actual outer and joint labels, but is separated from the \(n\)-coefficient.

Let \(U(t)\) collect this joint coefficient at the distinct residues of (7). Then \(\|U\|_{4/3}\ll(S C_0 T)^{3/4}L^C\) by injectivity. Orthogonality and [Shparlinski, arXiv:1710.02777, Lemma 2.5](https://arxiv.org/pdf/1710.02777) give the average fourth moment for the \(n\)-inverse sum with the unit \(N/f\), as in the weighted derivation of the earlier reciprocal slice. Its \(L^4\)-norm averaged over actual \(q_*\)-representations (bounded multiplicity) is at most
\[
                  (Z_0+Q_*^{1/4}Z_0^{1/2})x^{o(1)} .
\]
The formula applies to coefficient functions of \(n\) depending on the particular outer representation, using the positive collision majorant. There is no prime-result hypothesis on the modulus distribution; the average is over integers and its multiplicity is bounded. Also \(2Z_0<Q_*\) on the whole box.

Here the target size before the Poisson prefactor per modulus is \(S C_0 Z_0\). Since \(S C_0\ge x^{.259+o(1)}\), \(T\le x^{.064}\), and \(Q_*^{1/4}Z_0^{-1/2}\le x^{.00125+o(1)}\), the complete nonzero-frequency normalized saving is at least
\[
                .259/4-3(.064)/4-.00125=.0155
\]
in exponent before subpower factors. Multiply by \(H/(f s_0 Q_*)\) and sum the outer moduli: the cost is at most \(H S C_0 Z_0 x^{-c_1}/(f s_0)\) for some fixed \(c_1>0\) (e.g. .01 asymptotically). Because \(C_0 Z_0\asymp D/g\) and \(DH\asymp x\), this is \(O(xS x^{-c_1}/(f s_0 g))\). Summing reciprocal weights in \(f,s_0,g\), and the fixed log-power many dyadic splits, leaves a power saving in \(xS\). **There is no additional \(B\)-sum** after this computation: it was already the short prime slot of (7) and paid only in \(S C_0\). This estimates the whole natural reciprocal frequency range for the selected actual block, not merely its low frequencies.

Combining the absolute tails, diagonal, zero mode, and the nonzero estimates proves \(\mathcal Q_N\ll_B xS L^{-B}\) and hence (2). Summing the log-power number of \(s,d,h,c,n\) box splits keeps arbitrary log reserve.

## 4. What is still required

The result handles real semiprime labels \(s_{\rm lab}\) anywhere in \([x^{.10},x^{.14}]\) and the **actual** prime \(q_{\rm lab}\) paired with the specified reflected Vaughan component. It does not bound either all of \(\mu_{\le U}*\log\), its complementary divisor structures, or the other Vaughan terms in the original \(\Lambda(N-s_{\rm lab}q_{\rm lab})\). The shifted prime's composite-expansion pieces are signed and cannot be ignored by counting the just-proved block. Thus no unconditional upper of the required sign for the whole unmarked semiprime cell, and no binary Goldbach positivity, follows from this block.

Related primary work includes [Yang, arXiv:2611.01522v2](https://arxiv.org/abs/2611.01522v2) on smooth numbers in simultaneous progressions and [Wright, arXiv:2608.27732v1](https://arxiv.org/abs/2608.27732v1) on trilinear Kloosterman fractions and averaged congruences. Neither is used as an estimate for this selected signed fixed-target prime-shift block. The input used here is the explicitly cited average inverse collision lemma.
