# Both reflected Vaughan Type I terms on an actual unbalanced semiprime cell

Let \(N=2x\) be even, \(I=(x/2,x]\), \(L=\log x\); take a dyad \(S<s\le 2S\), where \(s\) is prime, \(S=x^\alpha\), and \(.10\le\alpha\le.14\). A fixed factor of slack at the endpoints is harmless (\(\alpha\) may differ by \(O(L^{-1})\)). The second label \(q\) is also a genuine prime, with \(sq\in I\); the reflected argument is \(m=N-sq\). Write \(\mathfrak S(E)\) for the ordinary Goldbach singular series at even \(E\). This proves the two exact Type I terms of the reflected Vaughan expansion over this actual semiprime family for each individual \(N\), with a dyad-dependent cutoff. It neither proves \(\Lambda(m)>0\) nor bounds the remaining bilinear term.

## 1. Results

Fix \(0<\Delta<.01\), and set
\[
       b_0=\tfrac12-.51\alpha,\qquad b_1=\tfrac12-\alpha/4-\Delta.
\tag{1}
\]
Take \(x^{.40}\le U\le x^{b_1}\); for the second identity also take \(1\le V\le x^{.03}\), \(UV\le x^{b_1}\). Let \(|\kappa_s|\ll L^C\), and \(W_s(v)\) be a finite sum of powers of \(\log s/L\) times smooth functions of \(sv/x\) with uniformly log-power derivatives; dependence on \(L\) in the latter is allowed. The exact \(K_{P_3}(sq)=(1-t)(1-2t)^2\), \(t=\log s/\log(sq)\), qualifies. The central interval is allowed to be sharp, as are all divisor bounds. Define
\[
\begin{aligned}
T_1(U)&=\sum_{\substack{s,q\ \mathrm{prime}\\s\sim S,\ sq\in I}}
 \kappa_s W_s(q) \sum_{\substack{d\mid m\\d\le U}}\mu(d)\log(m/d),\\
T_2(U,V)&=\sum_{\substack{s,q\ \mathrm{prime}\\s\sim S,\ sq\in I}}
 \kappa_s W_s(q) \sum_{\substack{d\ell\mid m\\d\le U,\ \ell\le V}}\mu(d)\Lambda(\ell).
\end{aligned}
\]
Then for every fixed \(B>0\),
\[
\begin{aligned}
T_1(U)&=\sum_{\substack{s\sim S,\ s\ \mathrm{prime}\\(s,N)=1}}
  \kappa_s\mathfrak S(Ns)\int_{I/s}W_s(v)\frac{dv}{\log v}
      +O_{\Delta,B}(xL^{-B}),\\
T_2(U,V)&=O_{\Delta,B}(xL^{-B}).
\end{aligned}
\tag{2}
\]
Constants may also depend on the fixed weight family. The continuous improvement above the exponent \((1-\alpha)/2\) from ordinary quotient-prime Bombieri–Vinogradov is \(\alpha/4-\Delta>0\). Across the whole \(s\)-band \(b_1\ge.465-\Delta\), and at \(\alpha=.10\) one has \(b_1=.475-\Delta\).

Since \(m\in[x,3x/2)\), the literal Vaughan identity is
\[
 \Lambda(m)=(\mu_{\le U}*\log)(m)
 -(\mu_{\le U}*\Lambda_{\le V}*1)(m)
 +(\mu_{>U}*\Lambda_{>V}*1)(m).
\tag{3}
\]
Here its fourth usual piece \(\Lambda_{\le V}(m)\) is zero. For instance fix tiny \(\upsilon>0\) with \(\upsilon+\Delta<1/40\), and use \(V=x^\upsilon,\ U=x^{b_1-\upsilon}\); both coprime Type I evaluations extend past the BV boundary. The **complete last term of (3), with its actual signs, remains**. In particular the positive main of (2) does not imply a prime count.

With \(W_s=K_{P_3}\), \(\kappa_s=1\), and the complete band \(x^{.10}<s<x^{.14}\), summing dyads in (2) and applying the prime number theorem gives
\[
 \left(\log(7/5)-.160+.0192+o(1)\right)
       \frac{\mathfrak S(N)x}{2\log x}
\tag{4}
\]
for the Type I main. Indeed for \(s\nmid N\), \(\mathfrak S(Ns)/\mathfrak S(N)=(s-1)/(s-2)\); in the long-prime integral the factor \(1-\log_xs\) cancels the same factor in \(\log v\) asymptotically, and \(\sum_s1/s\) supplies \(da/a\), \(a=\log_xs\). The limit in (4) is \(\int_{.10}^{.14}(1-2a)^2\,da/a\).

## 2. Signed cancellation on all moduli above the BV join

It suffices to prove \(O_B(xL^{-B})\) in each dyad of \(d\) intersecting \(x^{b_0}<d\le x^{b_1}\), for the original sums in (2). Put \(m=dh\) and use the respective divisor coefficients
\[
 c(d)=\mu(d)1_{d\le U},\qquad
 c(d)=\sum_{\substack{\ell\mid d\\\ell\le V,\ d/\ell\le U}}
                          \Lambda(\ell)\mu(d/\ell)
\tag{5}
\]
with free-factor weight \(\log h\) or \(1\). In both cases \(|c(d)|\le L\) up to an absolute constant, using \(\sum_{\ell\mid d}\Lambda(\ell)=\log d\). Remove the \(O(1)\) possible primes \(s\mid N\) or \(q\mid N\) per band at total cost \(O((x/S+S)x^{o(1)})\), by the pointwise divisor bound. The alternative \(s=q\) is not on the support, since \(s^2\ll x^{.28}\). Thus \(m\) is a unit mod \(N\). Cauchy in \(q\) removes its actual prime indicator at squared cost \(O((x/S)L^C)\) and leaves
\(\mathcal Q=\sum_u|\sum_{N-dh=Au}\kappa_Ac(d)\cdot\text{(test)}|^2\),
with all quotients \(u>0\) on the retained unit support. It is enough to bound \(\mathcal Q\ll_B xS L^{-B}\). The argument in this section in fact allows any log-bounded quotient weight supported on units.

The physical tails and zero-mode cancellation use the determinant from [the marked divisor argument](UnmarkedSemiprimeSignedBlock.md), but **there is no condition on the factorization of \(d\)**. The decisive sharper bound below uses that each fixed reciprocal frequency lives in one coset modulo the row prime \(A\), with an orthogonality bound of length \(Q/A\), not \(Q\). No inverse-energy estimate is needed.

**Exact same-divisor dyad and sharp boundaries.** Split the *original linear sum* by its \(d\)-dyads before Cauchy; logarithmic triangle inequality recovers the full sum. In each individual quadratic estimate both \(d\) and \(r\) are therefore in the **same** dyad \(D<d,r\le2D\), possibly with further sharp interval endpoints. In particular \(H=x/D\) is a common free-variable scale, and \(h/H,h'/H\in[1/2,3/2]\) on the original support. Take a fixed broad smooth free cutoff identically one on this interval, and smooth only the central product endpoints at relative width \(L^{-F}\). The product edge sequence is bounded by \(L^C\tau_2(m)\) on \(O(xL^{-F}+1)\) integers, so its squared mass is \(O(xL^{-F/2+C'})\) by the fourth divisor moment. A test \(z(m)\) with this bound costs at most \(O(S\sum_m|z(m)|^2)\) in the quadratic form, by Cauchy across labels and the fact each \(0<N-m\ll x\) has \(O(1)\) prime divisors in the label band. This proves arbitrary log precision for smoothing; all divisor bounds stay sharp. The diagonal \(A=B\) costs \(O(x^{1+o(1)})\).

Off diagonal put \(m_1=dh=N-Au\), \(m_2=rh'=N-Bu\), \(j=B-A\), with \(A,B\) distinct genuine primes in the same \(S\) dyad. We have
\[
 Bdh-Arh'=Nj,\quad (m_1,m_2)=(j,m_1)=(j,m_2),\quad
 g=(Bd,Ar)=(d,r)\mid j .
\tag{6}
\]
The unit relation implies \((m_i,u)=1\), giving the middle equality, and gives \(A\nmid d,\ B\nmid r,\ (g,NAB)=1\). Conversely the determinant on this support gives the two reduced congruences and equality of the positive quotients. A reduced progression mod \(A\) at scale \(X_0\), \(A\le X_0^{1/4-c_0}\) with fixed \(c_0>0\), has second divisor moment \(\ll(X_0/A)L^C\). Indeed \(\tau_2^2\le\tau_4\); separate the largest of four factors, and for each of the other products \(v_0\ll X_0^{3/4}\) count that largest factor in \(O(X_0/(A v_0)+1)\) choices. The other product is a unit and the fixed slack absorbs the additive term. If \(v\mid(m_1,m_2)\), then \(v\mid j\), \(v\ll S\); the \(m_i/v\)'s lie in reduced progressions mod \(A,B\) at scale \(x/v\). By Cauchy in \(u\) the absolute cost is \(O(x\tau_2(v)^2 L^C/(vS))\) per \(A,B,v\). At most \(O(S(S/v+1))\) ordered label pairs satisfy \(v\mid j\), so
\[
 O\left(x L^C\sum_{L^K<v\ll S}\tau_2(v)^2(S/v^2+1/v)\right)
       \ll_B xS L^{-B}
\]
for large fixed \(K\). We retain \(g,(j,r)\le L^K\), but need no extra cutoff on \((j,d)\).

Put \(d=g n,\ r=g r_1,\ q_0=A r_1,\ C_0=Nj/g\). Then \(Bnh-q_0h'=C_0,\ (Bn,q_0)=1,\ (nr_1g,N)=1,\ (g,AB)=1\). Include \((h,N)=1\) by \(\sum_{f\mid(h,N)}\mu(f)\); \(f\mid h'\) is automatic. Truncate \(f\le\exp(L^{3/4})\) with arbitrary log error. For \(f\le x^{.4}\) the same reduced-progression moment at scale \(x/f\) applies (\((x/f)^{1/4}\ge x^{.15}>A,B\) with fixed slack), with cost \(O(x\tau_2(f)^2 L^C/(fS))\) per \(A,B\). Harmonic Rankin bounds the large-divisor tail: with exponent \(1/4\) its Euler product over primes dividing \(N\) is \(\exp(O(L^{1/2}))\) by splitting primes at \(L^2\). For \(f>x^{.4}\), \(f\mid u\) and \(u>0\) give \(O(x/(Sf))\) possible quotients, without an additive 1. The pointwise divisor bound and \(\tau(N)=x^{o(1)}\) dispose of these terms. The bounds precede Poisson and sum over factorizations rather than charging each possible \(g\) again.

**Zero mode.** The progression for \(h/f\) is Poisson with summand
\[
   \frac{H}{f q_0}\widehat W_{\rm ph}(\ell H/(f q_0))
                    e_{q_0}(\ell(C_0/f)\overline{Bn}).
\tag{7}
\]
The true smooth test \(W_{\rm ph}\) substitutes
\(h'/H=(Bn/q_0)(h/H)-C_0/(q_0H)\)
in the second free and product weights. The prefactor in this substitution is \(\asymp1\), and the offset is bounded. The normalized \(n\)-derivatives and \(h/H\)-derivatives therefore cost only fixed powers of \(L\), after smoothing above.

We use uniform maximal coprime Mertens, for each fixed \(c,C_1,M>0\),
\[
  \sup_{0\le t\le X}
   \left|\sum_{\substack{j\le t\\(j,E)=1}}\mu(j)\right|
       \ll_{c,C_1,M} XL^{-M}\qquad (X\ge x^c,\ E\le x^{C_1}).
\tag{8}
\]
Indeed \(\mu(j)1_{(j,E)=1}\) is the convolution of \(\mu\) with the indicator of integers supported on primes dividing \(E\). Below \(\sqrt X\) in the latter variable use ordinary maximal Mertens and \(\prod_{p\mid E}(1-1/p)^{-1}=L^{O(1)}\). Above \(\sqrt X\) use harmonic Rankin, with the same prime split and exponent \(1/4\) as above. This proves the arbitrary reserve uniformly. Ordinary Mertens here is the classical consequence of the zeta zero-free region.

At \(\ell=0\), fix each \(A,B,r_1,g,f\). In the first case of (5), \(\mu(g n)=\mu(g)\mu(n)1_{(g,n)=1}\), and (8) applies at \(D/g\) with \(E=gNq_0\). In the second case, fix a prime power \(\ell_0\le V\); let \(t=(g,\ell_0)\), \(n=(\ell_0/t)v\), \(g_0=g/t\). Then \(g n/\ell_0=g_0v\), the sharp cutoff is an ordinary prefix, and any surviving \(\mu(g_0v)\) equals \(\mu(g_0)\mu(v)1_{(g_0,v)=1}\), with further unit conditions on \(v\) at \(Nq_0\). If \(\ell_0/t\) is nonunit mod \(Nq_0\) the term is zero. The length of \(v\) is \(\asymp Dt/(g\ell_0)\ge x^{.398+o(1)}\), usable in (8). The total coefficient loss relative to the length \(D/g\) is at most
\(\sum_{\ell_0\le V}\Lambda(\ell_0)(\ell_0,g)/\ell_0\ll g L\),
a fixed log power; no Möbius factorization of the *new coefficient* is presumed. Partial summation with the actual \(\widehat W_{\rm ph}(0)\) costs log powers. The prefactor in (7) times the \(n\)-scale is \(O(x/(f A r_1g))\). Sum over both labels (one \(1/A\) saving), \(r_1\) (harmonic), and \(g,f\) to get \(O_B(xS L^{-B})\) from the genuine zero mode.

**Full nonzero modes.** Set \(s_0=(C_0/f,q_0)\le L^K\), \(Q=q_0/s_0\). Since \((N,q_0)=1\), \(s_0\mid j/g\), so the phase in (7) is exactly
\[
 e_Q\left((N/f)\frac{\ell(B-A)}{g s_0}\overline B\,\overline n\right).
\tag{9}
\]
Here \(N/f\) is a unit mod \(Q\). Since \(d,r\le x^{b_1}\) and the shorter \(h\)-scale is \(H=x/D\), the true dual scale satisfies
\[
 fq_0/H \le x^{\alpha+2b_1-1+o(1)}
              =x^{\alpha/2-2\Delta+o(1)} .
\]
Thus retain \(0<|\ell|\le x^{\alpha/2-\Delta}\), with arbitrary power reserves in the remaining terms by integration by parts in (7); the polynomially bounded counts of the untransformed variables do not spoil an arbitrarily high fixed-order reserve.

Fix \(g,f,s_0,A,r_1\) and a single signed nonzero \(\ell\), and **vary the genuine prime \(B\)**. Since \(g s_0\) divides \(j=B-A\), the signed rational
\[
                  t_B=\frac{\ell(B-A)}{g s_0 B}\pmod Q
\tag{10}
\]
is reduced with denominator \(B\), since \(B\nmid B-A\) and \(0<|\ell|<B\); the denominator is a unit mod \(Q\). Cross-products have size \(O(x^{5\alpha/2-\Delta+o(1)})\le x^{.351}\), whereas \(Q\ge x^{.549+o(1)}\). Thus the \(t_B\)'s are distinct mod \(Q\). Crucially both \(g,s_0\) are units mod \(A\) since \(A\nmid j\), so \(A\mid Q\) and
\[
              t_B\equiv \ell (g s_0)^{-1}\pmod A
\tag{10a}
\]
for **every** admissible \(B\). This statement remains true if \(A^2\mid Q\); we do not assume a coprime factorization of \(Q\). The exact conditions \(g\mid j,\ s_0,\ (j,r),(B,q_0)=1\) affect only the joint \((B,\ell)\) slot once the fixed outer representation is given.

Put \(Z\asymp D/g\) and \(Q_2=Q/A=r_1/s_0\), so \(Q_2\ll Z\) by the genuine same-dyad step. Use fixed-cutoff Mellin inversion only in \(n/Z\) to separate the smooth Fourier test from the \(B\)-coefficient, with log-power integrable norms, by normalized derivatives. All sharp conditions on \(n\), including (5), the divisor cutoff and units, stay on the \(n\)-side. Their coefficients are bounded by \(L^C\) even after the unit-modulus Mellin character in \(n/Z\) is included. For each such separated contribution let
\[
 V(t)=\sum_{\substack{n\asymp Z\\(n,Q)=1}}c_n
                                   e_Q((N/f)t\overline n).
\]
Write \(t=t_A+A k\) on the unique coset (10a), where \(k\pmod{Q_2}\). By orthogonality over \(k\), inversion on the unit classes of \(Q_2\), and bounded coefficients,
\[
 \sum_{k\bmod Q_2}|V(t_A+A k)|^2
 \ \le\ Q_2 L^{C}\sum_{a\bmod Q_2}
                    \bigl(\#\{n\asymp Z:n\equiv a\bmod Q_2\}\bigr)^2
 \ \ll\ (Q_2+Z)ZL^C\ \ll Z^2L^C.
\tag{10b}
\]
Indeed \(N/f\) is a unit mod \(Q_2\), and \(\overline{n_1}\equiv\overline{n_2}\pmod{Q_2}\) iff \(n_1\equiv n_2\); phases from \(t_A\) are harmless inside the squared norm. Injectivity of (10) and Cauchy over \(B\) give \(\ll\sqrt S\,Z L^C\) per fixed \(\ell\). Summing the true frequency length \(\le x^{\alpha/2-\Delta}\) still saves \(x^{-\Delta}\) relative to \(SZ\), up to log factors. At a common dyadic divisor exponent \(b\) this has saving \(1-2b-\alpha/2\) before reserving smoothing slack.

For fixed \(g,f,s_0\) each \(Q\) has \(O(1)\) actual outer representations \(s_0Q=A r_1\), because every \(A\) is a prime divisor in \(S\) and determines \(r_1\). The Poisson prefactor \(H/(fs_0 Q)\) summed over this dyad of moduli is \(\ll H/(f s_0)\); multiplying by the proved bound before this prefactor gives \(O(xS x^{-c_\Delta}/(g f s_0))\), since \(HZ\asymp x/g\). There is no additional \(B\)-sum, and \(g,f,s_0\) have harmonic costs. Together with the true zero mode and physical tails this proves cancellation throughout the claimed strip; there is no marker divisor or assumed cancellation of a Kloosterman energy.

## 3. Exact BV overlap and uniform evaluation of the Euler main

For fixed \(s\), quotient primes are at scale \(Y=x/S\). For \(d\le x^{b_0}\), apply standard maximal BV at \(Y\) to \(q\equiv N\bar s\bmod d\), with \((d,Ns)=1\). This is below \(Y^{1/2}\) by the fixed exponent reserve \(.01\alpha\). The retained true primes excluded previously are a power-small difference. For a reference see the classical theorem in the introduction to [Akbary–Hambrook](https://arxiv.org/pdf/1309.2730v2); to pass from the von Mangoldt to the prime version, for the proper prime powers, the maximal sum of per-residue counts over all moduli \(d\le x^{b_0}\) is \(O\big(x^{b_0}Y^{1/2}\log^2Y\big)\): each maximum is at most their entire contribution at scale \(Y\), so this is power-small compared with \(Y\). Partial summation gives the corresponding unweighted prime theorem. The two weights \(W_s(v),\log((N-sv)/d)\) have uniformly log-power sup norms and total variation on \(I/s\); maximize over prefixes to handle arbitrary retained endpoints. The BV error is \(O_B(YL^{-B})\) per \(s\), even with bounded log factors in (5), so \(O_B(xL^{-B})\) in all.

For \(Z\ge x^c\) fixed \(c>0\), apply
\[
 \frac{a}{\phi(a)}=\sum_{e\mid a}\frac{\mu(e)^2}{\phi(e)},\qquad
 \mu(ev)=\mu(e)\mu(v)1_{(e,v)=1}
\]
to the summatory function of \(\mu(a)a/\phi(a)\) with \((a,E)=1\). Below \(\sqrt Z\) in the \(e\)-variable use (8) and \(\sum_e1/(e\phi(e))<\infty\); above it the bound \(Z\sum_{e>\sqrt Z}1/(e\phi(e))\ll Z^{1-c'}\) suffices with an absolute \(c'>0\). Hence the summatory function is \(O_B(Z(\log Z)^{-B})\) uniformly for \(E\le x^{O(1)}\), also when \(Z\) is arbitrarily large (apply (8) at parameter \(Z\) instead of \(x\)). By partial summation both Euler series below have arbitrary log-power tails. For real \(z>0\), exactly
\[
  F_E(z)=\sum_{(a,E)=1}\frac{\mu(a)}{\phi(a)a^z}
   =\frac{G_E(z)}{\zeta(1+z)},\qquad
  G_E(z)=
 \prod_{p\nmid E}\frac{1-1/((p-1)p^z)}{1-p^{-1-z}}
 \prod_{p\mid E}(1-p^{-1-z})^{-1}.
\]
\(G_E\) is analytic near 0 by absolute convergence of the first product and finiteness of the second. Here \(E=Ns\) is even. These are also the uniform Goldston–Yıldırım tails quoted in [Huang–Li, Lemma 1](https://huixil.wordpress.com/wp-content/uploads/2019/10/on-a-variant-of-the-elliott-halberstam-conjecture-and-the-goldbach-conjecture.pdf), since \(\log E\ll\log Z\). Abel convergence, justified by the summatory estimates also for the derivative series, gives
\[
 \sum_{\substack{a\le Z\\(a,E)=1}}\frac{\mu(a)}{\phi(a)}\ll_B L^{-B},\qquad
 -\sum_{\substack{a\le Z\\(a,E)=1}}\frac{\mu(a)\log a}{\phi(a)}
       =G_E(0)+O_B(L^{-B})=\mathfrak S(E)+O_B(L^{-B}).
\tag{11}
\]
For the first BV main insert \(Z=\min(U,x^{b_0})\ge x^{.40}\), and split the real weight \(\log((N-sv)/d)\) at \(\log d\). This is the first line of (2).

For the second BV main keep both factors. Write \(Z_0=x^{b_0}\); its coefficient sum is
\[
 \sum_{\substack{\ell\le V\\(\ell,E)=1}}\Lambda(\ell)
 \sum_{\substack{d\le\min(U,Z_0/\ell)\\(d,E)=1}}
                             \frac{\mu(d)}{\phi(d\ell)} .
\]
If \(\Lambda(\ell)\ne0\), write \(\ell=p^k\). The exact factor \(\phi(d)\phi(\ell)/\phi(d\ell)=1-p^{-1}1_{p\mid d}\) splits the inner sum into \((1-1/p)\) times the unrestricted-in-\(p\) sum plus \(1/p\) times the \(p\)-coprime sum, all divided by \(\phi(\ell)\). Both sums are covered by the first identity in (11) with \(E\) or \(Ep\), since their cutoff is \(\ge x^{.398+o(1)}\). Finally \(\sum_{\ell\le V}\Lambda(\ell)/\phi(\ell)\ll L^C\). This proves the negligible second term with no hidden Euler main.

## 4. Related scope

[Pham Van Khanh, *Uniformity, Local Structure and Boundary Correlations in Goldbach Representations*, v1 (30 Oct 2026)](https://www.preprints.org/manuscript/202610.3061), Appendix A uses ordinary BV with \(DM<x^{1/2-\epsilon}\) for mixed prime–rough slope sums. B.1 proves weighted Type I for the full reflected-prime/rough sequence below \(x^{1/2}\); B.4 treats the rough reference on fixed-rank products. D.2 is a two-rough benchmark, D.4 an upper sieve, D.5 explicitly assumes a centered two-sided covariance, and F.4 compares actual product-formation primes to the rough reference only off an exceptional set of targets. Appendix L's rational-target kernel concerns different parity-signed weights with a complementary slab outside its estimate. None of these statements supplies (2) above *quotient-prime* BV, and (2) does not provide a general BV improvement for arbitrary modulus coefficients, a whole prime-shift asymptotic or binary Goldbach. The mechanism here is the exact moving prime label \(B\) recovered from (10), localized to one coset modulo \(A\) by (10a), and the literal signed zero-mode cancellation of (5).
