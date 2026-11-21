# A genuine Heath–Brown free-factor component of the signed notch

In the actual far-angle covariance of [FarAnglePoissonDescent.md](FarAnglePoissonDescent.md), retain both genuine prime-log slots \(p_1,p_2\) of exponent near .09. The exact Heath–Brown component of \(\mu(d)\) having a free factor with complementary product at most \(x^{.01}\) gives cancellation to arbitrary log power, even against the full \(\mu(r)\) on the opposite row. It also gives cancellation against the same component on the opposite row. This removes those parts of the **physical equality**, including nonzero Poisson frequencies in their sum; it is not an estimate for the remaining balanced signed component.

## 1. Exact component in the actual Möbius function

Write \(U=x^{.01}\), \(\mu_2=\mu*\mu\), with \(*\) Dirichlet convolution. Let \(\delta(n)=1_{n=1}\), let \(\mathbf 1\) be constantly one, and use a fixed integer \(J=60\). On the whole \(d\)-band \(.489\le\log_x d\le.491\),
\[
 \mu(d)=\sum_{\nu=1}^{J}(-1)^{\nu-1}\binom J\nu
       \big((\mu1_{\le U})^{*\nu}*\mathbf 1^{*(\nu-1)}\big)(d).
 \tag{1}
\]
Indeed \(\delta-(\mu1_{\le U})*\mathbf 1=(\mu1_{>U})*\mathbf 1\) has support contained in \((U,\infty)\); its \(J\)-fold convolution has no support below \(U^J=x^{.60}\). Multiply the binomial identity by \(\mu\) by convolution, using \(\mu*\mathbf 1=\delta\).

Call a tuple in (1) a long-free tuple if some \(\mathbf 1\)-slot is \(d/c\), where the product \(c\) of all other slots is at most \(U\). Such a slot is unique since \(d>U^2\): it exceeds \(U\), and every other slot is at most \(c\le U\). Conversely, fixing \(c\mid d,c\le U\) and the index of the distinguished \(\mathbf 1\)-slot, the \(\mu\)-slot cutoffs on the remaining tuple are redundant. The convolution of the remaining \(\nu\) Möbius slots and \(\nu-2\) free slots on \(c\) is \(\mu_2(c)\). Summing the \(\nu-1\) possible distinguished positions gives the exact combined coefficient
\[
 \begin{split}
 a_U(d)&=-\sum_{\substack{c\mid d\\c\le U}}\mu_2(c),\\
 \mu(d)&=a_U(d)+b_U(d),\\
 \sum_{\nu=2}^J(-1)^{\nu-1}\binom J\nu(\nu-1)&=-1.
 \end{split}
 \tag{2}
\]
In the last identity use the binomial sum and its first derivative at 1. Thus \(b_U\) is represented by just the tuples without a distinguished free slot of this size; no approximating surrogate has been asserted. The piece is nonzero, e.g. \(a_U(d)=-1\) for prime \(d>U\). Since \(|\mu_2(c)|\le\tau(c)\), \(|a_U(d)|\le\tau_3(d)\).

## 2. The physical covariance and a large common-product gcd

Use \(x=N/2,\ L=\log x\), \(A,B\asymp Y\) actual distinct prime labels, and independent actual prime slots \(p_i\asymp P_i\). Let \(d\asymp D\), \(r\asymp R\), \(h\asymp H\), \(h'\asymp H'\) be one pair of boxes of the earlier note; in particular
\[
 \begin{gathered}
 Y\le x^{.0151+o(1)},\quad x^{.089}\le p_i\le x^{.091},
 \quad x^{.489}\le d,r\le x^{.491},\\
 x^{.418}\le h,h'\le x^{.422},\quad DP_1H,\ RP_2H'\asymp x.
 \end{gathered}
\]
All integer slots and labels are units modulo \(N\); both \(m_1=dp_1h,m_2=rp_2h'\) lie in fixed compact subintervals of \((0,N)\) bounded away from 0 and \(N\) by fixed multiples of \(x\). Smooth weights on the named normalized free and product slots have bounded magnitude and derivatives bounded by fixed powers of \(L\), as in the previous note. Let \(\mathcal Q(\alpha,\beta)\) be this expanded physical sum over
\[
               N-m_1=A u,\quad N-m_2=B u,\quad u>0
 \tag{3}
\]
with coefficients \(\alpha(d)\overline{\beta(r)}(\log p_1)(\log p_2)\kappa_A\overline{\kappa_B}\) and the smooth weights. Allow arbitrary bounded pair masks on \(A,B\) (e.g. the far-angle mask), and log-power \(\kappa\). Then for \(|\beta(r)|\le\tau_3(r)\),
\[
                \mathcal Q(a_U,\beta)\ll_{B_0}xY L^{-B_0}
                    \qquad \text{for every fixed }B_0>0.
 \tag{4}
\]
The same holds with the two rows swapped. The prime-weight normalization and boxes are unchanged from the original covariance.

Here are details on discarding large physical gcd. Put \(j=B-A\). On solutions of (3),
\[
       (m_1,m_2)=(j,m_1)=(j,m_2),
 \tag{5}
\]
since \((m_1,m_2)\mid j\) in the unit domain, and \(m_1\equiv m_2\bmod j\). If \(v\mid(m_1,m_2)\), then \((v,ABN)=1,\ v\mid j\), and \(u\) is in a single progression modulo \(v\), so \(m_i/v\) runs through a reduced class modulo \(A_i=A,B\). Both full factorization coefficient absolute sums are bounded by \(L\tau_5(m_i)\), since \(\tau_3*\mathbf 1*\mathbf 1=\tau_5\). The elementary argument for (3) of the previous note, with \(\tau_5^2\le\tau_{25}\), gives the power-of-log mean-square AP bound at scale \(X\asymp x/v\) because \(A_i\ll X^{1/25}\) for \(v\ll Y\). The proof is to choose the largest of 25 factors and trivially count its required reduced residue; the product of the other 24 is \(O(X^{24/25})\). By Cauchy, the absolute contribution per \(A,B,v\) is
\[
             \ll (x/(vY))\tau_5(v)^2 L^{O(1)}.
\]
Summing \(O(Y(Y/v+1))\) possible labels and \(v>L^K\) bounds the entire physical tail by \(xY L^{O(1)-K}+xL^{O(1)}\). This uses the actual product coefficients and applies uniformly to the unfolded \(a_U\) term also because its *absolute unfolded* coefficient is bounded by \(\tau_3(d)\). Thus take \(K\) sufficiently large, and impose only \((j,r)\le L^K\), since its failure forces the physical tail. Any sharp \(h,h'\) endpoints can again be smoothed to arbitrary log-power precision by (1) of the previous note and the global fourth moment of \(\tau_5\).

## 3. Two-dimensional completion

Put \(a=Ap_2,\ b=Bp_1\). Exactly as in the prior physical proof, \(p_1\ne p_2\), \(p_1\nmid m_2,\ p_2\nmid m_1\), \(A\nmid m_1,\ B\nmid m_2\), and
\[
         g=(bd,ar)=(d,r),\qquad g\mid j,\quad(g,abN)=1.
 \tag{6}
\]
Thus for fixed \(A,B,p_1,p_2,r\) with the new outer restriction \((j,r)\le L^K\), sum over \(g\mid(j,r)\). Write \(d=g d_1,\ r=g r_1,\ q=a r_1,\ C=Nj/g\). Keep \((b,q)=1\), \((d_1,q)=1\); with the other displayed outer restrictions imposed, these enforce exactly the desired gcd \(g\), even for nonsquarefree \(d,r\). The equality \(b d_1 h-q h'=C\) is equivalent to (3) on the support, as in the previous note.

Unfold \(a_U(d)\) using (2). The condition \(c\mid g d_1\) is precisely \(c_1\mid d_1\), where \(c_1=c/(c,g)\). If \((c_1,qN)>1\) there can be no term. Otherwise put \(d_1=c_1 s\). Enforce \((s,N)=(h,N)=1\) by independent expansions over \(k\mid (s,N)\) and \(f\mid(h,N)\) with coefficients \(\mu(k)\mu(f)\). Then \(s=k z,\ h=f t\), and the complete congruence is
\[
          zt\equiv C_f\overline{b c_1 k}\pmod q,\qquad
          (z,q)=1,\qquad C_f=C/f.
 \tag{7}
\]
Both \(f\mid C\) and \((f k,q)=1\) because \(f,k\mid N\) and \(q\) is a unit modulo \(N\). There is no restriction that \(t\) be a unit modulo \(q\); this is essential when the right hand side is nonunit. The condition \((h',N)=1\) is then automatic in the sum after inclusion-exclusion because the row coefficients are units modulo \(N\) and \(C\) is divisible by \(N\). Also
\[
           (C_f,q)\le (j,r)\le L^K,
 \tag{8}
\]
since \((a,j)=1\), \(r_1\mid r\) and \(q\) is coprime to \(N\).

For two real intervals of lengths \(\mathcal L_1,\mathcal L_2\), both at most \(q\), completion gives the count of (7) in their integer points as
\[
 \frac{\varphi(q)}{q^2}\mathcal L_1\mathcal L_2+
           O_\eta(q^{1/2+\eta}(C_f,q)^{1/2}).
 \tag{9}
\]
Indeed for each unit \(z\bmod q\) there is exactly one residue \(t\), and the nonzero Fourier pairs give complete Kloosterman sums \(S(k_1,k_2 C_f\overline{b c_1 k};q)\). Use the classical Weil bound and \((k_1,k_2 C_f,q)\le (C_f,q)(k_1,k_2,q)\). On multiples of a divisor \(e\mid q\), the sum of the interval Fourier-transform absolute values over nonzero frequencies is \(O((q/e)\log(2q))\) by the geometric sum. Expand \((k_1,k_2,q)^{1/2}\le\sum_{e\mid(k_1,k_2,q)} e^{1/2}\); the resulting terms are bounded exactly as in [MacroShiftRootLattices.md](MacroShiftRootLattices.md), including pairs with just one frequency zero. Integer-length rounding changes the main term by \(O(1)\) since the interval lengths are at most \(q\).

Here \(q\ge x^{.5929-o(1)}\) since \(g\le L^K\), whereas the coordinate lengths \(D/(g c_1 k)\) and \(H/f\) are \(\ll x^{.491+o(1)}\) and \(\ll x^{.422+o(1)}\); all intervals in the completion satisfy the hypotheses even when some have length under one. For continuous weights and the original dyadic boxes, bivariate partial summation uses (9) on subrectangles. The relevant test in \((d_1,h)\) includes the actual window \(h'=(b d_1 h-C)/q\), so normalized \(h'/H'\) is
\[
  \frac{(b(D/g)H)}{q H'}\frac{d_1}{D/g}\frac hH-\frac C{q H'}.
\]
Both coefficients are \(O(1)\) uniformly, because \(DP_1H,\ RP_2H'\asymp x\) and \(|j|\ll Y\); all partial summation variations are at most log powers including mixed derivatives. In normalized \((z,t)\) these same bounds hold by the displayed scalings. No fixed independent window for \(h'\) is presumed.

The sum of the errors (9) over \(r,g,k,f,c,A,B,p_1,p_2\), with their coefficient magnitudes, is at most
\[
     x^{o(1)} U Y^2 P_1P_2 R \sqrt{Y P_2 R}
       \ll xY\,x^{-.00335+o(1)}.
 \tag{10}
\]
Here the \(g,k,f\) multiplicities are divisor bounds \(x^{o(1)}\); \(\sum_{c\le U}|\mu_2(c)|\ll UL\), and \(\sum_{r\sim R}|\beta(r)|\ll RL^2\). The last exponent is exactly
\(.01+\tfrac32(.0151)+.091+\tfrac32(.091+.491)-1=-.00335\),
so there is fixed margin even allowing arbitrary log factors and choosing the positive \(\eta\) in (9) sufficiently small. In particular this comparison does not require a prime-count upper bound, and it retains the actual prime slots and their weights.

## 4. The weighted continuous term is genuinely small

The exact continuous weight integral in the original \((d_1,h)\) variables is independent of \(c,k,f\), including its boundaries and coupled \(h'\) condition. Under \(d_1=c_1 k z,h=f t\) the only dependence of its area after (9) is the Jacobian \(1/(c_1 k f)\). Thus \(k,f\) yield \((\varphi(N)/N)^2\) exactly; there is no endpoint term surviving beyond (10). It remains to bound for fixed \(g,q,N\)
\[
       \sum_{\substack{c\le U\\(c/(c,g),qN)=1}}
             \frac{\mu_2(c)}{c/(c,g)}
         \ll_{B_0}L^{-B_0}.
 \tag{11}
\]
Factor \(c=c_g c_0\) where \(c_g\) is supported on primes dividing \(g\) and \((c_0,g)=1\). Since \(\mu_2(p^e)=0\) for \(e\ge3\), the relevant \(c_g\) satisfy \(c_g\mid\operatorname{rad}(g)^2\) and \(c_g\le L^{2K}\), so there are only log-power choices including their divisor weights. The coprimality restriction first tests \(c_g/(c_g,g)\) against \(qN\), and on a surviving term the remaining harmonic sum is
\[
                  \sum_{\substack{c_0\le U/c_g\\(c_0,gqN)=1}}
                    \frac{\mu_2(c_0)}{c_0}.
\]
For every \(E\le x^{O(1)}\) and \(W\ge x^{.009}\), this sum up to \(W\) is \(\ll_{B_0} L^{-B_0}\). In fact the coprime \(\mu_2\) is the convolution square of coprime \(\mu\); the hyperbola formula and the uniform coprime Mertens bound from (6) of the previous note give
\(\sum_{n\le t,(n,E)=1}\mu_2(n)\ll_F t(\log t)^{-F}\)
uniformly for \(t\ge W\) with any reserve \(F\). All factors to which Mertens is applied have scale at least \(\sqrt t\) and \(E\le t^{O(1)}\). The full harmonic sum is zero: by partial summation the series converges, and by Abel passage it equals the value at \(s=1^+\) of \(\zeta(s)^{-2}\prod_{p\mid E}(1-p^{-s})^{-2}\), which is 0 for each fixed \(E\). Integrating the uniform summatory bound on the tail \([W,\infty)\) makes the cancellation uniform in \(E\). This proves (11).

Finally the original continuous test has area \(O((D/g)H)\), and \(\varphi(q)/q^2\le1/q=1/(a r_1)\). The sum over \(r_1\asymp R/g\) of \(\tau_3(g r_1)/r_1\) is \(\ll\tau_3(g)L^2\), and \(\sum_{g\le L^K}\tau_3(g)/g\) costs only logs. Hence (11), with arbitrary reserves, gives \(O_{B_0}(xY L^{-B_0})\) after summing the labels: \(DH/(YP_2)\) times \(Y^2P_1P_2\) is \(O(xY)\). This and the two genuine error bounds prove (4).

## 5. Exact scope of the improvement

By bilinearity and (4) in both orientations,
\[
           \mathcal Q(\mu,\mu)
                 =\mathcal Q(b_U,b_U)+O_{B_0}(xY L^{-B_0})
 \tag{12}
\]
on the actual off-diagonal covariance, including the far-angle part. This is not a bound just for the Poisson zero mode: the genuine component was counted with its entire physical equality via the completed Kloosterman terms. Both actual \(p_i\) remain present. The separate rough-reference subtraction before Cauchy is unchanged. The still-unproved part \(\mathcal Q(b_U,b_U)\) retains both signed sums after excluding *all* tuples with free slot exceeding \(d/U\) or \(r/U\) respectively; the complement and the fixed polynomial threshold are exact. This theorem gives no bound for a general tuple in that complement, nor for binary Goldbach.

The underlying Möbius version of the convolution identity is classical; for a published application see [Matomäki–Teräväinen, *On the Möbius function in all short intervals*](https://www.utupub.fi/bitstream/handle/10024/183097/4411198-10.4171-jems-1205-print.pdf?isAllowed=y&sequence=1). The application here is to the stated physical fixed-target covariance with both .09-scale prime slots, not to all reflected-prime correlations.
