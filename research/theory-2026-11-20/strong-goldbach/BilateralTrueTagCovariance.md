# A fixed-target signed covariance under two actual prime-factor tags

This is a signed result on a literal mask in the **bilateral smooth** Goldbach ledger, not an upper count on a sieve surrogate. It depends on the freedom to set the smooth \(q\)-kernel, whose whole-row null was proved in [BilateralSmoothRoughReduction](BilateralSmoothRoughReduction.md). It does not give a sign on the complement, which may change when the kernel is changed.

## 1. Statement and choices

Keep \(N=2x\), \(q,m=N-sq\), \(s,n,W_s,L,M_N\), unit conditions and central intervals as in the bilateral note. Its actual sum has weight
\[
 X_h(s,q)=W_s(q)(\log m)H_h(q)H_f(m)
\]
on composite \(q,m\). For the same \(f\), choose the fixed flattening width sufficiently small that \(f=f_0=(1-t)g(t)\) for \(t\in[.039,.046]\), as allowed in the previous construction. Choose one fixed real \(h\in C_c^\infty\), supported inside \([-.4,.4]\), equal to 1 near 0 with \(h'(t)=1\) on \([.110,.125]\). No monotonicity outside this band is needed.

Let \(A=(x^{\alpha_0},x^{\alpha_1})\), \(B=(x^{\beta_0},x^{\beta_1})\) denote **prime** bands in \((x^{.100},x^{.105})\) and \((x^{.040},x^{.045})\) respectively. They have fixed positive widths, chosen sufficiently small *after* fixing \(h,f\). Put
\[
 H_A=\log(\alpha_1/\alpha_0),\quad H_B=\log(\beta_1/\beta_0),\quad
 K=\omega_A(q),\quad J=\omega_B(m),
\]
where \(\omega_I\) counts distinct prime factors in \(I\). Uniformly for all large even targets, each of
\[
 \sum_{s,q} X_h(s,q)1_{\{K\ge1,\ J\ge1\}},\qquad
 \sum_{s,q} X_h(s,q)1_{\{K=1,\ J=1\}}
                                                                       \tag{1}
\]
is at most \(-c\,H_AH_B M_N\), with an absolute \(c>0\) for the above derivative choices. Indeed each mask already forces both legs composite: \(q\asymp x/s\gg a\) for \(a\in A\), \(m\asymp x\gg b\) for \(b\in B\). For the original bilateral weight \(W_s B_h C_f\) the only extra terms on these masks are proper prime powers, already bounded by \(x^{.57+o(1)}\) and \(x^{.50+o(1)}\) in the bilateral note. No additional prime term is silently approximated.

## 2. The actual double-tag principal

First weight by \(KJ\). Then sum separately over true \(a\mid q,\ b\mid m\) from the two bands. Discard rows where \(q\) is divisible by \(s\), some \(a^2\mid q\), or some \(b^2\mid m\) in the respective bands. The actual absolute cost is power-small. At fixed \(s\), with \(X=x/s\), opening a square in one of the bands costs \(O(Xx^{-.040}+x^{.105})\) by \(\sum_{p\ge x^{.040}}p^{-2}\ll x^{-.040}\), the residue for \(m\) being unique since \(b<s\). Opening \(s\mid q\) costs \(O(X/s+1)\). The divisor bounds on the weights, the bounded multiplicities \(K,J\), and \(\sum_s1/s=O(1),\#s\le x^{.14}\) give \(O(x^{.98})\). In particular the \(a=s\) diagonal is gone. Tags meeting \(N\) are not on the unit support. On the remaining rows \(s,a,b\) are all distinct units at \(N\). The divided legs \(q/a,m/b\) are both units at \(F=Nsab\): the own-prime exclusions are as just discussed, and the opposite-leg exclusions follow from \(m+sq=N\).

For \(y\in(X/2,X]\) set \(L_y=\log y,\ L_z=\log z,\ z=N-sy\), and
\[
 g_a(t)=h(t)-h(t+\log a/L_y),\qquad
 g_b(t)=f(t)-f(t+\log b/L_z).
\]
Thus \(g_a,g_b\) vary with \(y\); their first two derivatives in \(t\) have uniformly bounded norms. By exact divisor splitting of the actual prime bits on the good rows, the two scores in \(X_h\) are
\[
 H_h(q)=\sum_{d\mid q/a}\mu(d)g_a(\log d/\log q),\quad
 H_f(m)=\sum_{e\mid m/b}\mu(e)g_b(\log e/\log m).
\]
Both sums can impose \((de,F)=1\) and \( (d,e)=1\): any common prime would divide \(N\), but both legs are units there. These conditions must not be dropped when computing the signed principal.

For fixed \(s,a,b,d,e\) satisfying those conditions the actual row is \(ad\mid q,\ be\mid N-sq\). Because \((s,be)=1\) and \((ad,be)=1\), there is one class modulo \(abde\); primitivity at \(N\) gives density \(\phi(N)/(Nabde)\) and an \(O(\tau(N))\) prefix floor error. For evaluating this principal we can count *all* the rows in these classes, ignoring the earlier \(s\) and repeated-prime deletions: the wrong weights on the removed rows are still divisor-bounded, so their contribution again costs \(O(x^{.98})\). The combined modulus search costs at most
\[
 x^{.14+.105+.045+.360+.310+o(1)}=x^{.960+o(1)}
\]
since \(d\le X^{.4}\le x^{.36}\), \(e\le(1.5x)^{.31}\). Smoothness gives a bound \(O_{f,h}(L)\) on the total variation plus supremum for each physical \(y\)-integrand after multiplication by \(\log z\). This covers the variable \(L_y,L_z\) before extending to any infinite sums.

### The finite bivariate harmonic evaluation

For \(\Re u,\Re v>0\) define
\[
 \sum_{\substack{(d,e)=1\\(de,F)=1}}
  \frac{\mu(d)\mu(e)}{d^{1+u}e^{1+v}}
 =
 U_F(u)U_F(v)\!\prod_{p\nmid F}\left(1-
   \frac{p^{-2-u-v}}{(1-p^{-1-u})(1-p^{-1-v})}\right),\quad
 U_F(u)=\frac1{\zeta(1+u)}\prod_{p\mid F}(1-p^{-1-u})^{-1}.                 \tag{2}
\]
This follows prime by prime from \(1-p^{-1-u}-p^{-1-v}\) at \(p\nmid F\). Let \(k_F(D,E)\) be the coefficients of the last product in variables \(D^{-1-u}E^{-1-v}\). At \(p\nmid F\) its local coefficients are \(1\) at \((0,0)\), \(-1\) if both exponents are positive, and zero otherwise. In particular
\(\sum |k_F(D,E)|(DE)^{-1+\delta}\ll_\delta1\) uniformly for fixed \(0<\delta<1/2\). It has finite uniform log moments of every order. Write
\[
 \mathcal K_F=\sum_{D,E}\frac{k_F(D,E)}{DE}
 =\prod_{p\nmid F}(1-(p-1)^{-2}).
\]
It is positive and bounded below by the twin-prime constant since \(2\mid F\).

For one smooth \(g\) of the above class and a shift \(u_0=\log D\ge0\), partial summation gives, for \(T\asymp L\),
\[
 \sum_{(n,F)=1}\frac{\mu(n)}n
       g((\log n+u_0)/T)
 =-\frac{F}{\phi(F)}\frac{g'(0)}T
    +O_g\!\left(\frac{F}{\phi(F)}
              \frac{1+\log L+u_0}{T^2}\right).                            \tag{3}
\]
Here the underlying coprime cumulative sum \(S_F(t)=\sum_{n\le e^t,(n,F)=1}\mu(n)/n\) satisfies
\[
 \int_0^\infty S_F(t)\,dt=\frac{F}{\phi(F)},\qquad
 \int_0^\infty (1+t)|S_F(t)|\,dt
       \ll \frac{F}{\phi(F)}(1+\log L).
\]
For the unmasked \(S_1\), absolute convergence of the first log moment follows from the ordinary prime number theorem with classical zero-free-region error (or arbitrary log reserve for the Möbius sum), and its integral is 1 by \(U_1(u)/u\to1\). For the mask, \(S_F(t)=\sum_{j\mid F^\infty,\ \log j\le t}j^{-1}S_1(t-\log j)\); the sums of \(1/j\) and \((\log j)/j\) are \(F/\phi(F)\) and that times \(\sum_{p\mid F}\log p/(p-1)\). The latter is \(O(1+\log L)\) by splitting at \(p=L^2\), using the prime reciprocal-log bound below the split and \(\log F\ll L\) above. This also proves the integral identity directly, with no need for a uniform exceptional-zero theorem for the mask. Formula (3) follows by integrating \(-T^{-1}g'((t+u_0)/T)S_F(t)\) and bounding the derivative difference by the Lipschitz norm of \(g'\). The error is valid also if the shifted support is empty.

Apply (3) twice in the coefficient convolution (2), with \(\log D,\log E\) the corresponding shifts. Compact positive support makes the original harmonic sums finite; the Rankin bound justifies extending sums of the separated principal to infinity and all error products. This gives uniformly throughout the physical interval
\[
 \sum_{\substack{(d,e)=1\\(de,F)=1}}
 \frac{\mu(d)\mu(e)}{de}
   g_a(\log d/L_y)g_b(\log e/L_z)
 =\frac{(F/\phi(F))^2\mathcal K_F}{L_y L_z}\,
       g_a'(0)g_b'(0)
 +O_{f,h}\!\left((F/\phi(F))^2\frac{1+\log L}{L^3}\right).                \tag{4}
\]
In particular the joint Euler factor is not the product of two unmasked coprime means. Indeed
\((N/\phi(N))\mathcal K_N=\mathfrak S(N)\), and the three extra prime exclusions change the factor \((F/\phi(F))^2\mathcal K_F\) from its \(N\)-value by \(1+O(x^{-.040})\).

After the physical density and the factor \(\log z\), the main integrand for the fixed tags is therefore
\[
 \frac{\mathfrak S(N)}{ab}\,W_s(y)\,
  \frac{[h'(0)-h'(\log a/L_y)] [f'(0)-f'(\log b/L_z)]}{L_y}.             \tag{5}
\]
The total error in (5), integrated and summed over all tags, is \(o_{f,h,A,B}(M_N)\), since the summed harmonic masses of \(s,a,b\) are bounded. More precisely its analytic part after the Euler normalization is \(O_{f,h}(H_AH_B(1+\log L)M_N/L)\) for fixed widths, plus the power errors.

For large \(x\), \(\log a/L_y\in[.110,.125]\) and \(\log b/L_z\in[.039,.046]\). The first bracket is exactly \(-1\). For the second note \(f'(0)=-1\), and with \(\beta=.310\) we have \(g(t)\ge0\) and
\[
 g'(t)=-(1-t/\beta)(\pi/\beta)\sin(\pi t/\beta)
\]
on the positive band. For \(t\in[.039,.046]\), \(\pi t/\beta\ge .395\), \(\sin(\pi t/\beta)>.38\) (sine Taylor and monotonicity), \(1-t>.95,\ 1-t/\beta>.85,\ \pi/\beta>10\). Thus \(f'(t)=-g(t)+(1-t)g'(t)<-3\), and the second bracket is \(>2\). Also \(W_s(y)>.4,\ L_y<L\). Summing (5) with the positive length \(X/2=x/(2s)\), and applying the prime reciprocal sums on the fixed exponent bands, proves
\[
 \sum X_h(s,q)KJ \ \le\ -\tfrac{1}{10}\,H_AH_B M_N                       \tag{6}
\]
eventually, with room: the limiting lower magnitude in (5) is at least \(0.8\log(7/5)H_AH_B M_N\). Omitting prime divisors of \(N\) costs \(O(x^{-.040})\) in the factor sums, and omitting \(a=s\) costs a power-small harmonic diagonal. No signed count of prime factors of an unlabelled cofactor is assumed.

## 3. From factorial weight to literal masks

For nonnegative integers \(K,J\) the excess \(KJ-1_{\{K,J\ge1\}}\) is nonnegative and at most
\(\binom K2 J+K\binom J2\); for \(KJ-1_{\{K=J=1\}}\) at most twice that bound. It suffices to bound the signed-weight difference absolutely by the three-tag arithmetic sums.

Discard \(s\mid q\) and repeats at any tag at the same power-small cost as above, so each extracted prime occurs with valuation one. For any prescribed distinct tags, divide the \(q\) leg by their \(A\)-product \(a_0\) and the \(m\) leg by their \(B\)-product \(b_0\). The free variable can be chosen by \(q=a_0(u_0+b_0j)\) and \(u_0\equiv N\overline{s a_0}\pmod {b_0}\), exactly as in the bilateral proof. Again both linear forms are primitive, determinant \(N\), all altered slope primes are among \(s\) and these tags, and the physical unit masks at \(N\) kill the nontrivial discriminant locals. The product of the three tags is at most \(x^{.255}\); the resulting free interval is \(\asymp x/(s a_0 b_0)\gg x^{.60}\). Each extracted prime costs at most 2 in the Fourier product, after which the extra valuation masks can be dropped for the nonnegative upper. The same corrected Henriot bound and frequency integrability as in the bilateral proof then give an absolute total
\[
 \ll_{f,h} \frac{x\,\mathfrak S(N)}{s a_0 b_0 L}
\]
at fixed \(s\) and tags, with a constant independent of their locations and chosen widths. Summing over the two triple patterns proves that the difference between either mask in (1) and (6) is
\[
 O_{f,h}\!\left((H_A+H_B)H_AH_B M_N\right)+o_{f,h,A,B}(M_N).
\]
Now fix both widths small enough to make the first coefficient less than \(1/40\) after dividing by \(H_AH_BM_N\), and take \(x\) large with those widths fixed. This gives (1), for example with \(c=1/20\).

## 4. Scope

This is an actual signed, simultaneous factor-mark result at every even target, with true \(m+sq=N\) throughout. The information is the joint Euler normalization and two slope differences in the same ledger, not a heuristic product of one-leg prime-frequency models. Choosing a different derivative of \(h\) in the \(A\)-band can reverse this local sign while preserving the same total ledger, so this theorem does not imply the as-yet-unproved signed bound on the complement. In particular the balanced actual semiprime \(q\) obstacles are outside this small-\(A\) tag sector. Neither the earlier old-\(B'\) reserve nor any other chart's negative budget is spent here, and no Goldbach representation is deduced from (1).
