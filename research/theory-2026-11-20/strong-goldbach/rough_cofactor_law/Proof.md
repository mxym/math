# The signed law of the actual small-prime part of the multiplier

Use the moving near-half notation and the same actual triples as in [the fixed-target rough difference](https://github.com/mxym/math/commit/81604636). Thus \(p+sq=P,\ p,q\) are prime, \(p\in[P/3,2P/3]\), \(q>P^\alpha\), and \(T_v\) weights these rows by \((\log q)/L\) when \(P^-(s)>P^{1/v}\). Here \(L=\log P,\ H=\log L,\ w=H^3,\ \alpha=1/2-H^{-7/4},\ U=\mathfrak S(P)|C|/L^2\), and \(S=2T_w-T_{2w}\) is a signed measure, with \(S[{\rm all}]=(e^{-\gamma}+o(1))U\). For those definitions, the actual two-large-prime error was \(o(U)\), so any **bounded physical indicator** below is equally valid when just the largest eligible \(q\) is retained. Keep
\[
 \beta=H^{-23/8},\quad y=P^\beta,\quad
 s_{\le y}=\prod_{\ell\le y}\ell^{v_\ell(s)},\qquad
 Y=\log(s_{\le y})/\log y,\quad A=(1-\alpha)/\beta.
\]
In particular \(Y=0\) includes \(s=1\), while \(Y>0\) excludes it. All limits hold for every sufficiently large even target, without averaging.

**Theorem.** As a literal statistic over actual prime triples,
\[
 \begin{array}{ll}
 S[Y=0]=e^{-\gamma}(A+1)U+o(U),\\
 S[Y\le B]=e^{-2\gamma}(A+1)U+o(U) & (0<B\le1\ {\rm fixed}),\\
 S[0<Y\le1]=(e^{-2\gamma}-e^{-\gamma})(A+1)U+o(U),\\
 S[Y>1]=\{-e^{-2\gamma}A+e^{-\gamma}-e^{-2\gamma}\}U+o(U).
 \end{array}                                                     \tag{1}
\]
In particular every fixed shell \(a<Y\le b,\ 0<a<b\le1\), has signed contribution \(o(U)\) at the original Goldbach scale. For every fixed \(B>0\),
\[
 \frac{S[Y\le B]}{A U}\ \longrightarrow\ e^{-2\gamma}\rho(B),    \tag{2}
\]
where \(\rho\) is the Dickman function. Thus for every fixed \(1\le a<b\) the signed contribution on \(a<Y\le b\) is asymptotic to the **strictly negative**
\(e^{-2\gamma}(\rho(b)-\rho(a))AU\). These are raw indicator restrictions, not smooth Laplace tests or target-dependent threshold choices. The binary prime-pair term is contained exclusively in \(Y=0\); (1) evaluates that entire population, not its division into primes and composites. In particular (1) does not settle that split or imply a Goldbach representation.

## 1. Open the entire small part, not just one marked prime

Write \(z=P^{1/v}\), \(v=w\) or \(2w\), \(h=\beta v\asymp H^{1/8}\). Apart from \(O(P/P^{1/(2w)}+\omega(P))\) in weighted total, discard nonsquarefree rough rows and exceptional \(p\mid P\), as in the preceding theorem. For a real restricted row let \(d=s_{\le y}\). It is now squarefree and equals the entire \(y\)-smooth part of \(m=P-p\): the marked \(q\) is larger than \(y\). For \(Y\le B\) it is characterized by
\[
 (d,P)=1,\quad d\le y^B,\quad z<r\le y\ \ (r\mid d),\qquad
 d\mid m,\quad (m/d,\prod_{r\le y}r)=1 .
\]
Conversely these conditions force this exact \(d\). Thus there is no multiplicity when recombining physical errors from powers. We temporarily include rough residuals with repeated primes \(>y\); they too are covered by the same estimate.

Given the prime progression \(p\equiv P\bmod d\), a sieving prime \(r\le y,\ r\nmid P\), tests \(r\mid m/d\) with conditional prime density
\[
  g_d(r)=\phi(d)/\phi(dr)=
 \begin{cases}1/(r-1), &r\nmid d,\\1/r,&r\mid d .\end{cases}
\]
The latter modulus contains \(r^2\). The CRT principal for jointly imposed distinct residual primes factors into these conditional densities. Therefore the rough principal multiplier is
\[
 V_d(y)=V_P(y)\!\prod_{r\mid d}\frac{(r-1)^2}{r(r-2)}
      =V_P(y)\{1+O_B(h/z^2)\},\quad
 V_P(y)=\prod_{r\le y,r\nmid P}(1-1/(r-1)).
\]
Here \(\omega(d)\le Bh\); \(r>z\) on the support.

The total large-\(q\) logarithm for a physical \(d\) comes from \(\log(m/d)\) less the prime-factor logarithms in \(y<r\le P^\alpha\); these marks cannot divide \(d\), and proper powers are paid above. The logarithmic mass of these small marks divided by \(L\), with \(r\mid P\) omitted, is \(\alpha-\beta+O(1/L+1/y)\). For \(\log(m/d)/L\) the central interval allows \(1-(\log d)/L+O(1/L)\). For the empty mark and the positive sum of marks, apply adjacent even/odd Bonferroni truncations around \(12H\) to the remaining sieve up to \(y\). Since \(\sum g_d(r)\le H+O(1)\), their model errors relative to \(V_d(y)\gg1/L\) are \(O(e^{-8H})\). They occur with positive weights before the final signed difference. All physical moduli, including a logarithmically weighted mark, have size
\[
        \le P^{\alpha+(B+12H+2)\beta}<\sqrt P/L^K
\]
for each fixed \(K\), as \(H\beta=o(H^{-7/4})\). They are exactly \(der\) (or \(de\) without the mark), including the repeated prime when \(e\) meets \(d\). At most \(\tau(n)^C\) choices occur at a single modulus \(n\) for some absolute \(C\). Thus maximal-residue Bombieri--Vinogradov gives an arbitrary-log total error, by the standard divisor-weighted Cauchy corollary. The exceptional \(p\mid P\) may be included in the progression theorem and discarded after sifting; even a crude divisor-weighted accounting on those \(O(\omega(P))\) values of \(m\) costs only \(P^{o(1)}\). Omitting sieving primes dividing \(P\) is then exact.

For \(z<r\mid d\le y^B\), one has \(1/\phi(d)=d^{-1}(1+O_B(h/z))\). The harmonic mass over the outer \(d\)'s is \(O_B(h)\) by the Euler product for \(z<r\le y^B\). Uniformly in all targets, restoring possible \(r\mid P,\ r>z\), to this outer harmonic sum costs \(O_B(hL/z)\). The main prefactor \(X_0 V_P(y)\), \(X_0=\int_C dt/\log t\), equals \(e^{-\gamma} U/\beta\{1+O(1/L+1/\log y+L/y)\}\) by Mertens with its uniform target Euler factors. All displayed relative errors, even multiplied by \(O_B(h)\) and by \(1/\beta\), are \(o(1)\). Consequently with the following sums over squarefree \(z\)-rough, \(y\)-smooth \(d\le y^B\) (including 1),
\[
 \begin{split}
 D_v(B)&=\sum_d 1/d,\qquad E_v(B)=\sum_d\frac{\log d}{d L},\\
 T_v[Y\le B]&=\frac{e^{-\gamma}U}{\beta}
           \big\{(1-\alpha+\beta)D_v(B)- E_v(B)\big\}+o(U).
 \end{split}                                                        \tag{3}
\]
On \(Y=0\) only \(d=1\) occurs; this gives its formula in (1) immediately.

## 2. Reciprocal-prime convolution to a precision better than every power of \(H^{-1}\)

Replace the measure of atoms \(1/r\) at \(\log r/\log y\) for \(z<r\le y\) by \(dt/t\) on \(1/h<t\le1\). Their cumulative discrepancies on every prefix of this interval are \(O(1/\log z)\) by the quantitative prime Mertens theorem; their masses are \(\log h+O(1/\log z)\). In the exponential convolution series with \(k\)-fold terms weighted by \(1/k!\), replacing one coordinate at a time in the constraint \(\sum t_i\le B\) costs at most \(k\Delta M^{k-1}\) before the factorial, since the admissible last coordinate is always a prefix. Here \(\Delta=O(1/\log z)\), \(M=\log h+O(1)\). Repeated prime coordinates cost \(O(e^M\sum_{r>z}r^{-2})\) after the same factorial sum. These bounds apply uniformly as the prefix \(B\) varies over a fixed compact interval. Partial summation therefore applies also to \(E_v\), whose continuous version weights by \(\beta\sum t_i\). The total errors \(O_B(h/\log z+h/z)\) are \(o(H^{-K})\) for **every** fixed \(K\), not just \(o(1)\).

For \(u\ge0\) put
\[
 F(u)=\sum_{k\ge0}\frac1{k!}
        \int_{\substack{x_i\ge1\\\sum x_i\le u}}\prod_i\frac{dx_i}{x_i}.
\]
Its zeroth term is 1. Differentiation, adding the \(k\) symmetric \(x_i\)'s on a convolution boundary, gives \(uF'(u)=F(u-1)\) for \(u>1\), with \(F=1\) on \([0,1]\). If \(\omega=F'\) on \(u>1\), then \(F(u)=(u+1)\omega(u+1)\). On successive intervals \(u\ge3\) the differential equation gives
\(\left|\omega'(u)\right|\le u^{-1}\int_{u-1}^{u}|\omega'(t)|dt\).
Hence the supremum of \(|\omega'|\) on \([n,n+1]\) is at most the preceding supremum divided by \(n\), for \(n\ge3\), using one-sided values at the few initial corners. In particular \(\omega\to c\) and \(F(u)=c(u+1)+O(1/(\lfloor u\rfloor-2)!)\) for \(u\ge4\). The exponential convolution Laplace transform is
\[
 \int_0^\infty e^{-s u}F(u)\,du
     =s^{-1}\exp\left(\int_1^\infty e^{-sx}dx/x\right)
     \sim e^{-\gamma}s^{-2}\quad(s\downarrow0),
\]
so \(c=e^{-\gamma}\). This elementary derivation of the usual Buchstab asymptotic also supplies its constant **intercept**. Integration by parts gives
\(\int_{[0,u]} t\,dF(t)=c u^2/2+O(1)\), since the difference from \(c(t+1)\) is integrable with a factorial tail.

For fixed \(0<B\le1\), the smooth upper end \(t_i\le1\) automatically follows from \(\sum t_i\le B\). Thus \(D_v(B)=F(hB)+o(H^{-K})\) for every fixed \(K\), and
\[
 E_v(B)=v^{-1}\int_{[0,hB]}t\,dF(t)+o(H^{-K}).
\]
As \(h\asymp H^{1/8}\), the factorial error at fixed positive \(B\) is \(o(H^{-K})\) for each \(K\). The parts of \(D_v,E_v\) linear in \(v\) cancel under \(2\cdot{}_w-{}_{2w}\), leaving \(c+o(\beta)\) and \(O(1/w)+o(\beta)=o(\beta)\), respectively. Substitution into (3) proves the subunit formula in (1). The two disjoint debit formulas follow by subtracting \(Y=0\) and using the independent full \(S\) evaluation. In particular the terms of order \(U\) in (1) are not claimed from a weak limit.

## 3. Full cumulative signed law

For fixed \(B>1\), use finite signed convolution to remove the coordinates \(t_i>1\) from the unrestricted \(F\). This is exponential inclusion-exclusion: on nonnegative sum at most \(B\) at most \(\lfloor B\rfloor\) removed coordinates fit. In the continuous approximation to \(D_v(B)\) it gives
\[
 \sum_{j\le B}\frac{(-1)^j}{j!}
 \int_{\substack{t_i>1\\ \sum_i t_i\le B}}
          F\big(h(B-\textstyle\sum_i t_i)\big)\,\prod_i \frac{dt_i}{t_i}.
\]
For every positive remaining argument \(u\), \(2F(hu)-F(2hu)\to c\), and the same expression is uniformly bounded for all \(u\ge0,h\ge1\) by the preceding factorial bound and compact boundedness. The face with zero remaining argument has measure zero. Thus the signed limit of the \(D_v\) is \(c\rho(B)\): explicitly, the remaining alternating exponential integral (the same expression with \(F\) replaced by 1) is 1 on \([0,1]\) and obeys \(B\rho'(B)=-\rho(B-1)\). The classical Dickman function is positive on every finite interval; for example positivity follows recursively from \(B\rho(B)=\int_{B-1}^B \rho(t)\,dt\), with \(\rho=1\) initially. It is strictly decreasing for \(B>1\). Finally \(E_v(B)=O_B(\beta h)=o(1)\), since \(\log d/L\le B\beta\) and \(D_v(B)=O_B(h)\). Inserting these estimates into (3) gives (2), at the stated precision \(o(AU)\), not in general \(o(U)\) above 1.

**Scope.** The large positive \(Y=0\) population and both explicit negative composite populations in (1) come from the same true triples, fixed target, prime test and rough difference. They are not approximations obtained by averaging over targets. Nevertheless after accounting for those composite debits, \(Y=0\) still contains composite multipliers with only factors above \(y\) and true primes \(s=1\) with identical weight. Formula (1) does not evaluate either subset separately.


For context, [Bharadwaj and Rodgers, Large prime factors of well-distributed sequences, v4](https://arxiv.org/abs/2402.11884v4) study the Poisson–Dirichlet law and restricted-support correlations for nonnegative regularly distributed sequences, including shifted primes. Here the signed operation on two rough cutoffs is applied at one prescribed reflected target and is resolved at two different scales; the Dickman and Buchstab functions themselves are classical.

[Uniformity, Local Structure and Boundary Correlations in Goldbach Representations, October 2026](https://www.preprints.org/manuscript/202610.3061), Appendices A and C, also combines directly reflected ordinary primes with roughness and maximal Bombieri--Vinogradov, including a moving below-square-root range, for a two-form row correlation. Those estimates and their balanced-endpoint caveat are distinct from the exact-small-part law and its signed intercept here. The comparison is not a priority claim.
