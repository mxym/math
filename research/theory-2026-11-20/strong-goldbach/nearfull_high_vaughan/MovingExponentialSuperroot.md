# Moving exponential weights across the actual square-root prime collar

Use \(N,J,L,y,R_J(N)\) and the binary singular series
\(\mathfrak S(N)\) of
[the polynomial smoothed reduction](PolynomialSmoothedGiantReduction.md).
Write \(M_N=|J|N\mathfrak S(N)\).
Fix \(\gamma=1/100\) and put
\[
       h=L^\gamma,\qquad s=h^{-1},\qquad
       D=L^{\gamma+\delta},\qquad
       U=\sqrt N\,e^{-D}L^{-C},\qquad V=\sqrt N\,e^D .
\]
Here \(C>0\) is a sufficiently large fixed BV denominator power
and \(\delta>0\) is fixed with \(\gamma+\delta<.10\).
For the square-root collar result below choose \(\delta\) still
smaller, only after fixing the projection and its bank parameters.
Set
\[
 B_{N,s}=\prod_{p\nmid N}\left(1-\frac{p^{-s}}{p-1}\right),\qquad
 W_s(m)=\prod_{p\mid m}(1-p^{-s}),\qquad
 R_{J,s}=\sum_{\substack{x+y=N,\ x,y\ {\rm prime}\\x\in NJ}}
                       (\log x)(\log y)(y/N)^s.
\]
A prime 2 is excluded from \(B_{N,s}\) because \(N\) is even.
Primes in \(W_s\) occur once regardless of multiplicity.
For a real interval \(I\), write
\[
 {\cal P}_s(I)=
     \sum_{\substack{x+mr=N,\ x,r\ {\rm prime}\\x\in NJ,\ r\in I,\ m>1}}
           (\log x)(\log r)(y/N)^s W_s(m).
\]
This is a positive statistic of the literal two genuine prime
labels, with no largest-prime choice except that the label
\(r>V\) is automatically unique on each surviving row.

**All-even calibration.** For each such fixed \(\delta\), at
every sufficiently large even target, with all Euler terms
evaluated at the moving \(s=1/h\),
\[
 {\cal P}_s((U,\infty))
 =\int_{NJ}(y/N)^s\{B_{N,s}\log(y/U)+B_{N,s}'\}\,dx
        -R_{J,s}+o(M_N).                                         \tag{1}
\]
The prime-binary term has its literal spatial multiplier.
The derivative is with respect to \(s\).

**Actual crossing of the square root.** For each fixed \(B_0>0\)
there is a sufficiently small fixed \(\delta>0\) such that for
\(\operatorname{rad}(N)\le L^{B_0}\) the **entire** genuine
square-root collar with the same positive weight satisfies
\[
 {\cal P}_s((U,V])
   =B_{N,s}\log(V/U)\int_{NJ}(y/N)^s\,dx+o(M_N).                 \tag{2}
\]
In particular the original positive statistic restricted to
\(r>V\) obeys the closed identity
\[
 {\cal P}_s((V,\infty))
 =\int_{NJ}(y/N)^s\{B_{N,s}\log(y/V)+B_{N,s}'\}\,dx
        -R_{J,s}+o(M_N).                                         \tag{3}
\]
The error here is on the \(M_N\) scale of the binary term, not
merely small relative to a positive main of order \(L/h\) times
that scale. This is different from the fixed-\(\beta\) statement
in [ZeroCutoffExponentialMoment.md](ZeroCutoffExponentialMoment.md):
the Euler product and its derivative are not replaced by their
first Taylor terms. It remains necessary to bound the actual
\(r>V\) score strictly below the displayed model by more than
the error. Nothing here bounds that unpriced positive score or
gives binary positivity.

## 1. Complete the real exponential in the finite BV model

Take a fixed smooth nonincreasing \(\chi\) on the nonnegative
axis, 1 up through \(1/2\) and 0 from 1 on.
Use \(b_N=D/L\),
\[
     F_N(t)=\chi(t/b_N)e^{-sLt}\quad(t\ge0),\qquad w_N=-F_N'.
\]
The weights \(w_N\) are nonnegative and integrate to 1, so
integrating a uniform BV error costs no additional norm.

Use the literal finite model (4)--(5) of
[the zero-cutoff proof](ZeroCutoffExponentialMoment.md) for
\(0\le\tau\le b_N\), with the same common \(U\) as above,
\(B_\tau=N^{1-\tau}\) and \(T_\tau(y)=y/B_\tau\).
The proof there does not need \(\tau\) bounded away from zero
or \(T_\tau\) large: the unmarked moduli obey \(n\le e^D\)
and the marked actual modulus \(dn\) is at most
\(Ue^D=\sqrt N/L^C\).
Its genuine prime BV errors with maximal prefixes and fixed
divisor multiplicity therefore stay \(O_A(NL^{-A})\)
uniformly, on choosing a sufficiently large fixed \(C\) for
the prescribed fixed accuracy. All proper-power errors
including true marks \(>U\) are power-small. Keep the same
target units and the strict real \(n<T_\tau(y)\).

At fixed genuine \(x,y\), the binary atom \(G_\tau\) in that
proof marks \(y\le B_\tau\), equivalently
\(\tau\le\log(N/y)/L\). This endpoint is below \(b_N/2\)
for all central \(y\) for large \(N\). Its integrated weight
is \(1-(y/N)^s\) exactly. Thus after integrating the finite
identity the original binary count minus this atom is
precisely \(R_{J,s}\). It has not been estimated by an
unscaled \(o(1)\) change in the density. For \(m>1\) the
old upper \(r\le B_\tau\) gate remains redundant off
\(Q_{\tau,y}=0\), just as in the zero-cutoff proof.

At fixed real central \(y\), integrating the finite model
before changing its \(n\)-sum gives the actual factor
\(F_N(\log(nN/y)/L)\), since the \(n\)-gate is strict and
the measure is continuous. This factor equals
\((y/N)^s n^{-s}\) whenever \(n\le(y/N)e^{D/2}\).
The tail when removing the cutoff is
\(O_A(NL^{-A})\): use \(n^{-s/2}\le e^{-cL^\delta}\)
on that tail and
\(\sum (1+\log n)/(\varphi(n)n^{s/2})\ll s^{-2}\).
The last elementary estimate follows by the absolutely
convergent positive convolution \(n/\varphi(n)=
\sum_{d\mid n}\mu^2(d)/\varphi(d)\), or by its Euler
product. The bracket's prime-power part is
\(\ll L\) uniformly in \(n\), by the exact local totient
ratios used in the zero-cutoff proof. The same exponential
saving pays the \(\log(y/n)\) tail.

On physical rows we may also replace \(F_N\) by its full
exponential at arbitrary fixed log accuracy, **in the
actual absolute score**. Indeed \(m\le N/U=N^{1/2+o(1)}\)
so (4) of the polynomial reduction holds with a fixed
constant (e.g. use the lower exponent .49 there).
The profile difference
\((1-\chi(t/b_N))e^{-sLt}\) vanishes for \(t\le b_N/2\)
and has a fixed compact upper extension above all
physical arguments \(t\le\log(N/U)/L\); extend by zero
on negative \(t\). Its \(j\)-th derivative has \(L^1\)-norm
\(\ll_j L^{O_j(1)} e^{-cL^\delta}\) for every fixed \(j\).
The positive Fourier--Euler estimate in the polynomial
reduction with \(H=L\) and a fixed prime-exponent upper
bound applies to this entire actual quotient range.
Its Fourier polynomial degree is fixed independently of
\(h\) and \(b_N\). Integration by parts more times than
that degree leaves \(O_A(NL^{-A})\), even after accounting
for the at most logarithmic target singular series.
At \(m>1\) the complete divisor weight really factors
as \((y/N)^sW_s(m)\), including multiplicities.
These arguments price a moving profile tail; they
have not yet altered the physical lower endpoint \(U\).

The resulting absolutely convergent finite-BV principal
is
\[
 \int_{NJ}(y/N)^s\{B_{N,s}\log y+B_{N,s}'
                         -B_{N,s}{\cal D}_{N,s}(U)\}\,dx,
\]
where
\[
 {\cal D}_{N,s}(U)=
    \sum_{\substack{p^j\le U,\ j\ge1\\p\nmid N}}
       \frac{\log p}{\varphi(p^j)}
          \frac{1-p^{-s}/p}{1-p^{-s}/(p-1)} .
\]
For the prime power \(p^j\) the first ratio arises by
replacing the \(p\)-Euler factor of
\(\sum_{(n,N)=1}\mu(n)/(\varphi(n)n^s)\) with its
\(p\mid p^j\) factor \(1-p^{-s}/p\). The negative
logarithmic moment in \(n\) is \(B_{N,s}'\).
For \(p\nmid N\), hence \(p\ge3\), that displayed ratio
is \(1+O(p^{-2})\), uniformly in \(s>0\).
Consequently \({\cal D}_{N,s}(U)=\log U+O(\log L)\),
by the usual harmonic \(\Lambda\)-sum and deleting
\(p\mid N\) as in the zero-cutoff proof.
Also \(B_{N,s}\ll s\mathfrak S(N)\): factor out
\(\zeta(1+s)^{-1}\), bound the non-target Euler ratios
by absolute convergence, and bound the excluded-prime
product by \(\prod_{p\mid N}(1-1/p)^{-1}\ll\mathfrak S(N)\).
Thus \(B_{N,s}O(\log L)\) costs \(o(M_N)\), since
\(h=L^\gamma\gg\log L\). Combining the exact \(R_{J,s}\)
part with these models proves (1).

## 2. The genuine covered part of the physical collar

Now take \(N\) of polylogarithmic radical. Choose the usual
fixed separated prime bank families as in
[the high-cut proof, §§3--4](Proof.md) and its
[prime-column input](../polynomial_prime_columns/UntwistedNearRoot.md):
there are \(\asymp_K\log L\) disjoint families of \(K\)
separated colors, their primes have logarithms between
a constant times \(L^{.10}\) and \(2L^{.20}\), and each
color has fixed positive reciprocal mass with fixed
upper bound. Take \(K\) sufficiently large after the
fixed projected accuracy and divisor/mesh losses.
Let \(E(m)=1\) mean some family has a genuine \(m\)-factor
in every color.

On \(U<r\le V\) the actual cofactor scale is
\(m=N^{1/2}\exp(O(D+\log L))\).
Replace the genuine left prime by the usual
\(Z=\exp(L^{.24})\)-rough Vaughan expansion with cutoffs
\(N^{.10},N^{.10}\), as in
[TinyMOriginalGiant, §2](TinyMOriginalGiant.md).
After excluding actual bank-square incidence,
extract \(w\mid m\), one real prime per color of the
first successful family, and put \(m=w m'\).
The exact allocation is \(\prod_i(1+\omega_i(m'))^{-1}\);
prior families are disjoint and their tests stay on \(m'\).
The factor \(W_s(m)\) separates exactly as \(W_s(w)W_s(m')\):
the individual tag multipliers \(1-p^{-s}\) are bounded
by 1. After restoring the extracted-prime gcd mask,
the only new rows still have actual \(p^2\mid y\) and
all factors divide the physical arguments, so are paid
by actual-square counting and fixed crossed divisor moments.
The actual residual is \(m'r\), including \(\log r\) and
the full real \(r\)-interval \(U<r\le V\).
No smoothing of the \(r\) gate is needed: it is entirely
on this residual. Central tests including \((y/N)^s\)
are smooth-separated on the two genuine source factors
with the usual log-power mesh/smoothing and negligible
physical central boundary. Both source factors are
\(Z\)-rough, so they avoid all chosen tags and the
determinant endpoint primitivity remains as in the cited
projection. The long signed \(\mu\) major and restricted
Bessel apply at the given radical, and the true residual
has squared norm \(O((N/Y)L^{O(1)})\) on a tag shell
\(w\asymp Y\). Thus the covered Type II is arbitrary-log
small in the actual weights. All powers in the error
budgets can be fixed for \(0<\delta<.01\).

For Type I hold each true \(m\) fixed. The actual opposite
\(r\) is genuine, at scale \(N/m=N^{1/2+o(1)}\), and its
BV progression modulus \(q=afe\le N^{.20+o(1)}\) is
inside the ordinary BV range at that scale. Here \(a,f\)
arise from the two short \(Z\)-rough Vaughan terms
(\(f=1\) in the first) and \(e\) is the ordinary short
roughness opening of the free coordinate. The literal
reduced class is \(N\bar m\bmod q\), with the mask
\((m,Nq)=1\); retain the true unit condition at \(N\).
The weights \(E(m)W_s(m)\) are fixed here; \((y/N)^s\)
and the left free log have uniformly fixed log-power
prefix variation. The divisor weights and rough
opening use the same factorial and BV bounds as
TinyMOriginalGiant. BV errors are summed by the true
\(N/m\) scales, hence with only the \(m\)-harmonic.

We explicitly allow primes of \(m\) above \(Z\). At such
primes the coprimality mask is on \(a,f\), not on the
small rough opening \(e\). The signed
\(\mu(a)/\varphi(a f)\) zeroth harmonic and the
\(\mu(a)\log a/\varphi(a)\) derivative harmonic remain
uniform with all of \((af,Nm)=1\) retained: relative to
\(\zeta^{-1}\) the primes \(\le Z\) have at most a
log-power absolute Euler norm at
\(\sigma=1-c/\log Z\), and primes \(p\mid Nm\), \(p>Z\)
have total \(O(L/Z^\sigma)\) in that norm. This gives
arbitrary-log signed tails at \(a=N^{.10}\) by the
same ordinary zeta Mertens/Rankin proof as in
[TrueCompositeQuotientCredit, §2](TrueCompositeQuotientCredit.md).
The second Type I zeroth harmonic vanishes also when a
prime is in \(f\), using the actual product totient.
The first derivative has local factor
\((1-1/p)^{-1}\) at \(p\le Z\) or \(p\mid Nm\),
and \(p(p-2)/(p-1)^2\) elsewhere.
Its true \(e\)-product is
\(\prod_{p\le Z,p\nmid Nm}(1-1/(p-1))\).
Multiplying gives exactly
\(\mathfrak S(N)c(m)\), where
\(c(m)=\prod_{p\mid m,p>2}(p-1)/(p-2)\) on \((m,N)=1\).
Thus the covered collar has model
\[
 \mathfrak S(N)\int_{NJ}(y/N)^s
   \sum_{\substack{y/V\le m<y/U\\ (m,N)=1,\ E(m)=1}}
                    \frac{c(m)W_s(m)}m\,dx
     +O_A(NL^{-A})                                                \tag{4}
\]
at the fixed targeted accuracy. The real measure \(dx/m\)
is from the actual change of variable \(x=N-mr\).
The literal \(m\)-gate in (4) is the one from the true
\(r\)-interval and not a separately chosen extension.

## 3. A genuine positivity estimate on missed banks

At fixed true prime \(r\in(U,V]\), the interval in \(m\)
has scale \(X=N/r=N^{1/2+o(1)}\). The actual other form
is \(x=N-rm\), and the prime \(r\) is a target unit.
Let \(W_0=\exp(L^{\gamma+\delta/2})\); this is strictly
below all bank primes. Since every \(W_s\) factor is
between 0 and 1, it has the true positive upper
\[
             W_s(m)\le
               \prod_{p\le W_0}(1-p^{-s}1_{p\mid m}).
\]
With \(x\)-avoidance on these same primes, this is a
product \(\prod_{p\le W_0}(1-\rho_p(m))\) with
\(0\le \rho_p(m)\le1\).
At \(p\nmid Nr\) the two bad roots \(m=0\) and
\(x=0\) are disjoint and their weights are \(p^{-s}\)
and 1; at \(p\mid N\) there is a single coincident
root of weight 1, including \(p=2\).
The local factor at such a target prime is just
\(1-1/p\), with no additional \(W_s\) depletion.
All these are literal roots in the free variable \(m\).

Sieve \(x\) by one positive Selberg sieve on the other
primes up to a fixed tiny power of \(N\), omitting
the small and bank alphabets. Take for instance
squarefree divisor support \(N^{.01}\) and sifting
up to \(N^{.0005}\). At those outside primes the
ordinary one-root model suffices; the prime \(r\)
exceeds the sifting limit. Restore exactly the
omitted small-prime test by the above product and
the omitted bank-prime \(x\)-avoidance together
with the real \(1-E(m)\) condition.
At each bank prime the two roots are disjoint:
each bank prime is a target unit and smaller than \(r\).
Given avoidance of \(x\), the density for its bank
divisibility root is \(1/(p-1)\). Different bank
families use entirely disjoint alphabets, and
each color has fixed reciprocal mass bounded below.
Thus the independent **integer local** bank-failure
factor is \(\ll L^{-\kappa}\) for some fixed \(\kappa>0\)
after selecting \(K\).

For rigor in multiplying these tests, open the
\(1-E(m)\) Boolean by the usual separable signed
avoidance patterns (only \(L^{O_K(1)}\) of them).
Approximate the avoided root products on the small
and bank alphabets by successive Bonferroni brackets
at degree \(\lceil C_A\log L\rceil\), treating the
small local weights in \([0,1]\) exactly.
Add the positive first-omitted degree tails before
multiplying by the nonnegative outside Selberg
majorant. The reciprocal mass on these alphabets
with root counts is \(O_K(\log L)\), so the factorial
model errors beat any prescribed log power after
choosing \(C_A\). This includes the polynomial
number of signed Boolean patterns. The finite
squarefree labels from both omitted alphabets
have product and count \(\exp(O_K(L^{.20}\log L))\),
which is subpower. The exact CRT moduli are their
product with the outside label, since the alphabets
are disjoint. The outside Selberg coefficients
are at most \(3^{\omega(d)}\); all floors per
fixed \(r\) cost \(N^{.02+o(1)}\), even with the
omitted labels and polynomial-log Boolean counts.
Upon summing the actual \(r\)'s, \(r\le N^{.5+o(1)}\),
and restoring both logs, these errors are power-small.
These are integer root calculations followed by
a positive upper, not an independence assumption
for the two genuine primes.

The resulting local density is at most a constant times
\[
 \frac1L\, L^{-\kappa}
       \prod_{p\le W_0,p\nmid N}
                          \left(1-\frac{p^{-s}}{p-1}\right)
             \ll \frac{\mathfrak S(N)}{hL}L^{-\kappa}.
\]
For the first assertion reinsert all the
\(1-1/p\) prime factors, then the conditional
small and bank tests just computed. For the last
bound the omitted Euler tail beyond \(W_0\)
has \(\sum_{p>W_0}p^{-s}/p\ll e^{-cL^{\delta/2}}\)
by prime Mertens/partial summation; use
\(B_{N,s}\ll\mathfrak S(N)/h\).
Now \(\log x\le L\) is paid by this actual
prime sieve. The genuine remaining prime harmonic
is
\[
    \sum_{U<r\le V,\ r\ {\rm prime}}\frac{\log r}{r}
                             \ll 1+\log(V/U)\ll D+\log L
\]
by a fixed-ratio upper bound, not short-interval PNT.
Thus the true missed \(W_s\)-weighted prime rows have
total \(O(M_N L^{\delta-\kappa})+o(M_N)\).
The same bound with at most \(O((\log L)^{O(1)})\)
additional factor pays the missing part of (4):
on the ordinary integer \(m\)-interval, use the
same exact disjoint small/bank positive upper
without \(x\)-avoidance, so the local small factor
is now \(\prod_{p\le W_0}(1-p^{-1-s})\ll1/h\).
The harmonic caps on these real intervals have
floors \(O(N^{-1/2+o(1)})\) per label, and their
logarithmic length is \(\log(V/U)\).
Bound \(c(m)\ll\log L\) in this positive estimate,
and drop the unit mask only for it.
After fixing all bank data and \(\kappa\), choose
\(0<\delta<\min(.01,\kappa/3)\).
The claimed true and model misses are then both
\(o(M_N)\); no further positive powers of \(L\)
were suppressed in this bound.

## 4. The full exact local model of the real collar

At each real \(y\) the complete harmonic in (4) uses
the multiplicative function
\(g_s(m)=1_{(m,N)=1}c(m)W_s(m)\).
Its Dirichlet series in \(v\) is \(\zeta(v)H_{N,s}(v)\)
with
\[
 H_{N,s}(v)=
   \prod_{p\mid N}(1-p^{-v})
    \prod_{p\nmid N}\bigl(1+(c(p)(1-p^{-s})-1)p^{-v}\bigr).
\]
At \(\operatorname{Re}v=1-s/2\) the absolute coefficient
norm of \(H_{N,s}\) is \(L^{O(1)}\): the non-target
prime increments are \(O(p^{-s}+p^{-1})\), so the
log norm costs \(O(\log(1/s))\); for the target
primes split at \(L^2\) and use the summable
\(p^{-1+s/2}\) norm and their \(O(L)\) count above.
Ordinary harmonic summation of the convolution with 1
therefore gives, uniformly in the real central \(y\),
\[
        \sum_{y/V\le m<y/U}\frac{g_s(m)}m
                 =H_{N,s}(1)\log(V/U)+O_A(L^{-A}).
\]
Indeed both scales are \(N^{1/2+o(1)}\), so the
harmonic arithmetic flooring plus the discarded
Dirichlet tail is at most \(L^{O(1)}\exp(-c sL)\).
Endpoint equality is included by the usual count
of a single integer at this scale.

The local identity \(\mathfrak S(N)H_{N,s}(1)=B_{N,s}\)
holds prime by prime. At target primes the inverse
\(1-1/p\) cancels exactly, including 2. At \(p\nmid N\)
the product is
\[
 \frac{p(p-2)}{(p-1)^2}
    \left(1+\frac{[(p-1)/(p-2)](1-p^{-s})-1}{p}\right)
                      =1-\frac{p^{-s}}{p-1}.
\]
Insert this model into (4), replenishing the paid
model misses and adding the bounded genuine misses.
This proves (2). Finally subtract it from the
all-even calibration on the exact same score and
the exact same \(U\). This proves (3), with its
original genuine \(r>V\) boundary and actual
\(R_{J,s}\) term unaffected. On fixed central \(J\)
one also has \(R_{J,s}=R_J(N)+o(M_N)\) by
\((y/N)^s=1+O_J(s)\) and the genuine binary upper.
