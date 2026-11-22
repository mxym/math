# A bounded-rank reduction of the entire giant remainder

Let \(N\) be any sufficiently large even target, \(J\Subset(0,1)\)
a fixed nondegenerate central interval, and \(L=\log N\).
Use \(R_J(N)\) and \(\mathfrak S(N)\) of
[the original giant reduction](../giant_prime_divisor_remainder/Proof.md).
Fix
\[
            0<a<b<\tfrac12,\qquad \lambda=\tfrac12-b,\qquad
            C=\tfrac12+b.
\]
Let \(w\in C_c^\infty((a,b))\), real and not necessarily positive,
with \(\int w=1\). On \(t\ge0\) put \(F(t)=\int_{\tau>t}w(\tau)d\tau\),
and extend it smoothly with compact support to the left of zero.
For an actual row \(x+mr=N\), \(x,r\) genuine primes, \(x\in NJ\),
\(m>1\), let \(y=N-x\) and set
\[
       V_y(m)=\sum_{d\mid m}\mu(d) F\!\left(\frac{\log(dN/y)}L\right).
\]
All true marks \(r\) are counted even when a row has several; no
largest-divisor hypothesis is imposed.

**Theorem.** Given any fixed \(D>0\) there is a fixed \(C_D>0\)
such that, with \(U_*=N^\lambda L^{-C_D}\),
\[
 R_J(N)=|J|N\mathfrak S(N)-
  \sum_{\substack{x+mr=N,\ x,r\ {\rm prime},\ x\in NJ\\
                  r>U_*,\ m>1}}
        (\log x)(\log r)V_y(m)+O_{J,w,D}(NL^{-D}).                 \tag{1}
\]
This is an identity for the **entire** remainder, at every even
\(N\); no polylogarithmic-radical hypothesis is used.

Put \(M_N=|J|N\mathfrak S(N)\). For any prescribed \(\epsilon>0\)
one can take fixed \(0<\eta<\lambda/2\) and a fixed integer \(K\)
so that the difference between the true score in (1) and the
following finite-rank angular sum has absolute value at most
\(\epsilon M_N+o_{\eta,K}(M_N)\):
\[
 \sum_{\substack{x\in NJ,\ x\ {\rm prime}\\
           y=N-x\ {\rm squarefree},\
           y=p_1\cdots p_k,\ 2\le k\le K+1\\P^-(y)>N^\eta}}
        (\log x)(\log y)\,
               \mathcal K_{\lambda,F}(u_1,\ldots,u_k),            \tag{2}
\]
where all \(p_i\) are the actual prime factors, \(u_i=\log p_i/\log y\)
and
\[
 \mathcal K_{\lambda,F}(u)=
    \sum_{i:\,u_i>\lambda}u_i
       \sum_{I\subseteq[k]\setminus\{i\}}(-1)^{|I|}
                       F\!\left(\sum_{j\in I}u_j\right).          \tag{3}
\]
In particular a strict true upper bound for (2) below \(M_N\),
by more than the chosen tolerance, would give binary positivity.
Such a bound is not established here. The reduction retains all
remainders, including those whose \(m\) is of polynomial size.

## 1. Exact averaged polynomial cutoffs

At each fixed \(\tau\in[a,b]\) use the original marked-prefix
estimate (2) at \(S_\tau=N^\tau\) and \(B_\tau=N^{1-\tau}\).
It applies because \(S_\tau\) is above its subpower minimum
and is bounded by \(N^{1/2-\lambda}\). Its common admissible
cutoff is \(U_*\le\sqrt N/(S_\tau L^{C_D})\); take
\(a_d=1_{d\le U_*}\) inside that already-allowed prefix estimate.
The model for the complementary unmarked tail has maximal
BV moduli \(n\le S_\tau\le N^b\) and signed harmonic lengths
\(T_\tau(y)=y/B_\tau\gg_J N^a\).
The marked complementary moduli are \(dn\le
U_* N^\tau\le\sqrt N/L^{C_D}\).
Thus the BV/Mertens estimates are uniform for all these \(\tau\).
Actual proper-power marks \(>U_*\) are bounded by
\[
            N^{1+o(1)}U_*^{-1/2}=N^{1-\lambda/2+o(1)}
\]
by the same elementary actual-multiple count as in the original
giant proof. The replacement of the source on prime powers
and deletion of the proper-power part of \(\Lambda(y)\)
also retain power margins. This gives its literal sharp
identity for each \(\tau\) and this same \(U_*\).

For \(m>1\), \(r>B_\tau\) implies \(T_\tau(y)>m\), and hence
\(\sum_{d\mid m,d<T_\tau(y)}\mu(d)=0\). At \(m=1\) the genuine
\(r=y\) is outside all sharp remainders since \(y\asymp_J N\);
it must not be included after dropping the upper mark gate.
Integrate the remaining exact sharp divisor weights against
\(w\). The strict real inequality becomes the upper cumulative
at \(\log(dN/y)/L\). This proves (1), including for signed
\(w\), with the fixed multiplier \(\int|w|\) in its error.

## 2. A genuine two-prime bound at every fixed quotient

Remove \(x\mid N\); there are \(O_J(1)\) such central genuine
primes, with elementary divisor envelope and total \(N^{o(1)}\).
Then \(y,m,r\) are target units. On the true support
\(Y=N/m\ge N^\lambda L^{-C_D}\), so \(Y\) is polynomial and
the two genuine forms \(r,N-mr\) take central values of
sizes \(O(Y),O(N)\), respectively. With
\[
             c(m)=\prod_{\substack{p\mid m\\p>2}}\frac{p-1}{p-2}
\]
their weighted count for fixed \(m\) is at most
\[
                 A_\lambda M_N\,\frac{c(m)}m,\qquad
                      A_\lambda=\frac{2000}{\lambda},            \tag{4}
\]
for all sufficiently large \(N\), uniformly in the literal \(m\).
This bound can drop the mark gate \(r>U_*\) afterwards while
retaining the stated quotient range. For clarity, an elementary
choice yielding the very loose explicit constant is Selberg
support \(D_0=Y^{1/3}\) and sifting primes up to \(z=Y^{1/12}\).
The roots of the product are one at primes dividing \(Nm\)
and two elsewhere, and at 2 there is just one because \(N\)
is even and \(m\) is odd. The positive Selberg denominator
is \(\sum_{d\le D_0,\ d\mid P(z)}g_1(d)\), with
\(g_1(p)=\rho(p)/(p-\rho(p))\), where \(\rho(p)\) is that root
count. In the normalized complete positive Euler product
the mean \(\log d\) is
\(\sum_{p\le z}(\rho(p)/p)\log p\le(2+o(1))\log z\).
Markov retains at least \(1/3\) below \(D_0\), uniformly
in \(m,N\). Its inverse is at most
\(3\prod_{p\le z}(1-\rho(p)/p)\).
The standard Selberg coefficients are bounded in magnitude
by \(\prod_{p\mid d}(1-\rho(p)/p)^{-1}\le3^{\omega(d)}\),
so their full integer floor costs \(O(Y^{2/3}(\log Y)^{10})\),
using \(2^{\omega([d,e])}\) for the root multiplicity.
The root product is at most
\((1+o(1))\mathfrak S(N)c(m)e^{-2\gamma}/(\log z)^2\):
compare each exact local factor to \((1-1/p)^2\), then
bound the missing non-target factors by the convergent
\(p^{-2}\) tail. Missing target or \(m\) local enhancements
can only improve the upper. The interval length is at most
\(|J|Y\), and the floor is negligible relative to \(Y/\log^2Y\).
Multiply by \((\log N)(\log Y)\) and use \(\log Y\ge(\lambda-o(1))L\).
These estimates imply (4). This is only a positive upper, not a
fixed-\(m\) asymptotic for the genuine prime pair.

## 3. Explicit tails for the full score

The Fourier product (7) of
[the smoothed terminal proof](SmoothedTerminalQuotients.md)
applies here with \(H=L\), because it is an exact pointwise
factorization of the divisor sum. The quotient satisfies
\(m\le N^C L^{C_D}\); for positive Euler upper bounds
we may allow primes up to
\(P_N=N^C L^{C_D}\). For each \(t>0\) and real \(\xi\)
write
\[
 \mathcal E_{N,t}(\xi)=
 \prod_{p\le P_N}
   \left(1+\frac{t\,c(p)}{p-1}|1-e^{i\xi\log p/L}|\right),\qquad
 B_C(\xi)=\int_0^C\frac{|1-e^{i\xi u}|}{u}\,du .
\]
Here \(c(2)=1\) after positive enlargement. These products
are bounded by a polynomial in \(2+|\xi|\) for each fixed
\(t\), by the elementary split in the smoothed terminal proof.
They converge pointwise as \(N\to\infty\) to
\(\exp(t B_C(\xi))\). To see this, the differences
\(c(p)/(p-1)-1/p\) and the logarithm's higher powers have
summable \(O_t(p^{-2})\) majorants and vanish for each fixed
\(p\) as \(L\to\infty\). In the remaining reciprocal prime sum,
the part \(\log p/L\le v\) is \(O(|\xi|v)\), and above any fixed
\(v>0\) the prime reciprocal law gives the integral on
\([v,C]\). The log factor in \(P_N\) contributes \(o(1)\).
Letting \(v\downarrow0\) proves the limit. Thus the finite constants
\[
 \begin{split}
   D_F(t)&=\frac{A_\lambda}{2\pi}
            \int_{\mathbb R}|\hat F(\xi)|e^{t B_C(\xi)}\,d\xi,\\
   E_F&=\frac{A_\lambda}{2\pi}
            \int_{\mathbb R}|\hat F(\xi)|\,|\xi|e^{B_C(\xi)}\,d\xi
 \end{split}                                                       \tag{5}
\]
are explicit, with the chosen compact extension of \(F\)
and \(A_\lambda\) from (4). Take Fourier absolute values inside
the genuine-prime bound (4), enlarge the resulting harmonic
sum to all integers supported on \(p\le P_N\), and sum its
positive powers by \(\mathcal E_{N,t}\).
Marking \(t^{\omega(m)}t^{-K}\) gives
\[
 \limsup_N M_N^{-1}\!\!
   \sum_{\substack{\text{true rows of (1)}\\\omega(m)>K}}
   (\log x)(\log r)|V_y(m)|\le D_F(t)t^{-(K+1)}
          \qquad(t>1).                                          \tag{6}
\]
The marked event \(P^-(m)\le N^\eta\) gives at most
\(\eta E_F\) in this limsup, since for each fixed \(\eta>0,\xi\)
its marked local sum is bounded by
\((|\xi|/L)\sum_{p\le N^\eta}\log p/p+o(1)
=|\xi|\eta+o(1)\).
Marking a square has local sum
\(\ll(|\xi|/L)\sum_p(\log p)/p^2\), so the true nonsquarefree
\(m\) contribution is \(O_{J,w,\lambda}(M_N/L)\).
Schwartz decay justifies each complete \(\xi\)-integration.
For any \(t>1\) one can, for example, choose \(\eta<\lambda/2\)
and \(K\) so that \(\eta E_F<\epsilon/3\) and
\(D_F(t)t^{-(K+1)}<\epsilon/3\).
These are positive upper bounds over the actual entire score,
not dyadic average or distribution statements.

A squarefree \(m\) can still give nonsquarefree \(y\) if
\(r\mid m\). In that case \(r^2\mid y\) and \(r>U_*\).
The elementary number of possible \(y\)'s is
\(\ll\sum_{r>U_*}\lfloor N/r^2\rfloor\ll N/U_*\).
There are \(O_\lambda(1)\) true marks \(>U_*\) on each row,
and the fixed divisor/log weights are \(N^{o(1)}\);
this is \(N^{1-\lambda+o(1)}=o(M_N)\).
The small-factor and rank restrictions in (6) therefore
leave exactly the rows of (2), before the purely angular
cutoff adjustment: the mark \(r>N^{\lambda-o(1)}\) cannot
itself be the small factor, and the other factors are those
of its actual \(m\). Passing to \(\log y\) in the arguments
of \(F\) costs \(O_{J,w}(1/L)\) per divisor uniformly.
On the retained finite ranks and angular floor, their true
weighted volume is \(O_{\eta,K,\lambda,J}(M_N)\) by (4)
and \(\sum_{N^\eta<p\le P_N}1/p=O_\eta(1)\).
Thus this replacement costs \(o(M_N)\).

Finally the physical \(r>U_*\) and \(u_i>\lambda\) disagree
only for \(|\log r/L-\lambda|=O_{J,D}(\log L/L)\).
On these rows \(m\) lies in
\([N^CL^{-O(1)},N^CL^{O(1)}]\).
In the positive upper (4), open an actual prime factor
of \(m\) and fix its at most \(K-1\) other genuine primes.
The free prime is \(\ge N^\eta\) and confined to an interval
of multiplicative ratio \(L^{O(1)}\); its reciprocal prime
sum is \(O_{\eta,J,D}(\log L/L)\) by the uniform reciprocal
prime law starting at \(N^\eta\).
The other prime harmonics are \(O_\eta(1)\), and
\(c(m)=1+o_{\eta,K}(1)\) on this support.
This prices the entire true-rank cut adjustment by \(o(M_N)\).
Since \(\log r=u_i\log y\) exactly, summing the actual marked
orientations now gives the expression (3) and proves (2).

## 4. What the reduction does not pay

The fixed positive cutoff \(\lambda\) in (3) matters.
If one *formally* lets \(\lambda=0\) at a half-supported
profile, the sum over the complementary choices of \(i\)
collapses to
\[
             \sum_{I\subseteq[k]}(-1)^{|I|}
               (1-u_I)F(u_I),\qquad u_I=\sum_{j\in I}u_j.
\]
This is the old own-root parity/half-hinge structure,
not a new route to a sign at the root. The present claim
is the elementary true all-even finite-rank reduction for an
exact entire score with a strictly positive mark threshold.
Compare the [own-root cusp rank reduction](../true_even_cusp_rank_tail/Proof.md)
and the [literal giant reduction](../giant_prime_divisor_remainder/Proof.md).
Here the positive angular floor and every fixed rank-tail
tolerance are obtained on all remainder cohorts simultaneously.

For a nonnegative averaging weight, even just the genuine
rank-one-in-\(m\) angular sector above \(N^b\) has unsigned
mass in the ordinary two-prime angular model
\[
              \int_b^{1/2+b}\frac{dv}{v}
                   =\log((1/2+b)/b)>\log 2 .
\]
The measure \(dv/v\) results from the reciprocal genuine
prime \(m\) and the actual \(\log r\) cancelling the
\(r\)-harmonic. This statement about the angle model is not
a uniform lower for the genuine semiprime rows at a fixed
target. It shows why a common upper factor \(>2\) on
all positive angular contributions, discarding all real
compensation, does not itself give a certificate.
A signed \(w\) is permitted by (1) and could move mass,
but the resulting rank contributions must still be estimated
on the same true score. No binary result is asserted.
