# A double rough Vaughan reduction for the actual super-root score

Let \(N\) be any sufficiently large prescribed even integer. Use
\(L=\log N\), \(\ell=\log L\), \(S=\exp(\ell^4)\), \(B=N/S\),
\(T_y=y/B\), and \(Q_y(m)=\sum_{d\mid m,\ d<T_y}\mu(d)\).
Let \(p\) be a genuine prime in \(NJ\), \(J\subset J_0\Subset(0,1)\),
and \(y=N-p\). For any literal real interval
\(I\subset[\sqrt N S^2,B]\), put
\[
 C_I=\sum_{\substack{p\in NJ\\p\ {\rm prime}}}\log p
          \sum_{\substack{r\in I,\ r\ {\rm prime}\\ r m=y}}
                    (\log r)Q_y(m).
\]
Set \(z=\exp(\ell^2)\), \(V=S^{1/3}\), \(D=N^{1/200}\), and
\(\lambda_{>W}(n)=\sum_{j\mid n,\ j>W}\Lambda(j)\).
Assume the verified rough reversal (2) of
[ReverseTypeI.md](ReverseTypeI.md).

**Claim.** For every fixed \(A>0\), uniformly in \(J,I\),
\[
\begin{split}
 C_I={}&
 \sum_{\substack{a b+m c v=N,\ a b\in NJ,\ c v\in I\\
                 (a b m c v,N)=1,\ P^-(a b c v)>z\\ a>D,\ c>V}}
   \mu(a)\lambda_{>D}(b)\mu(c)\lambda_{>V}(v)Q_{mcv}(m)
      + O_{A,J_0}(NL^{-A}).                                   \tag{1}
\end{split}
\]
Both Vaughan Type I terms of the *opposite* \(p\) slot have
been removed, with the \(r\) slot already in its real rough
Type II form. The statement is not merely a deletion of small
\(a\) from an unrough Möbius/logarithm convolution.

After opening \(b=f g,\ v=h k\) with
\(f>D,\ h>V\) and weights \(\Lambda(f)\Lambda(h)\), the part
of (1) on
\[
                  (a f)(m c h)\le N/S^\epsilon                 \tag{2}
\]
is \(O_{A,\epsilon,J_0}(NL^{-A})\) for every fixed \(\epsilon>0\).
Thus (1) can also be written with only the strict complement
of (2) in its fully opened form. This is an actual subregion
of the expanded signed sum, with two free integer variables
\(g,k\). In that complement the identity
\((a f)(m c h)\, g k=(a b)(N-a b)\) implies
\(g k\ll N S^\epsilon\), not that either variable is bounded or
power-small. The complement is not priced, and no sign for
\(C_I\) follows. No small-radical hypothesis is used.

The related [tagged-semiprime double Vaughan reduction](../ReverseVaughanDoubleResidual.md)
also uses a two-free-coordinate CRT in a subcritical product region.
It starts with a specified polynomial-size prime tag and a
different semiprime score. Here there is no such tag: \(m\)
is the actual unrestricted quotient in the original giant
remainder, the short weight is \(Q_y(m)\) with its literal moving
cutoff, and the rough labels are retained. The two short
terms of the opposite prime are paid in all three cases below,
not by importing an unproved estimate for the tagged residual.

## 1. Sieve and harmonic conventions

All roughness sieves below use the actual integer threshold
\(z=\exp(\ell^2)\). They may be opened by successive
Bonferroni truncations of order
\(K=\lfloor C_A\ell/\log(2\ell)\rfloor\) (increase the fixed
\(C_A\) for the required log losses). The squarefree label
products then have size \(z^{K+1}=S^{o(1)}\), and
\[
 \sum_{\omega(e)=K+1}\frac{1}{\varphi(e)}
 \le\frac{(C\log(2\ell))^{K+1}}{(K+1)!}\ll_A L^{-A}
\]
when \(e\) is supported on sieved primes at most \(z\).
The same bound holds with \(1/e\). Opposite absolute label
masses, summed in the truncated support, are bounded by a
fixed power of \(L\). Work first at any requested log
accuracy, then choose truncation depths; all \(S^{o(1)}\)
bounds here are for fixed accuracy and \(\epsilon\).

We use the following uniform harmonic fact: for any
\(H\le N^{O(1)}\) and any positive-integer interval with
lower endpoint \(\gg V\),
\[
 \sum_{\substack{n\ {\rm in\ interval}\\P^-(n)>z,\ (n,H)=1}}
                      \frac{\mu(n)}n=O_A(L^{-A}).               \tag{3}
\]
This follows just as the short harmonic in the reverse note.
The Dirichlet series is \(\zeta(s)^{-1}\) times the Euler
product \(\prod_{\lambda\le z\ \text{or}\ \lambda\mid H}
(1-\lambda^{-s})^{-1}\). At
\(\sigma=1-1/\log z\) this last product is \(L^{O(1)}\):
for \(\lambda\le z\) compare \(\lambda^{-\sigma}\) to
\(e/\lambda\); the \(O(L)\) possible prime divisors of \(H\)
above \(z\) have negligible reciprocal sum. Split the
resulting convolution at the square root of the prefix
length. The classical Mertens bound on the smaller part
and Rankin on the larger give a bound
\(L^{O(1)}(e^{-c\sqrt{\log V}}+
  e^{-\log V/(2\log z)})\), which beats every fixed log power.
Differences of real prefixes preserve the literal endpoints.
For an interval with bounded variation weight one can apply
partial summation; below (3) is used at fixed integration
variable with just interval endpoints.

We also use the elementary unit-masked maximal Möbius BV
lemma of [SecondTypeI.md](SecondTypeI.md), §1, at an actual
length \(X\ge N^\delta\) with fixed \(\delta>0\).
Its proof works for a unit mask \(H\le N^{O(1)}\), not
only \(N\) itself: the target-supported Euler sums in that
proof use \(\log H=O(L)\) and the same split at \(L\).
We only use moduli \(\le N^{.01+o(1)}\) at lengths
\(\ge N^{.1-o(1)}\). Ordinary maximal prime BV is used
with the same strict margin. These applications are followed
by sums of reciprocal outer-factor masses, not by raw
summation over physical rows.

## 2. Opening the opposite prime

By rough reversal, replace \(\log r\) and the true \(r\)
indicator by the actual rough Type II expression
\[
 r=c h k,\qquad c>V,\quad h>V,\quad
 \mu(c)\Lambda(h),\quad P^-(c h k)>z.
\]
The opposite \(p\) still carries its genuine log-prime
weight. Replace it by \(\Lambda(P)1_{P^-(P)>z}\) on the
literal target units \(P=N-m c h k\); proper prime powers
cost \(N^{1/2+o(1)}\) by the physical divisor envelope
\(L^{O(1)}\tau(N-P)^{O(1)}\).
Apply Vaughan at \(D\) to \(\Lambda(P)\) exactly as
in the rough reversal. The small \(\Lambda_{\le D}\)
term vanishes centrally. The two Type I terms take the
shape \(P=a g\), \(a\le D^2=N^{.01}\), \(a\) \(z\)-rough
and target-unit, with grouped coefficient \(O(L)\);
the free integer \(g\) has weight \(1\) or \(\log g\)
and is \(z\)-rough. Their signs do not matter below.
We keep all true target-unit masks, which were common to
the rough reversal. In particular \(m,c,h,k\) are units.

We show both terms give \(O_A(NL^{-A})\). Partition the
actual rows into the following three cases (fix either
strict boundary convention).

### Case 1: \(k>N^{.1}\)

There are two free integers \(g,k\) in the literal equation
\[
                  a g+(m c h)k=N .
\]
Let \(P_0=a,\ Q_0=m c h\). Here \(P_0Q_0\le N^{.91}\).
Open the roughness conditions on \(g,k\) by labels
\(e_1\mid g,e_2\mid k\), outside \(\operatorname{rad}(N)\).
When compatible, the modulus in the integer CRT count is
the product \(P_0 Q_0 e_1 e_2\); indeed
\((P_0e_1,Q_0e_2)=1\) is forced by the equation and units.
The linear parameter advances \(x=P_0 g\) by that modulus.

For precision, at any fixed compatible tuple the condition
\((x,N)=1\) deletes one residue of the linear parameter at
each prime \(\lambda\mid N\), since its step is a target
unit. At primes \(\lambda\le z\) use a third Bonferroni
opening at the same log accuracy. At primes \(\lambda>z\)
the union bound is \(O(XL/z+L)\) in a parameter interval
of length \(X\), since each contributes \(O(X/\lambda+1)\)
and there are \(O(L)\) such primes. Thus the count in
any real subinterval, with literal endpoints, has main
density \(\varphi(N)/(N P_0Q_0e_1e_2)\), and error
\[
 O_A\!\left(\frac{N}{P_0Q_0e_1e_2}L^{-A}+S^{o(1)}\right).
\]
The floors for all tuples with \(P_0Q_0\le W\) and
presieve labels are \(O(W L^{O(1)}S^{o(1)})\)
for any \(W\) here: factor \(P_0Q_0\) into its actual
outer variables, bound the \(d\mid m\) options by a
divisor power, and use the ordinary summatory divisor
moments under the product ceiling \(W\).
In this case \(W=N^{.91}\), so the errors are negligible.
The omitted roughness tails have the factorial harmonic
bound of §1 with the same floor counts. For these positive
errors \(Q_y(m)\) may be bounded by \(\tau(m)\).
Open \(d<T_y\) literally for the weighted count and
partially sum the optional \(\log(x/a)\) on each real
interval (variation \(O(L)\)).

In the main term, exchange the \(x\)-integral with the
\(d\)-sums to recover \(Q_{N-x}(m)\). At fixed other
variables and \(x\), the signed \(c\)-sum is now
\(\mu(c)/c\) on an interval with \(c>V\), \(c\)
rough and \((c,N P_0e_1)=1\).
All other compatibility conditions are independent of
\(c\): the only \(c\)-dependent coprimality in
\((P_0e_1,m c h e_2)=1\) is \((c,P_0e_1)=1\);
\(k> N^{.1}\) gives an upper bound on \(c\), and
\(c h k=(N-x)/m\in I\) is independent of \(c\).
The grouped coefficient on \(a\) and optional \(\log(x/a)\)
also do not depend on \(c\).
Apply (3) and pay every remaining log and harmonic mass.
This removes Case 1.

### Case 2: \(k\le N^{.1}\), \(c\ge N^{.1}\)

Fix the actual \(m,h,k\), and put \(X=N/(m h k)\).
Any physical \(c\) lies in a fixed central fraction of
\([0,X]\), and \(X\ge N^{.1}\) when a row is possible.
Open \(g\)-roughness by \(e\mid g\), and independently
open \(c\)-roughness by squarefree \(d_0\mid c\) (both
outside target primes, still with \((c,N)=1\)).
The actual source equation requires
\[
 c\equiv N\overline{m h k}\pmod{a e}.
\]
This is a reduced progression, because \((a e,m h k)=1\)
is forced, and \(a,e\) are target units. If
\((d_0,a e)>1\) there is no row. Otherwise set \(c=d_0 u\);
the coefficient and mask become
\(\mu(d_0)\mu(u)1_{(u,N d_0)=1}\), and the actual residue
for \(u\) is multiplied by \(\overline{d_0}\).
The modulus remains \(a e\), not \(m h k a e\).
The length is \(X/d_0\ge N^{.1-o(1)}\), and the moduli
are \(\le N^{.01+o(1)}\).
Each modulus recovers \(a\) and \(e\) uniquely by their
disjoint prime ranges. Therefore the unit-masked Möbius
BV of §1 applies directly, summed over \(a,e\) at each
fixed \(m,h,k,d_0\).

To keep the real endpoints, open \(d\mid m\) in
\(Q_{m c h k}(m)\); this only adds the lower threshold
\(c>Bd/(m h k)\). Also \(c h k\in I\) and \(x\in NJ\)
are intervals in \(c\), and the optional
\(\log((N-m c h k)/a)\) has variation and supremum
\(O(L)\). All are admissible with maximal-prefix BV
and partial summation. The main signed bound at fixed
\(m,h,k,d_0\), after the \(a,e\) coefficients, is
\(O_A((X/d_0)L^{-A})\) with any fixed reserve.
The total \(d_0\) harmonic is a fixed log power, and
the other factors cost
\(N\sum_{m,h,k}\tau(m)\Lambda(h)/(m h k)\ll N L^{O(1)}\).
For the first positive Bonferroni error, drop the
\(c\)-roughness indicator and use one further \(g\)-sieve
label with \(d_0=1\). For the other, dominate the absolute
truncated \(g\)-sieve by its unsigned label expansion
and introduce one further \(c\)-sieve label. Thus for
both envelopes the integer count at each \(a,e,d_0\)
is \(O(X/(a e d_0)+1)\) when \((a e,d_0)=1\)
(and zero otherwise), using the actual reduced progression.
The same bound with the \((c,N)=1\) condition dropped
is a valid upper bound here because \(a,e,d_0\) remain
fixed target-unit labels. The total floors at fixed
\(m,h,k\) are \(N^{.01+o(1)}\) after all source choices,
including that extra label. Since \(X\ge N^{.1}\), the floors
are power-small relative to \(X\). Factorial tails and
outer harmonic costs are as before. This removes Case 2
without treating arbitrary rough Möbius progressions as
a new distribution axiom.

### Case 3: \(k\le N^{.1}\), \(c<N^{.1}\)

Then \(h\ge N^{.29}\) for all sufficiently large \(N\),
by the actual lower bound on \(c h k\). Replace its
\(\Lambda(h)\) by log weight on genuine primes in this
case only. Proper powers have
\(\sum_{h\ge N^{.29},\ h\ {\rm proper\ power}}1/h
 \ll N^{-.145+o(1)}\), giving negligible weight by
counting actual \(y\)'s divisible by \(h\) and using
the fixed divisor envelopes on \(x,y\).
These \(h\) are already \(z\)-rough. A true \(h\mid N\)
of this size costs negligibly by the same multiple bound,
summing its \(O(L)\) possibilities; hence \(h\) is a unit.

Now fix \(m,c,k\), \(X=N/(m c k)\), and open the source
\(g\)-roughness with \(e\mid g\). The literal progression,
when compatible, is
\[
 h\equiv N\overline{m c k}\pmod{a e}.
\]
All layouts, real endpoints and \(\log(x/a)\) work as in
Case 2. Here \(X\ge N^{.29}\) whenever there is a row.
Primality of \(h\) is kept until ordinary prime BV,
which replaces the genuine prime-log progression by
its real integral with density \(1/\varphi(a e)\).
The multiplicities of \(a e\) are unique as before,
so the maximal errors cost \(O_A(X L^{-A})\) with
arbitrary reserves before the outer reciprocal costs.
One may also use the same BV upper envelope for the
positive omitted Bonferroni tail; its main uses
\(1/\varphi(a e)\) and the factorial reciprocal bound.
No unit dependence on \(h\) is left in this modeled
density, having removed the exceptional true primes
dividing \(N\).

Change variables to \(x=N-m c k h\) in the integral.
At fixed \(x,m,k,a,e\) the now modeled measure has
a factor \(1/c\), and after restoring the short
\(d\)-sum it contains the actual \(Q_{N-x}(m)\).
The only \(c\)-dependent modulus compatibility is
\((c,a e)=1\), beyond \((c,N)=1\) and \(c\) rough.
The limits \(V<c<N^{.1}\), \(h>V\), and any previously
retained lower \(h\)-size bound define an interval in
\(c\); \(c h k=(N-x)/m\in I\) does not introduce a
divisor condition. Thus (3) cancels the signed main
in \(c\), paying all remaining harmonic labels and log
coefficients. This removes Case 3 and proves (1).

## 3. The two-free-coordinate part of the double Type II

Open the retained \(\lambda_{>D}(b)\) and
\(\lambda_{>V}(v)\) exactly, so \(b=f g,\ v=h k\)
with \(f>D,\ h>V\) carrying \(\Lambda(f),\Lambda(h)\).
Keep their roughness, actual unit masks and their log
weights; no approximation to either prime factor is
needed here. On (2) use the Case 1 CRT argument with
\(P_0=a f,\ Q_0=m c h,\ W=N/S^\epsilon\).
The product ceiling leaves a strict \(S^\epsilon\)
reserve, because the two roughness and target-unit
label counts are \(S^{o(1)}\) and ordinary divisor
moments and log weights cost only \(L^{O(1)}\).
For fixed \(x,f,m,c,h,e_1,e_2\), the exposed
\(\mu(a)/a\) harmonic satisfies \(a>D>V\),
\(a\) rough and \((a,N m c h e_2)=1\).
All other compatibility tests are independent of \(a\).
The literal inequality \(P_0Q_0\le W\) adds an upper
endpoint, and \(x\in NJ\), \((N-x)/m\in I\),
\(Q_{N-x}(m)\) are independent of \(a\).
Apply (3), now to \(a\) rather than \(c\).
This proves the stated deletion of (2).

The two fully expanded long-prime divisor coefficients
\(\Lambda(f),\Lambda(h)\) and the signed factors
\(\mu(a),\mu(c)\) are still genuinely coupled on
\(P_0Q_0>N/S^\epsilon\). Neither the ordinary BV steps
above nor the elementary CRT can be extended to that
region by applying their error term to a longer modulus.
