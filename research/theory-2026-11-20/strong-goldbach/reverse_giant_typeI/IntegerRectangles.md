# Signed integer-rectangle deletion in the double giant residual

Use the exact direct double-Möbius remainder of [SecondTypeI.md](SecondTypeI.md).
Thus \(N\) is prescribed even, \(I\subset[N^{1/2+\varepsilon},B]\),
\(S=\exp((\log\log N)^4)\), \(B=N/S\), and \(J\subset J_0\Subset(0,1)\)
is the actual source interval. All variables below are positive integers.
In
\[
\begin{split}
 \mathcal D_I={}&\sum_{\substack{bj+amk=N,\ bj\in NJ\\
 (amk,N)=1,\ ak\in I,\ am>Q\\b>Z(N/(mk))}}
       \mu(a)\mu(b)\log j\log k\,Q_{amk}(m),\\
 &Q_y(m)=\sum_{d\mid m,\, d<y/B}\mu(d),\qquad
 Q=\sqrt N/L^D,\quad Z(X)=\sqrt{X/H}/L^{D_1},\quad
 H=\exp((\log L)^3),\quad L=\log N,
\end{split}
\]
let \(\mathcal V\) be the union of the three regions
\[
 b\le m/S^3,qquad b\le k/S^3,qquad b^{3/2}\le mk/S^{12}.             \tag{1}
\]

**Theorem.** The restriction of \(\mathcal D_I\) to \(\mathcal V\) is
\(O_{A,J_0,\varepsilon}(NL^{-A})\) for every fixed \(A>0\). Consequently
in this fixed-gap giant range the original \(C_I\) can be restricted,
with arbitrary-log error, to the double signed remainder with
\[
 b>\max(m,k)/S^3,\qquad b^{3/2}>mk/S^{12}.
\]
In particular the remaining \(b\) is at least \(N^{2/7-o(1)}\): the
previous \(b>Z(N/(mk))\) also gives \(b\gg a^{1/2}N^{-o(1)}\) because
\(amk\asymp N\); combine that with \(b>(mk)^{2/3}S^{-8}\), taking
the geometric mean with powers \(4/7\) and \(3/7\).

This is a signed deletion of three actual expanded regions, not an
absolute bound on them. It uses no small-radical restriction and no
prime distribution in the integer rectangles. It does not bound the
remaining signed part of \(C_I\), or the full giant remainder.

## 1. Uniform elementary counts with the target-unit mask

Here and below \(S^{o(1)}\) permits fixed powers of \(L\); its exponent
tends to zero for each fixed requested log accuracy. If \((b,N)=1\),
in any shifted real interval of length at most \(Y\), the count of
\(v\equiv c\pmod b\) with \((v,N)=1\) equals its interval length times
\(\varphi(N)/(Nb)\), with error
\[
 O_A((Y/b)L^{-A}+S^{o(1)}).                                           \tag{2}
\]
To verify this without a large radical loss, first use the primes
\(q\mid N,q\le L^{C_A}\). Upper and lower Bonferroni at adjacent depths
near \(C'_A\log L/\log(2\log L)\) have \(S^{o(1)}\) labels; their
reciprocal factorial error is arbitrarily log-small because the prime
harmonic is \(O(\log\log L)\). Each opened divisor of the unit mask is
coprime to \(b\), and its count has a single interval floor. For
\(q\mid N,q>L^{C_A}\), a union bound costs at most
\((Y/b)\sum 1/q+O(L)\); the reciprocal sum is \(O(L^{1-C_A})\).
This bound holds for arbitrary shifted intervals even when a large
\(q\) can give just a single object. The product main differs from the
full \(\varphi(N)/N\) by the same union bound in density. If an opened
prime exceeds the largest positive integer of the relevant interval
it gives no actual object. Partial summation in (2) pays any weight
of supremum plus variation \(L^{O(1)}\).

We also use a two-variable form. For arbitrary shifted intervals of
positive integers \(v,w\), write \(Y=1+|I_v|, Z=1+|I_w|\) for their
*lengths* plus one, not their coordinate scales. The count with
\(vw\equiv c\pmod b\), \((vw,N)=1\), \((c,b)=1\), and \((b,N)=1\), equals
\[
 |I_v||I_w|\frac{\varphi(b)}{b^2}\left(\frac{\varphi(N)}N\right)^2
 + O_A\!\left(\frac{YZ}{b}L^{-A}+
   S^{o(1)}\tau(b)^{O(1)}\Bigl(\sqrt b+\frac{Y+Z}{b}\Bigr)\right).    \tag{3}
\]
Only the error uses lengths plus one; the sieve part of the
relative error can in fact use \(|I_v||I_w|/b\), because it
is an error in evaluating the exact reciprocal main. The
complete-modulus calculation is as follows. Without the target-unit tests, expand each integer
interval modulo \(b\). Its normalized Fourier coefficient at
\(j\ne0\pmod b\) is \(O(1/\min(j,b-j))\); its constant coefficient is
its integer cardinality divided by \(b\). The two zero frequencies
give \(\varphi(b)/b^2\) times the cardinality product, since the unit
class \(v\pmod b\) determines \(w\) uniquely. Replacing cardinalities
by real lengths costs \(O((Y+Z)/b)\), with an inessential additional
\(O(1/b)\) if the intervals are bounded. For the nonzero pair use the
[Weil bound for complete Kloosterman sums, Iwaniec–Kowalski, Corollary 11.12](https://people.math.ethz.ch/~kowalski/ik-ant-exp-sums.pdf):
modulus \(b\) contributes at most
\(\tau(b)\sqrt b\,(j_1,j_2,b)^{1/2}\). For each \(g\mid b\) the sum of
absolute nonzero interval coefficients of indices divisible by \(g\)
is \(O(\log(2b)/g)\). The two-variable gcd-weighted sum is therefore
\(O(\tau(b)\sqrt b\log^2(2b))\). On a single nonzero axis use the
Ramanujan bound \(|c_b(j)|\le\sum_{g\mid(j,b)}g\), giving
\(O(\tau(b)(Y+Z)\log(2b)/b)\). No individual prime modulus is required.

Now use the two target-unit expansions as in (2), separately in
\(v,w\). If \(v=e v'\), \(w=f w'\) for target-prime labels \(e,f\),
then \((ef,b)=1\), the transformed congruence is in the unit class
\(c\overline{ef}\), and its main is modified by \(1/(ef)\). The
product of the two nonnegative upper envelopes differs from the
true joint indicator by at most the sum of the upper-minus-lower
envelope on either leg multiplied by the upper envelope on the
other. Expand each such expression; the positive factorial error
is thus paid in the integer model with the same floor count.
For large target primes use the positive union bound on \(v\) or
\(w\), applying the no-mask rectangle estimate at the scale divided
by the prime on that leg. A prime exceeding the corresponding
largest positive integer can be omitted altogether. There are at
most \(O(L)\) remaining primes, and their reciprocals are arbitrarily
log-small. These arguments apply to shifted intervals and yield (3)
with the exact displayed unit factors. They do not insert an extra
unit density for the integer \(j=(N-amk)/b\): once \(amk\) is a target
unit and \(b\mid N-amk\), that integer is already a target unit.

We need two signed harmonics. From §1 of [ReverseTypeI.md](ReverseTypeI.md),
with the same zero-free and Rankin argument, for any \(U\le N^{O(1)}\)
and \(T\asymp_{J_0} S\) we have
\[
 \sum_{d<T,(d,U)=1}\frac{\mu(d)}d=O_A(L^{-A}),                       \tag{4}
\]
and tails starting at \(\sqrt S\) are also arbitrarily log-small.
For \(F\) of sup plus variation \(L^{O(1)}\) on a dyadic \(m\)-interval
above \(T_y\), and any \(U\le N^{O(1)}\) divisible by \(N\), we also have
\[
 \sum_{m\in J_M,(m,U)=1} Q_y(m)F(m)/m=O_A(L^{-A}).                     \tag{5}
\]
For completeness, open \(Q_y\) and split at \(d=\sqrt S\). For large
\(d\) fix \(n=m/d\), apply the tail in (4) in the resulting \(d\)-interval
on \(U\)-units and sum \(1/n\). For small \(d\), count \(U\)-units \(n\)
with the Rankin bound of §1 of *ReverseTypeI*, now in ordinary intervals with
\(n\asymp M/d\gg\sqrt S\), then using the harmonic weight. This gives
main \(\frac{\varphi(U)}U\frac{1}{d}\int_{J_M}F(u)du/u\); the total
error is arbitrarily log-small. Sum \(\mu(d)\) using (4) at \(\sqrt S\).

## 2. One free integer

Work in fixed-ratio dyads \(a\asymp A_0,b\asymp B_1,m\asymp M,k\asymp K\),
with \(A_0 M K\asymp N\) on any nonempty packet. Costs of the log-power
number of dyads will be absorbed. Keep \((abmk,N)=1\) by the
original target mask. In particular \((b,N)=1\). For fixed \(a,b,k\)
and \(d\mid m\), put \(m=dn\). The actual class is
\(n\equiv N\overline{akd}\pmod b\), with no row unless \((akd,b)=1\).
The absence if \((b,d)>1\) follows from \((b,N)=1\), not from replacing
an lcm by a product. The extra condition is exactly \((n,N)=1\).
All gates are intervals in \(m\): \(ak\in I\) is fixed,
\(bj=N-akm\in NJ\), \(am>Q\), \(b\le m/S^3\), and explicitly
\[
 b>Z(N/(mk))\iff mk>N/(b^2HL^{2D_1}),\qquad
 d<T_{amk}\iff amk>Bd.
\]
The variation of \(\log k\log j\) is \(O(L^2)\) on the central interval.
Apply (2) at scale \(M/d\). The integer floor after all \(a,b,k,d\)
and logs is \(A_0B_1KS^{1+o(1)}\ll NS^{-2+o(1)}\), since a nonempty
m-free chart has \(B_1\ll M/S^3\). The relative log error, using the
absolute \(1/(bd)\) harmonic, costs only more log powers. In the main
integral in \(m\), keep the \(d<T_{amk}\) gate inside its sum;
now (4) with \(U=bN\) pays the entire signed principal. No estimate
of the signs of \(\mu(a)\) or \(\mu(b)\) is used.

In the disjoint k-free chart impose \(b>m/S^3\) and \(b\le k/S^3\).
Fix \(a,b,m\) and \(d\mid m\). The actual class is
\(k\equiv N\overline{am}\pmod b\), allowed only if \((am,b)=1\).
Again every gate is an interval in \(k\); use (2) in this class.
The floor bound is \(A_0B_1M S^{o(1)}\ll NS^{-3+o(1)}\), where
\(\sum_{m\asymp M}\tau(m)\ll ML\) pays all opened divisors.
In the integral take \(y=amk\). At fixed \(y,a,b\) all conditions on
\(m\) are real intervals: from \(r=y/m\), \(am>Q\), the dyadic
\(k=y/(am)\), and the two free-chart gates. In particular \(m\ge T_y\),
and \(b>Z(N/(mk))\) is the condition \(b>Z(Na/y)\) independent of \(m\).
The fixed \(a,b\) are coprime and the progression requires \((m,b)=1\).
Thus the remaining sum is exactly (5) with \(U=bN\) and
\(F(m)=\log(y/(am))\), times
a factor \((1/(ab))\log((N-y)/b)\,\varphi(N)/N\) in the integral.
Summing \(a,b\) in reciprocal harmonic finishes this chart.

## 3. Two free integers near the product hyperbola

For this last disjoint chart require \(b>\max(m,k)/S^3\) and
\(b^{3/2}\le mk/S^{12}\). In a feasible dyad,
\[
 B_1\gg \max(M,K)/S^3,\qquad B_1^{3/2}\ll MK/S^{12}.
\]
These imply \(M\gg \sqrt K\,S^{15/2}\) and \(K\gg\sqrt M\,S^{15/2}\),
so both free variables are very long relative to \(S\), even
though neither need be longer than \(b\).

Fix \(a,b,d\) with \(d<T_y\ll_{J_0} S\), and count \(n=m/d,k\) in
the exact unit equation \(nk\equiv N\overline{ad}\pmod b\). If
\((ad,b)>1\) there is no retained row; otherwise apply (3) on a
rectangular mesh in \(m,k\) of relative size \(1/S\), at most \(O(S^2)\)
boxes per fixed dyad and parameters. In the log coordinates every
actual gate is an axis bound or a single monotone product contour:
these include \(d<T_y\), \(b>Z(N/(mk))\), \(bj\in NJ\), and the
threshold \(b^{3/2}\le mk/S^{12}\). A boundary contour crosses only
\(O(S)\) boxes (each vertical log strip meets \(O(1)\) horizontal strips
along the contour), and the total boundary area in \(m,k\) is
\(O(MK/S)\). Apply the **positive** version of (3) to the boundary
boxes, so their true integer contribution is bounded by the
corresponding scaled volume plus the summed arithmetic errors.
For interior boxes the weight \(\log k\log((N-amk)/b)\) varies by
\(O(L^2/S)\), since the physical opposite \(N-amk\) stays central.
The same positive count pays its replacement by a box value.
Thus neither equality at a cutoff nor integer boundary concentration
is replaced by a continuous measure assumption.

Sum all the rectangle errors, allowing even \(O(S^2)\) copies for
boundary boxes. Using \(\sum_{b\asymp B_1}\tau(b)^{O(1)}\ll B_1 L^{O(1)}\)
and all \(d\ll S\), the nonrelative terms are at most
\[
 A_0 S^{3+o(1)}B_1^{3/2}
   +A_0 S^{2+o(1)}(M\log(2S)+S K).
\]
Here \(\sqrt b\) produces the first term, and the two Ramanujan axes
produce the second. Each is \(NS^{-c}\) for some fixed \(c>0\)
by the displayed dyadic inequalities. The relative tail in (3) can
be taken at any fixed log power and summed by actual box areas
(the positive boundary area is \(O(MK/S)\)). The volume error is
\(NS^{-1+o(1)}\). Consequently the model may be integrated over the
exact real domain, not an enlarged cutoff. It is
\[
 \frac{\varphi(b)}{b^2}\left(\frac{\varphi(N)}N\right)^2
 \int\!\!\int \log k\log((N-amk)/b)
   \sum_{\substack{d<T_{amk}\\(d,bN)=1}}\frac{\mu(d)}d \,dm\,dk.
\]
All real gates except \(d<T_{amk}\) are outside the \(d\)-sum, and
\(T_{amk}\asymp S\). Formula (4) pays this principal uniformly in the
actual \(a,b\), after harmonic summation in \(b\). This finishes the
third signed deletion. The estimated kernel is not the residual on
\(b^{3/2}>mk/S^{12}\); no estimate for that kernel is assumed.
