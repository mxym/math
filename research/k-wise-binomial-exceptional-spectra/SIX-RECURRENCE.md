# Which fixed six-wise exceptional probabilities recur infinitely often?

In the positive-length phase and actual-departure convention of Berend–Ernst–Kontorovich–Kumar (BEKK), §5, **1/2 is the only fixed six-wise probability exceptional for infinitely many sizes n**. More precisely, for n≥8 and N=n−1, the half-probability is exceptional precisely on these two disjoint lists:

* N=(4j²+2)/3, for integers j≥3 not divisible by 3 (three departures);
* N=3h², for odd integers h≥3 (two departures).

The number of such n≤X is $(\sqrt3/2)\sqrt X+O(1)$. This does not assert that no other individual probability occurs at a six-wise exceptional size, nor does it bound all exceptional sizes after allowing p to vary with n. It contrasts with the four-wise infinite realization of **every** rational probability. The trivial boundary n=7 has a single actual departure, not an exceptional transition.

## Fixed probability and finite offsets

Use the previous [phase characterization](../k-wise-binomial-optimal-bases/PROOF.md), [six-wise rationality](../k-wise-binomial-optimal-bases/RATIONAL.md), [Hermite localization](../k-wise-binomial-optimal-bases/SPREAD.md) and [exact move theorem](../k-wise-binomial-exact-basis-moves/MOVES.md). In particular an irrational parameter is not six-wise exceptional. At an interior transition with r≥2 departures and n≥8, the common positive quadrature on the N-grid matches Bin(N,p) through degree five. For k=6 its support H consists of two isolated sites and one remaining pair of consecutive sites if r=2, or of three isolated sites if r=3. The pair starts in an old phase are ordered and lie within O(1) of t−√(3V), t, t+√(3V), respectively, with t=Np and V=Np(1−p). This is the quoted localization theorem with the three distinct zeros of the monic Hermite polynomial He₃, not an assumption about rounding those zeros. Moving from a start to its upper member or pair midpoint changes the error by at most one.

Fix rational 0<p<1, c=1−2p≠0, and suppose infinitely many N give an exception. Take an unbounded subsequence on which the type below is fixed. Put y=x−t. All centered individual sites belong to a fixed rational lattice depending only on the denominator of p, and the same holds for midpoints and sums after possibly doubling the denominator. Thus any bounded sequence of those offsets is constant on a further infinite subsequence. Products and V also lie on fixed rational lattices.

Let m_i=E y^i. The binomial central moments needed below are
```
m₀=1,  m₁=0,  m₂=V,  m₃=cV,
m₄=3V²+d₄V,  m₅=10cV²+cd₅V,
d₄=(3c²−1)/2,  d₅=3c²−2.
```
For instance these follow by differentiating the cumulant generating function N log(1−p+p exp(u)) at zero, or by the binomial factorial moments. Any quartic A(y) vanishing on H obeys E A=E[yA]=0 by degree-five quadrature.

### 1. A central pair

Assume r=2 and the actual unswitched pair is central. Its midpoint relative to t is a bounded b, now taken constant. Write l=b²−1/4, G(y)=y²−2by+l. Let S,P be the sum and product of the two centered outer singleton sites. With μ_i=E[y^i G],
```
μ₀=V+l, μ₁=(c−2b)V, μ₂=3V²+(d₄−2bc+l)V,
μ₃=(10c−6b)V²+(cd₅−2bd₄+lc)V.
```
The orthogonality of G(y)(y²−Sy+P) and its multiple by y implies
```
S=(μ₀μ₃−μ₁μ₂)/(μ₀μ₂−μ₁²),     P=(Sμ₁−μ₂)/μ₀.
```
The denominator is positive by nondegenerate nonnegative integer-grid tilting, or simply by its positive cubic leading term at large V. Comparing the cubic terms gives S→7c/3. Since S lies on a fixed discrete lattice, S=7c/3 eventually. The second formula gives P+3V tending to a finite limit K, so P=−3V+K eventually by the same lattice argument. Both moment identities thus become polynomials in V, vanishing for infinitely many V. Their nontrivial coefficients reduce to
```
K=(2b−c)(6b−5c)/6,    K(b²−1/4)=0,
(2b−c)(12b²−12bc+2c²−3)=0.
```
For 0<|c|<1 these imply b=c/2. Indeed if b=5c/6 but 2b≠c the last equation requires c²=9. If b=±1/2 and 2b≠c it requires c=0 or c=±3. Therefore K=0 and the actual central pair starts at t+b−1/2=(N−1)p, an integer. The sum of the original outer integer sites is 2Np+7c/3, hence 2p+7c/3=1+4c/3 is integral. The only nonzero possibilities are c=±3/4, or p=1/8,7/8. Both force N≡1 mod 8. But the square of the integral outer gap is S²−4P=(49+21N)/16, impossible: the numerator is 6 modulo 8.

### 2. An outer pair, or three isolated sites

If r=2 and the unswitched pair is outer, take that actual pair. If r=3, include **one auxiliary neighbor** of one of the two outer singleton sites as a fourth root, merely to define a quartic vanishing on H. No quadrature mass is assigned to this auxiliary root. For large N the three locations are separated and interior, since p is fixed and 0<p<1. In either case write the quartic as
```
A(y)=(y−h)(y−g+b)((y−b)²−1/4).
```
Here h is the centered central singleton, b is the centered midpoint of the selected outer pair, and g−b is the centered opposite outer singleton. The three-node localization above makes h and g bounded (the two outer offsets cancel to O(1)). They are constant on an infinite subsequence by discreteness, whereas |b|→∞.

Here are reproducible coefficient details of the elimination. Write A(y)=Σ a_i y^i. Its coefficients in descending order are
```
1, −b−g−h, −b²+2bg+bh+gh−1/4,
b³−b²g+b²h−2bgh−b/4+g/4+h/4,
−b³h+b²gh+bh/4−gh/4.
```
Using the moments above, set E A=3V²+BV+C, E[yA]/V=LV+T; explicitly
```
B=d₄+c a₃+a₂, C=a₀, L=10c+3a₃,
T=cd₅+d₄a₃+c a₂+a₁.
```
At every solution 3T²−BLT+CL²=0, with no assumption L≠0. For fixed h,g,c this polynomial in b vanishes for infinitely many distinct b, hence identically. Its degree is at most five, with successive leading coefficient tests:
```
[b⁵]: 2(2c−3h).
[b⁴] after h=2c/3: (14c−6g−3)(14c−6g+3)/6.
[b³] after h=2c/3 and g=7c/3±1/2: −2c(c−3)(c+3)/9.
```
These are obtained by ordinary multiplication of the displayed coefficients. The last cannot vanish for 0<|c|<1. This excludes an infinite sequence of every remaining type at a nonsymmetric fixed parameter.

## The symmetric parameter: exact converse

For p=1/2 the common positive support is reflection-invariant under x→N−x by uniqueness and symmetry of the reduced quadrature at the optimal breakpoint (as in Hermann and the cited phase theorem).

For r=3 the central singleton must be t=N/2, an integer; the other two are t±j. Orthogonality of y(y²−j²) to y gives j²=m₄/m₂=(3N−2)/4. For r=2 the unique adjacent pair must map to itself, so N is odd, its sites are t±1/2, and the outer two are t±D/2 with D odd. Orthogonality of (y²−1/4)(y²−D²/4) to the constant gives D²=(16m₄−4m₂)/(4m₂−1)=3N. These give exactly the two lists stated for N≥7; e.g. if 3N=D² with D odd then N=3h² and h odd.

Conversely, in the first case assign symmetric weights with total outer mass m₂/j², the rest at the center; in the second assign symmetric weights with total outer mass (4m₂−1)/(D²−1), the rest equally to t±1/2. The weights are strictly positive and match the second moment. Their fourth moment is correct by the very equations for j² or D² above (the fourth power reduces to a quadratic on each support); odd centered moments up through five vanish by symmetry. The roots are strictly interior and sufficiently separated in the listed ranges. At each singleton u use the old pair {u−1,u} and new pair {u,u+1}; leave the central full pair, if present, unchanged. They are disjoint in each proposed phase, with distinct actual departures. The existing tilted-mean sign rule gives strict positivity of the zero old lower weights immediately to the left, and of the zero new upper weights immediately to the right; the other weights remain positive. These are actual neighbors on positive-length intervals. Thus both lists are sufficient.

In the first list, 1≤j≤(√3/2)√X+O(1) and 3∤j; in the second, 1≤h≤√(X/3)+O(1) and h is odd. Their N have opposite parity. Adding the counts gives (√3/2)√X+O(1).
