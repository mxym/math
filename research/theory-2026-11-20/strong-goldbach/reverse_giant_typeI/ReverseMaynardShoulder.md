# The reverse uniform-residue shoulder in the original giant remainder

Use the exact fully opened [double remainder](DoubleRough.md)
at the prescribed even target \(N\). In its notation the two
physical products are \(x=a f g\) and \(y=m c h k=N-x\);
the actual weight is
\[
          \mu(a)\Lambda(f)\mu(c)\Lambda(h)Q_y(m).
\]
Keep \(x\in NJ\), \(c h k\in I\), the independent Vaughan
cutoffs, all the true target-unit masks, and the \(z\)-roughness
of \(a,f,g,c,h,k\), where \(z=\exp((\log\log N)^2)\).
There is no roughness or primality mask on \(m\).

Fix independent dyadic intervals on \(a,f,g,m,c,h\).
The free integer \(k\) has no additional interval restriction:
keep its true rough and unit tests and the central support;
its size is then determined up to fixed ratios by \(y/(m c h)\).
Let \(u,v,\beta\) be the exponents
of the \(m,\ c h,\ f\) scales, base \(N\), and suppose with fixed
positive reserves that
\[
 u+v>1/2,\qquad 7u+12v<4,\qquad
       u+2(u+v-1/2)<\beta<1-u.                                   \tag{1}
\]
Then the signed sum on this entire actual box is
\(O_A(N(\log N)^{-A})\) for every fixed \(A>0\), uniformly in
the prescribed even target and real intervals. The factored
modulus is now on the \(m c h k\)-side, and the Siegel--Walfisz
source is the genuine coefficient \(\Lambda(f)\).

A strictly admissible center of exponent boxes is
\[
 (m,c,h,k)=(.420,.050,.035,.495),\qquad
 (a,f,g)=(.560,.434,.006),
\]
where the displayed numbers are exponents; the \(k\)-scale
follows from centrality, not a further gate. Here \(u=.420\),
\(v=.085\), and \(.430<\beta=.434<.580\).
The fully opened products are at .994 and .505. The **raw**
products \(a,m c\) have exponents .560 and .470, with sum
1.030; they are above an under-hyperbola cut \(N/S^C\)
with any fixed \(C\). Even the reciprocal-seam exponent
\(.7(1.030)+.25(.560)-.85=.011\) is positive. Thus this
is a genuinely different imbalanced region, not a relabeling
of a subcritical or balanced reciprocal estimate. A small
fixed-width neighborhood still satisfies these strict
inequalities. This is feasibility of the size configuration,
not an existence or sign claim for its arithmetic rows.

The input is [Maynard, *Primes in arithmetic progressions to
large moduli III*, Proposition 5.3](https://arxiv.org/html/2006.08250v1#S5).
The related [forward giant shoulder](MaynardShoulder.md) uses
the short score on \(m\) as the SW **source**, and the
[tagged semiprime shoulder](../UniformResidueDoubleShoulder.md)
starts from a fixed prime tag and a different score.
Here that short score instead weights one true modulus coordinate.

## 1. The actual factorable modulus and SW sequence

Use the physical \(y\)-mesh of
[GiantReciprocalSeam.md](GiantReciprocalSeam.md) to
freeze the \(m\)-interval from \(y/m\in I\) and the actual
threshold \(T_y=y/B\) in \(Q_y(m)\). The bounds there use
only divisibility and fixed divisor moments, not a prime
progression estimate, and apply unchanged before either
orientation of the congruence is taken. Smooth each real
cell as in that note. Thus \(m\) on the cell carries
\(Q_T(m)\), \(T\asymp S=\exp((\log\log N)^4)\),
with an independent interval, and the central product has
a fixed smooth weight \(\Psi(x/N)\) with log-bounded
derivatives of every fixed order.

Open the \(z\)-roughness of the free \(k\) only, by a
squarefree \(e\mid k\) on primes at most \(z\) outside \(N\)
using the actual Bonferroni truncations of DoubleRough.
The positive first-omitted-label errors are paid before
taking any congruence: the omitted label divides the
physical \(y\), and the ordinary integer multiple count
together with the factorial harmonic bound and Cauchy in
divisor moments gives \(O_A(NL^{-A})\), \(L=\log N\).
All \(e\)'s retained are \(S^{o(1)}\).
The exact modulus is
\[
       q_1 q_2=m(c h e),\qquad q_1=m,\quad q_2=c h e .             \tag{2}
\]
Both \(c,h\) are \(z\)-rough, so \(q_2\) determines \(e\)
and \(t=c h\) separately by its smooth and rough parts.
The \(q_2\)-coefficient for the actual distinct factorizations
\(c h=t\), including all individual cuts and the signed
\(e\)-label, is bounded by
\[
       \sum_{c h=t}|\mu(c)\Lambda(h)|
             \le\sum_{h\mid t}\Lambda(h)=\log t.
\]
Thus there is no \(S^{o(1)}\) multiplicity factor in the
modulus discrepancy. The \(q_1\)-coefficient is
\(Q_T(m)\) and has magnitude at most \(\tau(m)\).
The factors \(q_1,q_2\) are both target units. They need
not be coprime to each other; (2) is the actual product
required by \(e\mid k=(N-x)/(m c h)\).

On the source side use \(f\) and \(w=a g\).
The exact \(w\)-coefficient is a signed divisor sum of
\(\mu(a)\) with the other \(a,g\) cuts and rough and unit
masks, and is bounded by \(\tau(w)^{O(1)}\).
The \(f\)-coefficient is the actual \(\Lambda(f)\) on its
independent polynomial interval, with its rough and
target-unit cuts. It satisfies Maynard (4.1). For each
arbitrary auxiliary integer \(d_0\), proper powers in
the \(f\)-interval are \(O(F^{1/2}L^{O(1)})\) in log
weight at scale \(F\). The remaining genuine primes
removed by the unit masks for \(N,d_0\) cost at most
\(O(L(\omega(N)+\omega(d_0)))\) in both numerator and
reduced mean; primes in this interval are already
\(z\)-rough. The actual prime-log coefficient has
ordinary Siegel--Walfisz at \(q\le L^C\).
For larger \(q\) use the ordinary interval count
\(O(F/q+1)\) and the mass divided by \(\varphi(q)\),
with \(\Lambda\le L\) and \(\varphi(q)\gg\sqrt q\).
Choosing \(C\) according to the desired precision
gives exactly the permitted \(\tau(d_0)^{O(1)}\) loss.
This is a distribution proof for the actual coefficient;
one need not remove proper powers from the physical sum.

Twisting \(f\) by \((f/F)^{it}\) with \(|t|\le L^{C'}\)
is harmless by the interval-uniform version and partial
summation. Separate \(\Psi(f w/N)\) by Mellin as in the
[forward shoulder](MaynardShoulder.md), with fixed
log-power transform cost and arbitrarily log-small tail.
Dyadize \(w\) and \(q_2\) as needed; these costs are log
powers. The actual \(f,w\) length product is \(\asymp N\);
normalizing the \(f\)-coefficient by \(L\) if needed
puts both coefficients within the divisor pointwise
hypothesis of Proposition 5.3.

## 2. Absolute modulus errors and the signed principal

In Proposition 5.3 take \(Q_1\) at exponent \(u\), \(Q_2\)
at \(v+o(1)\), and SW length \(F\) at \(\beta\).
The dimensions are exactly (1) with a small fixed
analytic epsilon and its original strict margins.
Use the common class \(N\bmod q_1\) for the first
supremum and the actual reduced class \(N\bmod q_1q_2\)
for each second one. This is the literal congruence
\(x\equiv N\bmod q_1q_2\); no comparison is made with
a fixed small integer residue.

To absorb the \(\tau(m)\) factor, let \(\Delta(q_1,q_2)\)
be the absolute centered discrepancy for fixed signed Mellin data
and the **actual** residue \(N\bmod q_1q_2\).
For any fixed \(j\),
\[
 \sum_{q_1,q_2}\tau(q_1q_2)^{2j}\Delta(q_1,q_2)
                     \ll_j NL^{O_j(1)} .                         \tag{3}
\]
For its actual progression part, sum over the physical product
\(x=f a g\ll N\) first. Its absolute source weight at \(x\) is
at most \(L\tau_3(x)\), and a contributing modulus product
divides \(N-x\). The integer \(x=N\) never occurs: the source
coefficient keeps the target-unit mask. Possible \(x>N\) before
Mellin recombination cause no problem, since the divisibility is
then of the nonzero \(|N-x|\). Counting all \(q_1,q_2\) factorizations
and the divisor powers in (3) costs at most
\(\tau(|N-x|)^{2j+2}\). The ordinary crossed divisor moments, by
Cauchy on the fixed intervals \(x\ll N\), give \(NL^{O_j(1)}\).
This bounds the true progression part, not a supremum over arbitrary
different residue classes.

For the model part, the total absolute source mass is \(NL^{O(1)}\)
and
\[
 \sum_{q_1q_2\ll N}\frac{\tau(q_1q_2)^{2j}}{\varphi(q_1q_2)}
  \le \sum_{q\ll N}\frac{\tau(q)^{2j+1}}{\varphi(q)}
  \ll_j L^{O_j(1)} .
\]
This last harmonic follows from
\(q/\varphi(q)\ll L\) and ordinary divisor harmonic moments.
Thus (3) covers both pieces, including the actual modulo grouping.
Apply Cauchy with nonnegative measure \(\Delta(q_1,q_2)\), pairing
(3) with the arbitrary-log **unweighted** Maynard estimate.
The result absorbs the \(\tau(m)\) and \(L\) costs from §1
without a separate progression upper theorem. Choose the input
accuracy before the final Mellin summation.

For the actual principal fix \(x=f a g\), \(m,h,e\).
The coprimality cut for \(c\) is \((c,N x)=1\), together
with its roughness. The other residue and target-unit cuts
on \(m,h,e\), together with their signed weights, remain
fixed. With \(H=m h e\) the \(c\)-sum is
\[
              \sum_{c\ {\rm in\ interval}}
                     \frac{\mu(c)1_{P^-(c)>z}1_{(c,Nx)=1}}
                          {\varphi(H c)} .
\]
The dyad for \(q_2=(h e)c\), the individual \(c\)-interval,
and \(c>V=S^{1/3}\) all give ordinary real endpoints.
The \(I\)-condition is \(y/m\in I\) and is independent of
\(c\) at fixed \(x,m\); the short score \(Q_T(m)\) is also
independent of \(c\).
No squarefreeness or coprimality of \(H\) with \(c\) is
imposed except what the literal masks already require.

Uniformly in \(H\le N^{O(1)}\), take out
\(1/\varphi(H)\). The coefficients of the resulting
harmonic have local value \(1\) in
\(\varphi(H)\lambda/\varphi(H\lambda)\) if \(\lambda\mid H\),
and \(\lambda/(\lambda-1)\) otherwise. With the
Möbius sign and the rough and unit exclusions, divide
their Dirichlet series by \(\zeta(s)^{-1}\).
The unexcluded factor then differs from \(1\) by a
convergent absolute Euler correction at
\(s=1-1/\log z>.9\), since the local parameter is
\(1+O(1/\lambda)\). At excluded primes the factor is
the ordinary inverse \(1/(1-\lambda^{-s})\), with
absolute product \(L^{O(1)}\) as in DoubleRough §1.
The same Mertens/convolution/Rankin split therefore
gives \(O_A(L^{-A}/\varphi(H))\), even when \(c\) only
has the original lower bound \(V\).
The remaining real \(x\)-weights have divisor mass
\(O(NL^C)\). Also
\[
 \sum_{m,h,e}\frac{\tau(m)\Lambda(h)}{\varphi(m h e)}\ll L^C
\]
on the retained ranges: use
\(\varphi(m h e)\ge\varphi(m)\varphi(h)\varphi(e)\)
and the separate divisor, Mangoldt and squarefree
presieve harmonics. Thus the entire signed principal
vanishes with the claimed log accuracy.

This prices the specified reverse factored boxes only.
The full double giant remainder and the original
binary prime count are not bounded in sign by the result.
