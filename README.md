# Exact six-bit punctured Walsh norms at every real exponent

Let \(G=\mathbb F_2^6\), \(N=64\), and for probability masses \(P,Q\)
on \(G\) let
\[
D_p(P,Q)=N^{-1/p}\Big(\sum_{a\ne0}|\widehat{P-Q}(a)|^p\Big)^{1/p}
\]
for \(1\le p<\infty\), with the maximum convention for \(p=\infty\).
The transform is unnormalized. Define
\(\Lambda_{6,p}=\sup_{P\ne Q}\operatorname{TV}(P,Q)/D_p(P,Q)\).

**Theorem.** For \(1\le p\le2\), \(\Lambda_{6,p}=64^{1/p}/2\). For
\(2\le p\le\infty\), let \(r=p/(p-1)\), with \(r=1\) at \(p=\infty\).
Then
\[
\boxed{\displaystyle
\Lambda_{6,p}=\left(\tfrac1{64}\max\{A(r),B(r),C(r),D(r)\}\right)^{1/r}}
\]
where
\[
\begin{aligned}
 A(r)&=63\cdot4^r,\\
 B(r)&=35\cdot3^r+28\cdot5^r,\\
 C(r)&=19\cdot2^r+32\cdot4^r+12\cdot6^r,\\
 D(r)&=48\cdot4^r+4\cdot8^r.
\end{aligned}
\]
On \(1\le r\le2\) the active branches in order are \(A,B,C,D\).
The adjacent crossings are the unique roots of \(B-A,C-B,D-C\),
respectively, on this interval. They lie in the following certified
intervals:

| crossing | interval for \(r\) | interval for \(p\) |
|---|---|---|
| \(A=B\) | [1.887369237, 1.887369238] | [2.126926602, 2.126926603] |
| \(B=C\) | [1.908721575, 1.908721576] | [2.100447075, 2.100447076] |
| \(C=D\) | [1.926564128, 1.926564129] | [2.079256112, 2.079256113] |

At \(p=2\) both displayed formulas give 4; other signs beyond the
exhibited \(D\)-branch examples can also attain this value.
The \(A=B\) crossing is exactly the \(p_0\) from Martinevski's
[Theorem 4.4, pp. 9–11](https://math.a-martinevski.com/publications/P16/P16_CF_V6_S8.pdf)
([fixed DOI](https://doi.org/10.5281/zenodo.23355709)). Thus bent
signs are optimal down to \(p_0\), not merely on the earlier proven
ray \(p\ge p_*\simeq2.5590\). Below \(p_0\) the two extra branches
and both additional transitions give the sharp value, not just
a non-bent counterexample.

The Boolean part of the proof is independent of any full spectral
catalogue. The few remaining scalar comparisons are certified over
entire real intervals with integer arithmetic, not by testing a
grid of exponents.

## 1. Duality, puncturing, and exhaustive cases

For a sign \(s(x)\in\{\pm1\}\), write
\(W(a)=\sum_x s(x)(-1)^{a\cdot x}\).
The columns of the nonzero-frequency Walsh matrix \(H'\) give
\(h=P-Q=N^{-1}H'c\) with \(c_a=\widehat h(a)\) for \(a\ne0\).
Every real zero-mass nonzero \(h\) becomes a difference of probability
masses after rescaling its positive and negative parts by their common
mass. The formula \(\|H'c\|_1=\max_s\langle (H')^\mathsf{T}s,c\rangle\)
and ordinary finite-dimensional norm duality therefore give
\[
 \Lambda_{6,p}
  =\frac{N^{1/p-1}}2\,
     \max_s \left(\sum_{a\ne0}|W(a)|^r\right)^{1/r}.
 \tag{1}
\]
Here the usual extrema apply at \(p=1,\infty\). This is the Walsh
duality from Martinevski's Lemma 2.1; the derivation also shows that
the maximum is attainable. For \(r\ge2\), Parseval bounds the
\(r\)-norm by \(N\), and a nonconstant affine character, with its
single nonzero coefficient \(N\), attains it. This proves the
formula for \(p\le2\).

From now on \(1\le r\le2\). Multiplication of \(s\) by any character
shifts Walsh frequencies and preserves full absolute values.
To maximize within a given spectrum, send one smallest absolute
coefficient to zero frequency and delete it. Conversely, any
puncturing loses at least that smallest contribution. This
explains precisely why we can optimize over punctured absolute
spectra. Below the objective is \(\sum k^r\) over the 63 retained
coordinates, where \(k=|W|/2\), unless an explicit alternative
normalization is stated. The factor \(2\) removed by this normalization
cancels the \(1/2\) in (1).

Set \(T=\{x:s(x)=-1\}\). At every frequency,
\[
 W(a)=64\,1_{a=0}-2\sum_{x\in T}\prod_{i=1}^6(1-2a_i x_i),
 \tag{2}
\]
so \(W(a)\equiv2|T|\pmod4\) for all \(a\).
Also \(\sum_a W(a)^2=4096\); hence the smallest absolute
value is at most 8, with equality only when all values have
modulus 8. The even-\(|T|\) case thus has minimum \(0,4,\) or 8
(only the flat, bent case for 8), while the odd-\(|T|\) case has
minimum 2 or 6. In particular our cases exhaust every Boolean sign.

### Two Walsh digit facts and a quadratic weight fact

1. If \(|T|\) is even, write \(w=W/4\) as a signed integer.
   Expanding (2) modulo 16 gives
   \(w(a)\equiv c+L(a)+2Q(a)\pmod4\), where \(c\in\mathbb Z\),
   \(L\) is integral linear in the frequency bits, and \(Q\)
   has integral coefficients and degree at most 2. Hence
   \(w\bmod2\) is affine. On the affine set where \(w\) is even,
   \(w/2\bmod2\) agrees with a Boolean polynomial of degree
   at most 2. To see this last assertion directly, write
   \(c=2c_1+c_0,\ L=\sum_i(2\ell_{i1}+\ell_{i0})a_i\) with
   \(c_0,\ell_{i0}\in\{0,1\}\). The high digit of \(c+L+2Q\)
   modulo 4 is
   \[
    c_1+\sum_i\ell_{i1}a_i+Q+
    c_0\sum_i\ell_{i0}a_i+
    \sum_{i<j}\ell_{i0}\ell_{j0}a_i a_j\pmod2.
   \]
   Indeed the carry from a sum of binary digits is the number
   of pairs of 1's modulo 2. This also applies to negative
   integer coefficients by the same decomposition into
   an even part and a bit.

2. If \(|T|\) is odd, write \(u=W/2\), a signed odd integer.
   In (2) the term \(32\,1_{a=0}\) vanishes modulo 8, giving
   \(u(a)\equiv c+2L(a)+4Q(a)\pmod8\) with odd \(c\),
   an integral linear \(L=\sum_i\ell_i a_i\), and integral \(Q\)
   of degree at most 2. The digit
   \[
    \chi(a)=\frac{u(a)^2-1}{8}\pmod2
   \]
   is Boolean quadratic (degree at most 2): \(u^2\bmod16\)
   depends only on \(u\bmod8\), and the expression is
   \[
     \frac{c^2-1}{8}
       + \frac{L^2+cL}{2}+cQ\pmod2.
   \]
   The diagonal coefficients of \(L^2+cL\) are
   \(\ell_i^2+c\ell_i\), which are even, and its mixed
   coefficients are \(2\ell_i\ell_j\). This proves the degree
   assertion and integrality. For \(k=|u|\), the digit is 0
   at \(k\equiv1,7\pmod8\), and 1 at \(k\equiv3,5\pmod8\).

3. On \(\mathbb F_2^d\) a Boolean function of degree at most 2
   that is not identically 1 has weight at most \(3\cdot2^{d-2}\)
   for \(d\ge2\). For clarity, its alternating polar form has
   rank \(2h\). Choose a basis of paired symplectic coordinates
   for this form and a basis of its radical; then its ANF
   is a sum of \(h\) disjoint binary products plus an affine
   term. A nonzero linear term on the radical makes it
   balanced, and otherwise completing each product gives
   weight \(2^{d-1}\pm2^{d-h-1}\) for \(h\ge1\). For rank zero
   the function is affine. This proves the bound, and when
   \(d=6\) the possible weights below 64 are contained in
   \(\{0,16,24,28,32,36,40,48\}\). In the rank-two case of
   weight 16 the completed product shows that its support is
   an affine 4-plane. Thus if \(\chi\) has weight 48, its
   zero set is an affine 4-plane.

## 2. Even \(|T|\)

We repeatedly use concavity of \(z\mapsto z^{r/2}\) for \(z\ge0\).
The extension of a secant through two points is an upper bound
outside the open segment between the two points, including the
endpoints. Every application below specifies why there are
no allowed interior points or bounds the zero point separately.

**Minimum 8.** All coefficients are flat, so the result is \(A\).

**Minimum 4.** For this paragraph put \(j=|W|/4\).
The affine digit \(w\bmod2\) has a 1, hence it has 32 or 64
ones. By Parseval, \(\sum j^2=256\); also
\[
 32\le\sum (j-2)^2=512-4\sum j .
\]
We removed a minimum \(j=1\), leaving 63 values, squared sum 255
and linear sum at most 119. The quadratic interpolation polynomial
\(P_r(j)\) for \(j^r\) at \(j=1,2,3\) majorizes \(j^r\) at every
positive integer: for \(j>3\) the usual third-derivative interpolation
remainder is nonpositive, since \(r(r-1)(r-2)\le0\); all other
allowed points are the interpolation nodes. The coefficient of the
linear term in \(P_r\) is \((8\cdot2^r-3\cdot3^r-5)/2\ge0\).
Indeed \(3(3/2)^r+5(1/2)^r\) is convex and at most 8 at both
endpoints \(r=1,2\). The interpolation sum is therefore at most
its value at the vector \(1^{19},2^{32},3^{12}\), which has exactly
the allowed length, energy and linear sum. Returning to units
\(|W|/2\) gives \(C\).

**Minimum 0, all coefficients divisible by 8.** Here use
\(j=|W|/8\), so \(\sum j^2=64\). The digit \(W/8\bmod2\)
is quadratic and is zero wherever \(W=0\), so it has weight
at most 48. In particular there are at most 48 values \(j=1\).
For \(j\ge2\), \(j^r\le 2^{r-2}j^2\). Thus the sum in these
units is at most \(48+16\cdot2^{r-2}\); deleting a zero has
no effect, and converting to \(|W|/2\) gives \(D\).

**Minimum 0, not all coefficients divisible by 8.** Use
\(j=|W|/4\) again. There are 32 odd \(j\) on one affine
half, and 32 even \(j\) on the other. Since at least one
\(j=0\) occurs on the even half, the quadratic digit
\(W/8\bmod2\) on that half has at most 24 ones. Thus at
most 24 entries have \(j\equiv2\pmod4\).
Let \(\alpha=(3^r-1)/8\). For odd \(j\), the secant at
squared values 1 and 9 bounds \(j^r\le1+\alpha(j^2-1)\).
For \(j\equiv2\pmod4\), the secant at squares 4 and 36 has
slope \(2^{r-2}\alpha\le\alpha\), so
\(j^r\le 2^r+\alpha(j^2-4)\).
For \(j\equiv0\pmod4\), either \(j=0\) or \(j\ge4\),
and \(j^r\le4^{r-2}j^2\le\alpha j^2\).
The final inequality is equivalent to
\(3^r-1-4^r/2\ge0\), checked below. Also \(2^r-4\alpha\ge0\):
the subadditivity of \(z^{r/2}\) gives \(3^r\le1+2\cdot2^r\).
Summing the three bounds and using \(\sum j^2=256\) yields
\[
 \sum j^r\le
 32(1-\alpha)+24(2^r-4\alpha)+256\alpha
       =16+24\cdot2^r+16\cdot3^r .
\]
This is at most \(48\cdot2^r+4\cdot4^r\), the \(D\) bound
in these units: the difference divided by 4 is
\(6\cdot2^r+4^r-4\cdot3^r-4\ge0\). Both scalar facts are
verified in Section 4.

## 3. Odd \(|T|\)

**Minimum 6.** Here all \(k=|W|/2\) are odd and at least 3;
the next allowed value is 5. After puncturing \(k=3\), the
energy is \(1024-9=1015\) on 63 positions. The secant at 9,
25 shows that the maximum is attained by \(3^{35},5^{28}\)
(which has that energy), proving \(B\) as an upper bound.

**Minimum 2.** All formulas in this subcase are in units
\(k=|W|/2\), and the punctured squared sum is 1023.
Let \(H_0,H_1\) be the zero and one sets of the quadratic
digit \(\chi\) in §1. Write \(m=|H_1|\). We puncture a value
\(k=1\) in \(H_0\); in particular \(m\le48\), and \(m<48\)
implies \(m\le40\). Set
\[
 \lambda=\frac{5^r-3^r}{16},\qquad
 \beta=3^r-1-8\lambda\ge0 .
\]
(The inequality follows from concavity of the two successive
secants at squares 1,9,25.) For positions of \(H_1\),
use \(k^r\le3^r+\lambda(k^2-9)\) from the secant at 9,25.
For \(H_0\) use
\(k^r\le1+\lambda(k^2-1)\), since its first two allowed
squares are 1 and 49 and the secant slope there is at most
\(\lambda\) by the scalar check below. Summed over all
positions these bounds give
\[
 \sum k^r \le 63+960\lambda+m\beta .
\]
At \(m=48\) this right side is \(V=15+12\cdot3^r+36\cdot5^r\).
Let
\[
 \delta_j=1+\lambda(j^2-1)-j^r.
\]
We show that one may subtract at least \(4\delta_7\) from \(V\);
this yields the single comparison profile
\[
 O=V-4\delta_7=11+24\cdot3^r+24\cdot5^r+4\cdot7^r.
 \tag{3}
\]

If \(m\le40\), the loss is at least \(8\beta\ge4\delta_7\)
(see §4). If a position of \(H_0\) has \(k\ge9\),
its secant slack is at least \(\delta_9\ge4\delta_7\).
Here \(\delta_j\) is nondecreasing for \(j\ge7\): concavity
in the squared variable makes the derivative at 49 at most
the secant slope from 1 to 49, which is at most \(\lambda\).
A position of \(H_1\) with \(k\ge11\) likewise has slack
\(\delta_k+\beta\ge\delta_9\).

It remains to treat \(m=48\), with only \(k=1,7\) on \(H_0\)
and \(k=3,5\) on \(H_1\), now before puncturing. We show
that at least four values \(k=7\) occur. By the weight fact,
\(H_0\) is an affine 4-plane. A character modulation places
its translate through zero; by choosing dual linear coordinates
we may write frequencies as \((a,b)\in\mathbb F_2^4\times
\mathbb F_2^2\), with \(H_0\) the plane \(b=0\).
For the corresponding time variables \(j,z\), set
\[
 v_b(j)=\tfrac12\sum_{z\in\mathbb F_2^2}s(j,z)(-1)^{b\cdot z},
 \qquad
 u(a,b)=\sum_j v_b(j)(-1)^{a\cdot j}.
\]
Then \(u=W/2\). For each \(j\), the four entries \(v_b(j)\)
are either all \(\pm1\), or one entry \(\pm2\) and three
zeros: they have a common parity, are bounded by 2, and
have squared sum 4 by four-point Parseval. Let \(J\) be
the set of \(j\) in the all-odd case. Since \(u(a,b)\) is odd,
\(|J|\) is odd. Translating the variable \(j\) by
\(\bigoplus_{j\in J}j\) preserves all moduli and makes the XOR
of the all-odd locations zero. Thus for each fixed \(b\),
\[
 u(a,b)\equiv \sum_j v_b(j)
          -2\sum_{a\cdot j=1}v_b(j)
       \equiv \sum_j v_b(j)\pmod4 ,
\]
since the parity of the inner sum is
\(a\cdot(\bigoplus_{j\in J}j)=0\).

For \(b\ne0\), given this constant residue modulo 4 and the
allowed signed values \(\pm3,\pm5\), the only possible values
are \(\varepsilon_b3,-\varepsilon_b5\), with a common choice
\(\varepsilon_b\in\{\pm1\}\) for that slice. If \(n_b\) is
the number of moduli 5 in the slice, inversion at \(j=0\)
gives \(v_b(0)=\varepsilon_b(3-n_b/2)\). Hence the total
number of 5's on \(H_1\) is
\[
 N_5=18-2\sum_{b\ne0}\varepsilon_bv_b(0)
          \le18+2\sum_{b\ne0}|v_b(0)|\le24.
\]
The last step is exactly the four-entry description above:
the sum over the three nonzero frequencies of a single
two-bit sign slice, normalized by 2, is at most 3.

If \(J_7\) is the number of moduli 7 on \(H_0\), full Parseval
gives \(16+48J_7+48\cdot9+16N_5=1024\). Therefore
\(N_5=36-3J_7\), so \(J_7\ge4\). All four or more high
entries remain after the puncture of a 1. They contribute
at least \(4\delta_7\) of slack, proving (3) also in the
last case. Section 4 verifies that \(O\) is strictly below
at least one of \(A,B,C,D\) at each \(r\).

## 4. Scalar inequalities and the continuous envelope

First, a nonzero sum of \(h\) real exponentials with distinct
bases has at most \(h-1\) real zeros, counted with multiplicities.
Divide by the smallest-base term and differentiate; this drops
the constant and the bound follows inductively by Rolle's
theorem (the finite-set version also rules out infinitely many zeros).

* \(3^r-1-4^r/2\) vanishes at 1,2, has positive derivative at
  1 (\(3^3>4^2\)), and has at most two zeros.
* \(6\cdot2^r+4^r-4\cdot3^r-4\) vanishes at 1,2. Its
  derivative at 2 is negative by \(2^{56}<3^{36}\); its eventual
  sign is positive, giving another zero above 2. With at most
  three real zeros it is positive on \((1,2)\).
* \(\lambda\ge(7^r-1)/48\) is equivalent to
  \(1-3\cdot3^r+3\cdot5^r-7^r\ge0\).
  The latter vanishes at 0,1,2, has positive derivative at 1
  by \(5^{15}>3^9 7^7\), and has at most three zeros.
* \(2\beta\ge\delta_7\) is equivalent to
  \(-3+6\cdot3^r-4\cdot5^r+7^r\ge0\).
  It vanishes at 0,2, has negative derivative at 2 by
  \(3^{54}7^{49}<5^{100}\), and is eventually positive,
  giving a third zero above 2. Thus it is positive in \((1,2)\).
* \(\delta_9-4\delta_7=-3+7\cdot3^r-7\cdot5^r+4\cdot7^r-9^r\)
  has values 2 and 0 at 1 and 2. Its second derivative is
  strictly negative throughout \([1,2]\) by the interval
  certificate below, so concavity proves the required sign.

For the first crossing, \( (B-A)/4^r =
35(3/4)^r+28(5/4)^r-63\) is strictly convex and vanishes
at \(r=0\). It is negative at 1 and positive at 2, so has
exactly one zero in \([1,2]\). The other comparisons use
the following rational interval certificates. Every inequality
listed holds on the entire closed interval, not just at endpoints:

| expression | interval | sign |
|---|---|---|
| second derivative of \(\delta_9-4\delta_7\) | \([1,2]\) | \(<0\) |
| \(C-B,\ D-C\) | \([1,9/5]\) | \(<0\) |
| first derivatives of \(C-B,\ D-C\) | \([9/5,2]\) | \(>0\) |
| \(A-O\) | \([1,189/100]\) | \(>0\) |
| \(B-O\) | \([189/100,191/100]\) | \(>0\) |
| \(C-O\) | \([191/100,3853/2000]\) | \(>0\) |
| \(D-O\) | \([3853/2000,2]\) | \(>0\) |

For reproduction, [verify_real_bounds.py](verify_real_bounds.py)
uses integer intervals scaled by \(2^{100}\), rounded outward.
For each integer base \(a\), \(z=(a-1)/(a+1)\), it bounds
\(\log a\) from below by the first 128 terms of
\(2\sum_{i\ge0}z^{2i+1}/(2i+1)\), and bounds the tail by
\(2z^{257}/(257(1-z^2))\). For nonnegative \(x\le8\)
the exponential is bounded by its Taylor polynomial through
degree 64 and the upper bound obtained by adding twice the
first omitted term. Products and division use floor for low
endpoints and ceiling for high ones. On a rational interval
\([l,h]\), all \(a^r\) lie between the directed bounds for
\(a^l,a^h\); derivative terms are the same bounds multiplied
by the appropriate powers of \(\log a\). Summing by coefficient
sign bounds the entire power sum over the interval. Bisection
only refines intervals whose current enclosure is inconclusive;
the accepted intervals cover each displayed domain. The
script also verifies the sign at both endpoints of the
rational crossing brackets \((1887,1888)/1000\),
\((1908,1909)/1000\), and \((1926,1927)/1000\), then shrinks
them for the decimal table. This closes the uniqueness and
ordering claims. Since each adjacent comparison switches
sign exactly once in that order, transitivity gives the
four-branch envelope.

## 5. Explicit extremizers

In binary coordinates take \(b(x)=x_1x_2+x_3x_4+x_5x_6\).
Its sign spectrum has constant modulus 8 and DC value \(+8\):
summing separately on each binary pair gives magnitude 2
and positive DC 2 for each pair. For the \(B,C,D\) branches
respectively, flip this sign on
\(\{0\}\), on \(\langle e_1\rangle\), or on
\(\langle e_1,e_3\rangle\). All three are linear subspaces
on which \(b\) is zero. Flipping on a subspace \(U\) changes
the spectrum by \(-2|U|1_{U^\perp}\). Thus the full modulus
multisets, in unscaled Walsh units, are
\[
 \begin{array}{c|l}
 A & 8^{64}\\
 B & 6^{36},10^{28}\\
 C & 4^{20},8^{32},12^{12}\\
 D & 0^{12},8^{48},16^{4}.
 \end{array}
\]
The multiplicities follow from the size of \(U^\perp\) and
Parseval; for example in the \(D\) case the 16 modified
frequencies have moduli 0 or 16, with squared sum
\(4096-48\cdot64=1024\), hence 4 of modulus 16.
The DC values are respectively 8,6,4,0, all minima,
so each punctured bound is attained. The four truth tables
and their spectra are also checked directly by
[verify_witnesses.py](verify_witnesses.py).

## References, scope, and reproduction

    python3 verify_real_bounds.py
    python3 verify_witnesses.py

The theorem addresses the **unrestricted probability-pair**
constant, not the subclass where \(Q\) is tied to the marginals
of \(P\). Martinevski's [October 2026 preprint](https://doi.org/10.5281/zenodo.23355709),
Lemma 2.1, Proposition 2.3 and Theorem 4.4, is the source of the
duality, the known small-\(p\) formula, the prior bent ray and the
one-flip obstruction. It explicitly leaves a six-bit interval
undetermined and does not establish the full envelope below \(p_0\).
The underlying Walsh catalogue is classical, and neither it nor the
one-flip branch is claimed as new. Searches through 2026-11-27 of the
title/DOI, six-bit exponent gap, and sharp punctured Sylvester Walsh
norm did not locate the four-branch result. This is not an absolute
priority claim.

As an optional independent finite sanity check, the witness script
accepts [Fuller's complete six-variable catalogue](https://booleanfunction.github.io/data/n6-classes.zip)
([description and attribution](https://booleanfunction.github.io/equivalence-classes.html);
[data DOI](https://doi.org/10.5281/zenodo.24217283)).
Its byte SHA-256 is
\(\texttt{6f1d7c7012d987d2d75a9618dd569959e66928d573c5f9b43db0b4276bcdecf8}\).
It confirms there are 2,082 distinct punctured absolute spectra
among the 150,357 representatives, and checks exact interval
separations at rational exponents typical of the four branches.
This optional check is not used anywhere in the proof.

    python3 verify_witnesses.py /path/to/n6-classes.zip
