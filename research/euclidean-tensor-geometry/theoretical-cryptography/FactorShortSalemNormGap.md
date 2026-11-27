# A uniform gap and an effective residual degree bound for length-six Salem polynomials

Here the **length** of an integer polynomial is the sum of the absolute
values of its coefficients, not its degree or the size of its support.
A Salem polynomial means the minimal polynomial of a Salem number
multiplied by any product of cyclotomic factors, as in
[McKee–Smyth, Short Salem polynomials](https://arxiv.org/abs/2605.19013).
Write \(N\) for the full degree, \(D\) for the Salem number's degree,
and \(\tau>1\) for its exceptional root.

**Results for length six.**

1. Every such Salem number satisfies \(\tau>10011/10000=1.0011\).
2. A Salem polynomial of length six with \(\tau\le1.01\) has
   \(N<7200\). If the polynomial is already minimal, \(\tau>1.01\)
   in every degree.
3. Put \(\eta=3\sqrt3/4\). In all cases
   \[
        \eta^{D-2}\le 1024\,\tau^{7N}. \tag{1}
   \]
   The cyclotomic part, counted with multiplicity, satisfies
   \[
    N-D\le300+
        \max\{10\sqrt{32N},\,N/2+576\}. \tag{2}
   \]

McKee–Smyth list the length-six cases from \(1.01\) upward and mention
a much smaller uniform gap from a general few-term bound. The results
here narrow their low-value gap and reduce it to bounded full degree;
they do **not** assert that the remaining finite catalogue has been
searched, that every length-six Salem number is already known, or that
Lehmer's conjecture has been settled. The arithmetic main ingredients
besides the elementary arguments below are
[Mann's theorem on roots of unity](https://doi.org/10.1112/S0025579300005210)
and [Dimitrov's Schinzel–Zassenhaus theorem](https://annals.math.princeton.edu/articles/22975).

## Normalize the six signed monomials

A Salem polynomial is monic and reciprocal or antireciprocal. With
\(A=N/2\), after dividing by \(z^A\) its six terms may be written
\[
  (z^A\pm z^{-A})-(z^B\pm z^{-B})-(z^C\pm z^{-C}), \tag{3}
\]
where \(A>B\ge C\ge0\), and all three signs are plus in the reciprocal
case or minus in the antireciprocal case. In the latter case \(C>0\).
The half-integers \(A,B,C\) have the same fractional part, so the
unnormalized exponents are integers. We count repeated occurrences
when two terms at the same exponent have the same sign.

For the reciprocal case, at \(1\) the polynomial is negative if
\(1\) is not a root and zero otherwise, by pairing the nonreal
unit roots and using \((1-\tau)(1-1/\tau)<0\). Its two outer
coefficients are positive. If the total mass of positive interior
coefficients were nonzero it would be at least two: all interior
terms occur in equal pairs, and a center coefficient, if present,
is even because the length is even. This would give \(P(1)>0\).
Thus all interior terms are negative. For the antireciprocal case
the outer centered pair has the largest positive hyperbolic sine
for \(\tau>1\). To vanish there, both remaining pairs must be
subtracted. The equation at \(\tau\) also forces
\[
                     A<B+C \quad\text{in the antireciprocal case}, \tag{4}
\]
by the addition formula for the hyperbolic sine.
The gcd of the supported integer exponents is one, since a proper
power substitution would create more than one root outside the
unit disk. Hence
\[
             \gcd(2A,2B,2C)\le2, \tag{5}
\]
since a common divisor of these three integers divides twice every
original supported exponent.

## A small integer auxiliary polynomial on a hexagon

For \(x+y+z=0\), put \(u=(x^2+y^2+z^2)/2=-xy-xz-yz\) and \(v=xyz\).
For real \(x,y,z\in[-2,2]\), the exact maximum is
\[
        \max |v(u-2)(u-3)|=\rho:=\frac4{3\sqrt3}. \tag{6}
\]
Indeed \(0\le u\le4\), by considering the two entries of the same sign.
The real-root cubic \(X^3-uX-v\) gives
\(|v|\le2u^{3/2}/(3\sqrt3)\) by its discriminant. Its endpoint signs
at \(\pm2\) also give \(|v|\le8-2u\).
For \(0\le u\le3\), the square of the first bound times
\((u-2)^2(u-3)^2\) has nonzero stationary candidates only at
\(1,18/7\), from \(7u^2-25u+18=0\). Its maximum is \(16/27\),
at \(1\). For \(3\le u\le4\), writing \(s=u-3\), the second bound
gives \(2s(1-s^2)\le4/(3\sqrt3)\).
Equality is feasible; a direct witness in the first range is \((2/\sqrt3,-1/\sqrt3,-1/\sqrt3)\).

At a root of (3), take \(x,y,z\) to be its three signed pairs,
and use
\[
 Q=v(u-2)(u-3)\quad\text{in the reciprocal case},\qquad
 Q=v(u+2)(u+3)\quad\text{in the antireciprocal case}.
\]
For a unit root these pairs are real in the first case and purely
imaginary in the second. Multiplying the imaginary pairs by \(i\)
turns the second quantity into the first up to a unit complex
factor, so \(|Q|\le\rho\) in either case.
The square \(Q^2\) is an integer Laurent polynomial in the original
root even if the centered exponents are half-integers: changing the
choice of its square root changes the common sign of \(x,y,z\),
so \(Q^2\) is invariant. For an algebraic unit it is an algebraic integer.

Evaluating the three signed pairs at \(\tau\) gives \(x>0\),
\(y<0\), \(z<0\), and \(x=|y|+|z|\). Therefore
\(u\le x^2\) and \(|v|\le x^3/4\). In the reciprocal case \(x\ge4\)
and \(u\ge3x^2/4\ge12\), so \(Q\ne0\) and
\(|Q|\le x^7/4\le32\tau^{7A}\).
In the antireciprocal case all three pairs are nonzero and \(u>0\),
so again \(Q\ne0\), while \(x<\tau^A\) gives
\[
       |Q|\le (x^3/4)(x^2+2)(x^2+3)\le3\tau^{7A}.
\]
At \(\tau^{-1}\) the absolute value is the same.
Apply the absolute norm to \(Q^2\) in the field of the Salem number.
Its \(D-2\) unit conjugates contribute at most \(\rho^{2(D-2)}\).
The norm is a nonzero integer, so
\(1\le |Q(\tau)|^2\rho^{D-2}\), which proves (1).

## Root-of-unity multiplicity and the ten directions

Let \(\xi\) be a root of unity of order \(m\) at which the polynomial
vanishes. Label the six monomials by the formal vectors
\(\pm e_1,\pm e_2,\pm e_3\) for their centered exponent types, including
coincident exponents as separately labeled terms. If \(\nu_i,\nu_j\)
are the actual integer exponents for two labels, group them together
when \(\xi^{\nu_i-\nu_j}\) is a 30th root of unity. Mann's theorem applies to every irredundant vanishing
subsum of the integer-signed powers, so every class separately vanishes
and has size at least two. The same assertion for weighted derivative
terms holds whenever the derivative vanishes, since their coefficients
are rational and still have at most six terms.

Put \(q=m/\gcd(m,30)\) and \(\mathbf X=(2A,2B,2C)\).
For every equal-class formal difference, \(q\) divides the corresponding
actual exponent difference. A between-type edge thus implies
\(X_i\equiv\pm X_j\pmod{2q}\); a self-pair forces \(q\mid X_i\).
If the real span of the differences has rank three, every connected
component of these signed equations either has a self-pair or a
sign-inconsistent cycle. Otherwise the corresponding real equalities
would leave a free common absolute value on that component. A
sign-inconsistent cycle also forces \(q\mid X_i\), and the signed
congruences propagate this to all vertices. By (5), \(q\mid2\),
so \(m\mid60\).

If \(m\nmid60\), the differences have rank at most two. Choose a
nonzero vector in their common nullspace. Each class lies in a level
set of this vector on the six signed basis vectors. Since no level
may occur just once, the only possibilities up to scaling are:
* one zero coordinate and the other two equal in absolute value,
  for six possible directions; the classes are three pairs;
* all three absolute values equal and nonzero, for four directions;
  the classes are two triples.

In these cases the level sets themselves must be the classes, since
a pair or triple cannot split without a singleton. Each pair cancels
as opposite complex numbers, and its two actual exponents are distinct
(no cancellation was introduced between equal-exponent labels).
Each triple sums as a rotated equilateral triple of unit complex
numbers. It too has distinct exponent occurrences, since equal
exponents have the same coefficient sign. Weighting the terms by
their actual exponents cannot make the pair vanish, and makes the
triple vanish only if all three weights are equal. Thus the derivative
cannot vanish when \(m\nmid60\); all these roots are simple.
Among 60th roots the multiplicity is at most five by the Vandermonde
matrix on the distinct supported exponents for the derivatives
\((z\,d/dz)^j\). This gives at most \(300\) exceptional roots counted
with multiplicity.

## Counting the other roots

A pair direction with self-paired type \(i\) imposes one sign condition
on \(\xi^{2A_i}\) and one on \(\xi^{A_j\pm A_k}\), where
\((A_1,A_2,A_3)=(A,B,C)\). It contributes at most
\[
               g=\gcd(2A_i,\,A_j\pm A_k)
\]
solutions, by the cardinality of the common kernel of the two powers.
For a nonempty class \(g\le N/2\). To see this, if the difference of
the two remaining magnitudes is zero, those two terms have the same
coefficient sign and cannot cancel. Otherwise both exponents are
nonzero integers of absolute value at most \(N\).
For the self-pair of \(A\), the other exponent has modulus strictly
less than \(N\), so their gcd is at most \(N/2\). For the self-pair
of \(B\) or \(C\), a gcd greater than \(N/2\) would force
\(2B=A+C\) or \(2C=A+B\), respectively. The required signs conflict:
a reciprocal self-pair requires \(-1\), but the cross sum with the
leading type requires \(+1\); for antireciprocity the signs are reversed.

For a triple direction, normalize the leading sign of the direction
to \(+1\). One triple contains the term of centered exponent \(A\)
and one choice of each of \(\pm B,\pm C\). Its cancellation gives
two power conditions with positive exponents
\(b=A\pm B,\ c=A\pm C\), both strictly below \(N\); their values are
the two nontrivial cube roots with signs determined by the coefficients.
For each of the two orientations the common kernel has size
\(g=\gcd(b,c)\). Hence its contribution is at most \(2g\).
In a nonempty direction with \(b=c\), the tied terms would have the
same coefficient sign and coincide, which cannot give an equilateral
triple. Thus assume \(b\ne c\).
If \(g>N/4\), the coprime quotients \(b/g,c/g\) are among \(1,2,3\).
The order of \(\xi^g\) divides six by Bézout; neither quotient can
be \(3\) since both prescribed phases have order divisible by three.
Thus they are \(1,2\). In the reciprocal case the two prescribed
values are negative cube roots, but squaring the first gives a
positive-sign cube root, impossible. In the antireciprocal case the
smaller exponent \(g\) is less than \(A\), and \(2g>A\).
Then the equality has the form \(A+A_j=2(A-A_k)\), forcing
\(A=A_j+2A_k>B+C\), contrary to (4). Thus \(2g\le N/2\).

For distinct nonempty directions \(d,e\), the corresponding gcds
divide \(v\cdot\mathbf X\) for any integral vector normal to the
respective direction. This follows directly from the two defining
difference forms above. Also their common gcd is at most four:
modulo it, \(\mathbf X\) is a scalar multiple of each direction, so
a nonzero two-by-two minor of the directions, of modulus at most
two, kills each scalar, and then use (5). For one pair direction
and one triple direction there is a unit minor, giving bound two.

We next check that a primitive integer normal \(v\) common to
distinct **nonempty** directions has \(v\cdot\mathbf X\ne0\) when
\(A>B>C>0\). The ten directions give the following possibilities
for a vanishing normal in this ordered cone (the companion script
enumerates the 45 pairs). The entries in the last column are the
pair directions involved in the possible coincidences.

| Relation | Pair directions possibly involved |
|---|---|
| \(A=B+C\) | \((0,1,-1),(1,0,1),(1,1,0)\), two at a time |
| \(A=2B+C\) | \((1,0,1)\) with a triple |
| \(A=2B-C\) | \((1,0,-1)\) with a triple |
| \(A=B+2C\) | \((1,1,0)\) with a triple |

For \(A=B+C\), antireciprocity is excluded by (4).
In reciprocity each of the listed pair directions is empty:
its cross requirement is respectively
\(\xi^{B+C}=-1\), \(\xi^{A-C}=1\), or \(\xi^{A-B}=1\);
squaring contradicts the self-pair requirement.
For the other relations in reciprocity, the self-pair exponent
\(2B\) or \(2C\) equals the cross exponent, whose required sign
is opposite. In antireciprocity \(A=2B+C,A=B+2C\) violate (4);
in the case \(A=2B-C\) the paired cross exponent \(A+C=2B\)
must give \(-1\), while the self-pair must give \(+1\).
This proves the nonvanishing. If \(B=C\) or \(C=0\), a direct
application of the two gcd forms and (5) instead gives every
nonempty direction \(g\le2\): tied cross exponents with the
same sign cannot cancel; all remaining two defining exponents
force the gcd to divide the two free doubled magnitudes.
In the reciprocal case \(B=C=0\) the polynomial is
\(z^{2A}-4z^A+1\), and cannot be a Salem polynomial because either
\(A>1\) creates multiple outside roots or \(A=1\) has degree two.

In the strict cone the primitive normals to two triple directions
have \(\ell^1\)-norm at most two, and normals to any pair of directions
have norm at most four. These finite facts also follow by taking
cross products in the ten-element list. Therefore, from the common
nonzero integral linear form and the gcd bounds, two nonzero root
counts \(r_i,r_j\) satisfy \(r_i r_j\le32N\):
two triples cost at most \(4\cdot4\cdot2N\);
a pair and a triple at most \(2\cdot2\cdot4N\);
two pairs at most \(4\cdot4N\).
Together with \(r_i\le N/2\) and at most ten counts, this gives
\[
 \sum_i r_i\le \max\{10\sqrt{32N},N/2+576\}.
\]
Indeed, for \(r=\max r_i\le\sqrt{32N}\) use the first bound.
Otherwise use \(r+9(32N)/r\), whose maximum over
\([\sqrt{32N},N/2]\) is at an endpoint. The degeneracies
covered above have total at most forty, also below this bound.
Adding the 300 exceptional multiplicities proves (2).

## Explicit numerical consequences

All comparisons in this paragraph reduce to integer powers; the
companion verifies them with \(\eta>1299/1000\).
For \(N\ge7200\), the maximum in (2) is at most \(2N/3\),
so \(D\ge N/3-300\). Then
\((1299/1000)^{\lfloor N/3\rfloor-302}
  > 1024(101/100)^{7N}\):
check \(N=7200,7201,7202\) and increase by three using
\(1299/1000>(101/100)^{21}\). This proves the cutoff at \(1.01\).

For \(N\ge4200\), the maximum in (2) is at most \(7N/8\),
so \(D\ge N/8-300\). With \(b=10011/10000\), now
\((1299/1000)^{\lfloor N/8\rfloor-302}>1024 b^{7N}\)
by checking the eight starting residues and then increasing by
eight. If \(\tau\le b\), this forces \(N\le4199\). In that
range (1) rules out \(D\ge154\), since
\((1299/1000)^{152}>1024 b^{7\cdot4199}\). As \(D\) is even,
\(D\le152\). Dimitrov applied to the Salem minimal polynomial
gives \(\tau^{4D}\ge2\), contradicting \(b^{608}<2\).
This proves the uniform gap.

If the polynomial is minimal then \(D=N\). For \(N\ge40\),
(1) implies \(\tau>1.01\), starting at \(N=40\) and increasing
the exponent difference by one. For smaller \(N\), use
[Mossinghoff–Rhin–Wu's exact enumeration](https://doi.org/10.1080/10586458.2008.10128872),
which excludes such a measure. This proves the separate
minimal-length-six assertion.
