# Exact linear-sieve factors on the same zero-tag self-pair

Keep the original sharp sextic, fixed even target, central interval,
normalization \(M=|J|N\mathfrak S(N)\), and precisely the original
physical score and chamber \(\mathcal Z_{.080}\) in
[the full zero-tag comparison](FullZeroTagAffineSelf.md).
The gate, both roughness tests, all cap and score conventions,
and the true unit restriction are unchanged.

**Proposition.** The complete signed sum on the same chamber obeys
\[
                      \sum_{\mathcal Z_{.080}}S(x)S(y)
                            >(2.091+o(1))M .
\]
This substitutes for the \(1.633M\) bound, improving it by
\(.458M\) on the identical support. The original \(R_J\)
term is not used again and no sign of the exterior is asserted.
In particular any already proved credit on the disjoint
[old tagged exterior](TaggedCreditOutsideZero.md) is unchanged.

## The entire genuine prime cross

Write \(a=.080\), \(V_0,H_0,\Pi,Q\) as in the
full zero-tag proof. Leave its original actual raw lower
\(\langle V_0,V_0\rangle>9.585M+o(M)\) and its original
\(Q,H_0\) costs of at most \(.016840M+o(M)\) per orientation
unchanged. Only the \(\Pi,V_0\) cross is strengthened.
All its previous physical progression estimates, its positive
affine \(q+dr=N\) estimate in which \(q\) is actually prime,
and its legitimate cellwise minimum of two upper bounds
remain exactly as in
[§3 of that proof](FullZeroTagAffineSelf.md#3-the-prime-terms-and-the-original-q-correction).

In those actual \(\Pi,V_0\) progression estimates do not
cap the sifting parameter at four. At each actual level
\(N^\Delta\) with \(\Delta=.499-s_+>0\) use
\[
 U_1(\Delta)=\frac{A(\Delta/a)}{\Delta},\qquad
 k_1(\Delta)=\frac{B(\Delta/a)}{\Delta},
 \quad
 A(u)=u e^{-\gamma}F_{\rm lin}(u),\quad
 B(u)=u e^{-\gamma}f_{\rm lin}(u).
\]
At the even unit atom \(d=1\) use \(\Delta=.499\).
As before \(U_1=2/\Delta\) when \(\Delta/a<1\)
is obtained by sifting fewer primes (to \(N^{\Delta/2}\));
\(k_1=0\) when \(\Delta/a\le2\).
For all other ratios these are the standard linear
sieve functions on the corresponding genuine ray.
Their delay equations (e.g.
[Franze–Kao, §4, (21)–(22) with \(g=1\)](https://arxiv.org/pdf/1812.11280))
in this normalization are
\[
 \begin{array}{ll}
 A(u)=2 &(0<u\le3),\\
 A'(u)= B(u-1)/(u-1) &(u>3),\\
 B(u)=0 &(0<u\le2),\\
 B'(u)= A(u-1)/(u-1) &(u>2).
 \end{array}
\]
In particular \(A,B\) are nonnegative and nondecreasing.
The attached checker bounds the integrals of their
derivatives by outward rectangles on \(u=j/800\).
On \([j/800,(j+1)/800]\), for example, the increment
of \(B\) is at least the lower bound for \(A((j-800)/800)\)
divided by \(j+1-800\), and at most the upper bound for
\(A((j+1-800)/800)\) divided by \(j-800\).
The identical rule with \(A,B\) interchanged holds
where \(A'\) is nonzero. Both bounds use already
available delayed entries. The actual levels
\(\Delta\) lie on the \(10^{-4}\) grid, and
\(a=.080\), so these are exactly the needed \(u\)'s,
through \(u=.499/.080\). There is no extrapolation
from ratios three through four.

The numerical rules for the actual upper are otherwise unchanged:
in each non-atomic \(s\)-cell with \(D=.499-s_+>0\)
use the smaller outward upper from
\(F(s)(U_1 E-k_1 O)\) and \(F(s)E C_2\);
if there is no genuine progression level, use only
the latter. Here \(E,O\) are the same ordinary
reciprocal *divisor* densities and \(C_2\) is the same
true prime-opposite affine Selberg upper. The signs
use a genuine lower on odd labels before subtraction.
The even atom uses the upper \(U_1(.499)<7.021589\).
The full signed upper is now \(<3.729964M+o(M)\)
in each orientation; reflection uses the equal-length
interval \(1-J\), not an assumption of symmetry of \(J\).

The original exact identity, dropping only the same
nonnegative terms, therefore gives
\[
 \sum_{\mathcal Z_{.080}}S(x)S(y)
 >\bigl(9.585-2(3.729964)-2(.016840)+o(1)\bigr)M
 >(2.091+o(1))M.
\]

Run:

    python3 -OB check_exact_linear_zero_tag.py

The [outward checker](check_exact_linear_zero_tag.py) locks the
original zero-tag arithmetic by hash, reuses its genuine
angular-density and affine-denominator enclosures, and
changes only the linear-delay input for the two prime crosses.
The new one-orientation upper is \(3.729963400140\ldots\).
