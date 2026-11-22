# A true tagged Chen cofactor in each small-index multiplicative coset

Let \(N=2x\) be sufficiently large and even, \(L=\log x\), and
\(J=xJ_0\), where \(J_0\subset[1,4/3]\) is a fixed interval of
positive length. Use the ordinary Goldbach singular series
\(\mathfrak S(N)\). Let \(x^{.002}\le A\), \(2A\le x^{.006}\), and
let \(a\in[A,2A]\) be a genuine prime not dividing \(N\).
Put \(B_a=2x/a\), and fix \(C\ge 1\).

**Theorem.** For each such \(N,A\), all but \(o(A/L)\) of the
primes \(a\) are good simultaneously for every coset \(cH\)
of every subgroup \(H\subset\mathbb F_a^\times\) of index
\(1\le k\le L^C\). For each coset, the true weighted count
\[
 \sum_{\substack{av\in J,\ P=N-av\ {\rm prime}\\
         v\ {\rm squarefree},\ \Omega(v)\le2,\ P^-(v)>B_a^{1/10}\\
         v\bmod a\in cH}} \log P
 \ >\ .024\,\frac{|J|\mathfrak S(N)}{a k\log B_a}               \tag{1}
\]
holds. The exceptional fraction is uniform in \(N,A\) for
fixed \(C,J_0\). In particular a single good actual \(a\) has
both real Legendre signs among its usual prime-or-semiprime
cofactors, the same spatial window and the same normalization.
The mark \(a\) is the unique least prime of \(av\), and both
factors of a semiprime cofactor exceed \(B_a^{1/10}\). This
theorem does not assert either exact cofactor rank separately.
It estimates neither ordinary Liouville parity, nor the
rough-\(.265\) signed Goldbach sum whose support excludes \(a\).

## 1. Extract only primitive \(a^2\)-conductors

For \((h,aN)=1\), write \(q=a^2h\). Let \(\xi\) be any
nonprincipal multiplicative character mod \(a\), extended
by zero at zero. The actual weight on \(P\) is
\[
 W(P)=1_{P\equiv N\pmod{ah}}\xi((N-P)/a).
\]
On the unit fibre in \((\mathbb Z/q)^\times\), let
\(P=N-av\); \(v\equiv0\bmod h\) and \(v\bmod a\) runs
freely. For any character \(\psi\bmod q\), its restriction
to this fibre is a constant of unit modulus times an
additive character of \(v\bmod a\): the quotient by the
fixed \(a^2\)-component \(N\) is \(1-a\overline N v\bmod
a^2\); the \(h\)-component is fixed. Therefore the
unnormalized multiplicative Fourier coefficient
\(\sum_{u\bmod q}^{*} W(u)\overline{\psi(u)}\) is zero
if \(\psi\) is trivial on \(1+a\mathbb F_a\), and otherwise
has modulus \(\sqrt a\) by the ordinary Gauss sum.
In the latter case the primitive conductor of \(\psi\)
is divisible by \(a^2\). This is an exact extraction;
there is no low-conductor, principal, or exceptional
real-character contribution to this signed term.

Here are the resulting uniform exponents. Use
[Sedunova (2019), Proposition 1.3](https://www.numdam.org/article/JTNB_2019__31_3_635_0.pdf),
the maximal primitive Vaughan inequality with bound
\((x+Q^2\sqrt x+Qx^{13/14+\epsilon})(\log x)^2\) for the
\(q/\phi(q)\)-weighted sum of \(\max_{t\le2x}|\psi(t,\chi)|\);
a constant factor change from \(x\) to \(2x\) is harmless.
By dividing by each conductor's dyadic lower endpoint and
summing primitive conductors \(\ge R\), the induced-character
sum with weight \(1/\phi(q)\) over \(q\le Q\) costs
\[
                (x/R+Q\sqrt x+x^{13/14+\epsilon})L^{O(1)} .
\]
Indeed \(\phi(cj)\ge\phi(c)\phi(j)\) makes the sum over
inducing multiples \(O(L)\), and at each \(q\) the Euler
prime-power omissions cost at most \(O(L^2)\) after averaging
over its characters. Use this estimate with
\(R=A^2\), \(Q=4A^2(2x/A)^{.479}\).
The fibre estimate pays only \(\sqrt{2A}\) outside it,
uniformly in \(\xi,N\) and the two prefix endpoints.
Exposing \((a,h)\) from \(q\) and inserting any fixed
divisor-power in \(h\) cost at most \(x^{o(1)}\).
The three aggregate powers, for \(\tau=\log A/L\), are
bounded by
\[
   1-\tfrac32\tau,\qquad 13/14+\epsilon+\tfrac12\tau,\qquad
   \tfrac12+.479+(\tfrac52-.479)\tau .
\]
They are below \(.9975\) for \(.002\le\tau\le.006\) and
\(\epsilon=.001\). Replacing \(\Lambda(P)\) by its genuine
prime part even by the crude per-\((a,h)\) bound
\(O(\sqrt x L^2)\) has a fixed power saving after summation.
It follows that the sum over \(a\) and
\(h\le B_a^{.479}\) of the maximal absolute genuine-prime
signed discrepancies, including fixed divisor powers and
the supremum over \(\xi\), is \(O(x^{1-c_0})\) for an
absolute \(c_0>0\).

For the principal character mod \(a\), the literal count
for \(h\mid v\) and \(a\nmid v\) is the difference of the
progressions \(P\equiv N\bmod ah\) and \(P\equiv N\bmod
a^2h\). Ordinary maximal Bombieri–Vinogradov applies to
both: \(a^2 B_a^{.479}\ll x^{.489}\), and their combined
model on \(P\in N-J\) is exactly
\[
             |J|(1-1/a)/\phi(ah)=|J|/(a\phi(h)).
\]
Pass to fixed divisor-power errors by interpolation with
the trivial \(O(xL^{O(1)}/q)\) discrepancy at these
sub-root moduli and a reciprocal divisor moment. For the
coset, use the exact formula
\[
 1_{v\bmod a\in cH}=\frac1k\sum_{\xi|_H=1}
                         \overline{\xi(c)}\,\xi(v),
\]
including the principal character extended by zero.
The coefficients have \(\ell^1\)-norm one. Thus on a
common good set of marks, for every coset the true
progression count has model \(X_a/\phi(h)\), with
\(X_a=|J|/(a k)\), and total divisor-weighted remainder
\(O((x/a)L^{-D})\) for any required fixed \(D\).
For example the aggregate ordinary error \(O_E(xL^{-E})\)
and Markov at threshold \((x/a)L^{-D}\) discard
\(O_E(A L^{D-E})\) marks, and the signed bound is stronger.
Choose \(D>C+10\) and upgrade \(E\).
If \(h\) contains a prime of \(N\), no genuine central
prime \(P\) can belong to that row, so these primes are
omitted from the sieve.

## 2. A genuine switched source, preserving its coset

There is a second good set, losing \(x^{o(1)}\) marks
in each dyad, on which every nonprincipal \(\xi\bmod a\)
has arbitrary-log small prime prefixes in all polylog
progressions, for prime lengths at least \(x^{.099}\).
For clarity, take grid spacing \(R\exp(-10(\log\log x)^2)\)
on each dyad of length \(R\ge x^{.099}\), test progression
moduli up to \(\exp((\log\log x)^2)\), and set the
discrepancy threshold \(R\exp(-(\log\log x)^2)\).
Use the ordinary multiplicative large sieve (for example
Sedunova's displayed (1.2)) on the coefficient
\(1_{p\equiv b\bmod d}\log p\) in each prefix. Since
\(R\gg A^2\), the sum of squared character discrepancies
is \(O(R^2L^2)\). All test counts are subpower, so excluding
every bad primitive character on a prime tag \(a\) loses
\(x^{o(1)}\) marks. Between grid points use the trivial
integer count times \(\log x\). Removing primes dividing
any additional polynomial-sized integer (including \(N\))
costs only \(O(L)\) per prefix since the variable primes
are polynomially large. This gives the auxiliary-mask
Siegel–Walfisz condition with zero main term, and also its
usual reduced-unit discrepancy formulation. Partial
summation gives the unweighted prime version.

Set \(z=B_a^{1/10}\), \(w=B_a^{1/3}\). In the switched
triprime term use \(v=rst\) with actual primes
\(z<r<w\le s,t\), and weight \(1/2\) on the independent
ordered \((s,t)\). This represents each squarefree
adverse triprime exactly once, and admits half the
coincident \(s=t\) cases nonnegatively. Requiring
\(v\bmod a\in cH\) gives an **exact** combination of
independent coefficients \(1_{p\ {\rm prime}}\xi(p)\)
in the three slots via the preceding coset formula.
All slots exceed \(a\), so they are units at \(a\).
By [Maynard, Primes in arithmetic progressions to
large moduli I, published-version Lemma 8.9](https://ora.ox.ac.uk/objects/uuid%3A39a52f47-3770-4ddd-b7a2-b2a4f7300931/files/srj4305733),
group \(s,t\) as one coefficient, and use the genuine
prime \(r\)-slot as the SW coefficient. Both lengths
are polynomial, the product is \(\asymp x/a\), and the
twisted \(r\)-slot has SW by the preceding argument.
For the principal slot use ordinary prime SW.
The standard below-square-root bilinear theorem is also
[Polymath, Theorem 2.9](https://msp.org/ant/2014/8-9/ant-v8-n9-p03-s.pdf).
The estimate has the reduced-unit model and maximum
reduced residue, and applies through \(D'=x^{.495}\):
\(.495<(1-.006)/2\).

One can keep every true source and harmlessly enclose the
sharp interval \(v\in J/a\) by independent factor boxes:
use relative widths \(O(L^{-H_0})\), retain those meeting
the interval, and then every admitted product lies in
the actual interval enlarged by that relative amount.
The label windows at \(z,w\) remain intrinsic to their
own coefficient, and the ordering \(s,t\) was removed
exactly by symmetrization. The number of boxes is a
fixed log power. Their extra ordinary source mass is
\(o(|J|/(a\log B_a))\) by PNT and prime harmonics; the
nonprincipal source mass on each box is arbitrary-log
small after summing the other two labels with their
true positive majorants. Since \(1/k\ge L^{-C}\), the
boxes' combined coset source count is
\[
  (I+o(1))\frac{|J|}{a k\log B_a},\qquad
  I=\int_{1/10}^{1/3}\frac{\log(2-3u)}{u(1-u)}\,du.             \tag{2}
\]
Here the fixed relative interval for \(v\) is used; the
actual ordered-prime density follows by fixing \(r,s\),
using PNT for \(t\) in \(J/(ars)\) with \(t\ge s\), and
then prime harmonics in \(\log r/\log B_a,\log s/\log B_a\).
The integral over \(s\) between \(1/3\) and \((1-u)/2\)
equals \(\log(2-3u)/(1-u)\). Endpoint regions with
\(t=s\), or the product interval ending at \(s\), have
zero limiting angular measure. Equivalently one may
use the upper bound dropping \(t\ge s\) in the inner
\(t\)-interval after retaining the necessary upper
bound on \(s\), as in the prior tagged switch.
Only the upper (2) is needed.

Leave \(P=N-av\) to the upper linear sieve at
\(D'=x^{.495}\) and cutoff \(x^{.248}\).
Primes dividing \(Na\) may be omitted, after keeping
the real target units \((v,N)=1\); nonunit omissions
cost no true central prime rows (or at most \(O(L^2)\)
in the true weight). In the arithmetic distribution
of \(v\) the actual reduced class is \(N\overline a
\bmod d\) at every supported \(d\). The positive
actual coset coefficient permits the usual sieve
majorization. In the principal model the true
extra condition \((v,d)=1\) yields local densities
\(1_{p\nmid v}/(p-1)\) at primes \(p\nmid Na\).
Since \(v\) consists of three polynomial prime
factors, omitting these additional primes changes
the completed Euler factor by \(1+o(1)\) uniformly.
The upper is \((2/.495+o(1))\mathfrak S(N)/L\) per
source, since the sieve parameter is below 3.
Multiplying by the actual \(\log P=L+O(1)\) on \(N-J\)
gives the switched bound in the normalization of (1).
No product-prime BV with a free or unsigned replacement
of the coset has been used.

## 3. The same-target Chen inequality

Use the three-term Chen weight of
[the earlier same-cofactor switch](../chen_p2_cofactor/Proof.md),
with \(\vartheta=.479\), \(z=B_a^{1/10}\), \(w=B_a^{1/3}\).
Let \(T_0\) be the genuine rough coset prime-weight sum,
\(T_1\) its sum of the number of actual prime divisors
\(r\in(z,w)\), and \(T_2\) its sum on the special genuine
triprimes \(rst\) with \(r\in(z,w)\), \(w\le s\le t\).
On squarefree rough \(v\le(2/3)B_a<w^3\), every rank
at least 3 is removed by the half-charge on its two
small factors, or by one small factor and the exact
triprime charge. Rank at most 2 receives weight at
most one. On the rough set the nonsquarefree errors
are \(O(((x/a)/z+\sqrt{x/a})L^{O(1)})\) per mark by
opening the actual prime square; there are boundedly
many contributing prime divisors of \(v\). They are
negligible even relative to the coset main since
\(k\le L^C\). The mark \(a<z\) is unique.

Write \(\mathcal M_a=X_a\mathfrak S(N)/\log B_a\).
Apply Section 1 to \(T_0\) with the ordinary lower
linear sieve at \(B_a^\vartheta\), and to \(T_1\)
with upper-sieve level \(B_a^\vartheta/r\), conditioned
on the genuine \(r\mid v\). The physical moduli are
\(ah\) and \(a^2h\) with \(h=d\) or \(h=rd\), already
covered. The forced prime \(r>z\) does not overlap
the small sieve. The Goldbach Euler normalization
is \((1+o(1))e^{-\gamma}\mathfrak S(N)/\log z\) on the
same interval, since \(a\) and any deleted target
primes above \(z\) have negligible harmonic mass.
With the usual linear sieve \(f,F\), this gives
\[
 \begin{split}
 T_0/\mathcal M_a&\ge 10e^{-\gamma} f(10\vartheta)-o(1),\\
 T_1/(2\mathcal M_a)&\le
   5e^{-\gamma}\int_{.1}^{1/3}F(10(\vartheta-t))\,\frac{dt}{t}+o(1),\\
 T_2/(2\mathcal M_a)&\le I/.495+o(1).
 \end{split}
\]
The third line is Section 2 in this exact model.
The first two are the standard delay-function
integrals in the cited switch, stopped at the same
literal residual moduli, independently of the coset.
The reproduced [rational certificate](check.py) of
their difference minus \(I/.495\), also checking
all conductor powers, gives the strict lower
\(12806655181/500000000000>.0256>.024\).
This leaves a fixed margin for all errors.
Thus \(T_0-T_1/2-T_2/2\) proves (1).

[Shparlinski's Fermat-quotient prime estimate](https://doi.org/10.1017/S000497271000198X)
is an adjacent signed prime sum: with Fermat quotient
\(Q_a\), on \(P=N-av\) one has
\(Q_a(P)-Q_a(N)\equiv v\overline N\bmod a\).
His unrestricted prime sum does not keep the actual
progression \(P\equiv N\bmod ah\) and the marked
switched prime-product coset here. [Lu–Cai's Chen
theorem in progressions](https://www.sciengine.com/doi/pdf/03a08bd295a7445caf69b311ec916e9c)
concerns residue restrictions on the actual prime and
almost-prime endpoints. The present endpoint \(av\)
has a compulsory polynomial prime factor; the
coset constrains its **quotient** and preserves the
cofactor rank at most two. Ordinary unrestricted
Chen supplies neither this tag nor this same-target
coset selection. These comparisons are not priority
claims. The proof does not relate multiplicative
cosets to the ordinary odd/even factor count.
