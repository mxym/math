# The whole negative-arm very-rough union for the half-zero detector

Keep the actual fixed-target notation \(N,L,J,M,\Pi,R_J\) and the
quartic polynomial \(P\) of [the uniformly removable half seam](Proof.md).
The detector in this note is **that** quartic half-zero detector, not
the compensated flat short receiver. On a central actual squarefree
integer write
\[
 H(n)=(\log n)\sum_{d\mid n}\mu(d)
               f_*(\log d/\log n)-\Pi(n),
       \qquad f_*(t)=P(t)1_{t<1/2}.
\]
Set \(H=0\) on nonsquarefree integers. The cited proof allows both
these replacements in the full pairing, so
\(\langle H,H\rangle=R_J-M+o(M)\).
All pairs are actual target units.

For \(a\in\{.132,.140,.145\}\) let \(\mathcal A_a\) consist of the rows
\(x+y=N,\ x\in NJ\) for which **at least one arm** has \(H(n)<0\)
and \(P^-(n)>N^a\). The other arm can have arbitrary least factor,
rank, or sign. Then at every sufficiently large even target,
\[
 \sum_{\substack{x\in NJ,\ (x,N)=1\\(x,N-x)\in\mathcal A_a}}
                  H(x)H(N-x)\ \ge -c_aM+o(M),
 \qquad
 (c_{.132},c_{.140},c_{.145})=(.970,.710,.585).                 \tag{1}
\]
Thus the complementary signed contribution is at most
\(R_J-(1-c_a)M+o(M)\). Any opposite-sign row in that complement
has an actual factor \(\le N^a\) on its negative arm. This is not
an absolute-value bound, or a bound requiring both arms to be rough:
the genuinely evaluated mixed correlations include all signs on the
arbitrary arm. No claim about the sign of that complement is made.

## 1. Rank five and seven, including the exact knot values

On a squarefree composite normalize \(H(n)\) by \(\log n\) and denote
the own angles by \(u_i=\log p_i/\log n\). The normalized score is the
alternating subset sum of
\[
         7(1/2-t)_+^2-12(1/2-t)_+^4,
\]
where \(z_+=\max(0,z)\). With all \(u_i>a>1/8\), the rank is at most
seven. Ranks two, four, and six respectively have signs \(+\), \(-\),
and zero by the even-rank formula in the cited proof. Rank three
is nonnegative if there is no giant factor. With a giant factor,
the negative magnitude, divided by \(\log n\), is
\[
 u_1u_2\{36(1-s)^2+12(u_1^2+u_2^2)-14\}_+,\qquad
 s=u_1+u_2<1/2.                                                 \tag{2}
\]
It is zero for \(s\ge .428\), since \(u_1^2+u_2^2\le s^2\) and the
resulting upper quadratic is nonpositive there. On this rough
floor the magnitude in (2) is \(\le7/16\): \(s\ge1/4\), the upper
bracket is decreasing up to half and is 7 at \(s=1/4\), and
\(u_1u_2\le1/16\).

For rank five let \(b_5\) be the density of the sum of five independent
uniforms on the centered intervals of lengths \(u_1,\ldots,u_5\).
This density is \(C^3\) even at repeated knots (for example, convolving
indicators gives the explicit truncated-power formula).
Five alternating finite differences and the distributional fifth
derivative of the displayed score give exactly
\[
          H_5=\left(\prod_{i=1}^5u_i\right)
                                \{14b_5''(0)-288b_5(0)\}.       \tag{3}
\]
Indeed the fifth derivative is
\(-14\delta_{1/2}''+288\delta_{1/2}\), and the alternating
finite difference has sign \((-1)^5\) times the integrated
derivative. The derivative is paired with the translated continuous
density and its continuous second derivative, so exact subset-angle
ties at half cause no convention issue.

Order \(u_1\le\cdots\le u_5\) and write \(g\) for the centered density
from the shortest three lengths. Differentiating the other two
uniform densities gives
\[
 b_5''(0)=\frac{2}{u_4u_5}
       \left\{g((u_4+u_5)/2)-g((u_5-u_4)/2)\right\}\le0.       \tag{4}
\]
Here \(g\) is even and nonincreasing on the nonnegative axis:
convolution preserves symmetric unimodality, as follows by writing
the densities as positive integrals of symmetric interval
indicators. Thus rank five is always nonpositive.

There is a useful pointwise bound sharper than applying the four
translated densities in (4) independently. Put \(s_3=u_1+u_2+u_3\le3/5\).
The unnormalized central slice of three intervals satisfies
\[
              u_1u_2u_3 g(0)\le s_3^2/12.
\]
If \(u_3\ge u_1+u_2\), the left side is \(u_1u_2\), at most \(s_3^2/16\).
Otherwise it is \(u_1u_2-(u_1+u_2-u_3)^2/4\), at most
\(u_3(2s_3-3u_3)/4\le s_3^2/12\). At
\((u_4+u_5)/2=(1-s_3)/2\), the same unnormalized slice is exactly
\((s_3-1/2)_+^2/2\): if inside its support the distance to the
edge is \(s_3-1/2\le1/10<\min_i u_i\). Thus (4) implies
\[
 -b_5''(0)\prod_i u_i
     \le2\{s_3^2/12-(s_3-1/2)_+^2/2\}\le1/20.                  \tag{5}
\]
The last expression is maximized at \(s_3=3/5\).

For \(b_5(0)\prod_i u_i\) take the largest length \(\ell=u_5\).
Integrating the four remaining intervals, the central-slice
condition removes two congruent simplex caps from their box.
Each excluded cap, at distance \(1/2-\ell\) from a corner, has
volume at least the simplex volume minus the sum of its four
single-coordinate truncations. Therefore, using \(\min_i u_i>1/8\)
and \(1/5\le\ell\le1/2\),
\[
 b_5(0)\prod_i u_i
  \le \left(\frac{1-\ell}{4}\right)^4
       -\frac{(1/2-\ell)^4-4(1/2-\ell-1/8)_+^4}{12}.
\]
The right side decreases on \([1/5,1/2]\). On
\([.22,.50]\) the inequality
\((1/2-\ell)^3/3\le(1-\ell)^3/64\) suffices for its derivative.
On \([.20,.22]\) its derivative is at most
\(-.78^3/64+.30^3/3-4(.28-.125)^3/3<0\).
Taking \(\ell=1/5\) and using (5) in (3) gives
\[
                    -H_5\le b_*:=16903/16000=1.0564375.         \tag{6}
\]

Rank seven has exactly the subsets of sizes at most three below the
half-angle, because every four factors exceed \(4a>1/2\).
Write \(s_j=\sum_i u_i^j\). Expanding \(P=1-t-11t^2+24t^3-12t^4\)
in those subset sums gives
\[
                H_7=10-78s_2+72s_2^2+48s_3-72s_4.
\]
For example the alternating subset sums of \(1,t,t^2,t^3,t^4\)
are respectively \(-20,-10,-4-6s_2,-1-9s_2,
6s_4-4s_3-6s_2^2-6s_2\), by counting the subsets containing the
indices of each monomial. Here \(\max u_i\le1/4\), \(s_2\le5/32\)
(by maximizing the convex sum over \(u_i\ge1/8\)), and \(s_3\ge1/49\).
It follows that
\[
 H_7\ge10-78(5/32)+72(5/32)^2+30/49=1145/6272>0.
\]
Thus among the very rough rows only genuine ranks three (with a
giant), four, and five can contribute a negative arm. Rank four
has magnitude \(\le144/4^4<b_*\), and (2) is smaller still.

## 2. A rigorous unopposed upper on those three negative weights

Put \(S(n)=[-H(n)]_+1_{P^-(n)>N^a}\). In either central interval
\(J\) or \(1-J\), the ordinary count satisfies
\[
       \mathfrak S(N)\!\sum_{\substack{n\in NJ\\(n,N)=1}} S(n)
                 \le (m(a)+o(1))M,\qquad
                 m=m_3+m_4+m_5.                                \tag{7}
\]
To justify the density used here, order the true prime slots to
avoid multiplicity, use reciprocal prime harmonics on all but the
largest, and use the ordinary PNT in the genuine last prime and
its actual fixed-relative spatial interval. On the compact
positive angular range every last-prime scale is polynomially
large. Finite box upper and lower approximations followed by
mesh refinement give density
\(du_1\cdots du_{j-1}/(j!\prod u_i)\) for symmetric labelled tests.
The weight \(\log n\) cancels the \(1/L\) scale of the prime-product
count; actual repeated prime rows are excluded, and the target
unit mask can only reduce a positive upper. Switching from
target-log to own-log coordinates uses an \(O_J(1/L)\) perturbation
on these compact domains. These are ordinary unopposed counts.

For (2) integrate in \(s=u_1+u_2\) and the smaller factor
\(u_1\in[a,s/2]\). Its two factors in the angular denominator
cancel. Monotonicity of \(u_1^2+(s-u_1)^2\) on that interval gives
\[
 m_3(a)=\int_{2a}^{.428}
       \frac{s/2-a}{1-s}
         \{36(1-s)^2+12(a^2+(s-a)^2)-14\}_+\,ds.               \tag{8}
\]
There is no factorial when using the ordered smaller factors and
the uniquely largest giant. Rank four gives exactly the positive upper
\(m_4(a)=(1-4a)^3\) because the four factors in the density cancel.
For rank five \(b_5(0)\le1/u_5\le5\); (4) also gives
\(-b_5''(0)\le 2/(u_3u_4u_5)\). The latter product is at least
\(.008\) for \(a\ge.132\). If \(u_3\ge.2\) this is immediate.
Otherwise \(u_3\in[a,.2]\); the sum of the two larger lengths
is \(\ge1-3u_3\), so their product is at least
\(u_3(1-4u_3)\). Minimize \(u_3^2(1-4u_3)\) on
\([a,.2]\) at an endpoint (its only interior stationary point is
a maximum), and \(a^2(1-4a)\ge.008\) for the displayed choices.
Thus (3), divided by the angular denominator, is at most 4940,
and we take
\[
                  m_5(a)=4940(1-5a)^4/(5!\,4!).                \tag{9}
\]

## 3. Genuine signed transfer and a genuine upper of the overlap

For every fixed \(a\) as above the exact actual source has
\[
 \langle S,H\rangle
  =\mathfrak S(N)\!\sum_{\substack{x\in NJ\\(x,N)=1}}S(x)
                  -\langle S,\Pi\rangle+o(M),                  \tag{10}
\]
with the reflected statement on \(1-J\). For the proof first pair
against \(V_{f_\delta}\) with its fixed strictly sub-root support,
as in the half-zero proof. The source is a finite collection of
actual prime-product ranks, with continuous bounded angular weight
on the compact positive floor. Work with labelled prime slots and
divide by their factorial: no near-equality of two angles needs
to be excluded. Independent boxes give a genuine prime coefficient
in any chosen slot (it need not be the largest), and an independent
divisor-bounded coefficient on the product of the others. Thus the
[true product Bombieri--Vinogradov estimate, §1](../nearfull_high_vaughan/WholeMarkPrimeTransfer.md)
applies at every fixed strict sub-root level. Repeated primes in
these separated boxes are supported on physical squares with prime
\(>N^a\), and have power-small cost after the true divisor weights
both in actual progressions and in the reduced reciprocals.
Keep the literal target-log prime floor in the box intervals;
replacing the remaining normalized angles by their own-log values
has \(O_J(1/L)\) coordinate error. The weight functions themselves
are continuous on this compact set (including their positive parts).
Uniform angle-box approximation therefore gives an error
\(\varepsilon L\) on an actual rough source; the half-zero positive
two-root bounds with a rough indicator on this arm give
\(O_a(\varepsilon M)\) paired error. For (11) below the same argument
uses the actual two-rough upper on the error source. The spatial
interval is retained by genuine prefixes. This is not a marginal
assumption on the sign of a reflected score.

The model for \(V_{f_\delta}\) at each actual source \(x\) has
the retained reduced mask \(Nx\). Its free Möbius zeroth moment
is zero and its first moment is \(-\mathfrak S(Nx)\).
Since \(f_\delta'(0)=-1\), the result is
\(\mathfrak S(Nx)(1+o(1))\), with the real spatial log kept.
All source primes are polynomially large, at bounded rank, so
\(\mathfrak S(Nx)/\mathfrak S(N)=1+o(1)\) uniformly.
Subtract the genuine \(\Pi\); it is not replaced by a model.
Finally the uniform weighted Fourier bound of the half-zero proof
pays the \(\delta\downarrow0\) transfer even against a true rough
indicator times \(L\). Likewise the own-log argument and the
squarefree deletion on the arbitrary arm are legitimate here:
for the latter, use the tiny-factor envelope on that arm with the
other a fixed rough indicator, then remove actual large squares;
for own logs use fixed-rank approximation and the weighted envelope
or the uniform bound
\(|\widehat f_*(\xi\log n/L)(\log n/L)|\ll (2+|\xi|)^{-3}\)
after changing the Fourier variable. This proves (10).

For the positive overlap use \(S(y)\le b_* L\,1_{P^-(y)>N^a}\).
The actual upper linear sieve for \(y=N-x\) on the genuine \(S\)
source, with level \(\theta=.499\) and \(z=N^a\), gives
\[
 \langle S,S\rangle
     \le \bigl(b_* A(a)m(a)+o(1)\bigr)M,\qquad
 A(a)=\frac{2}{\theta}\left(1+\frac{(\theta/a-3)^2}{4}\right).
                                                                    \tag{11}
\]
Here are the exact normalizers. For each true source \(x\), its
reduced local probability at a sifted prime \(p\) is \(1/(p-1)\)
if \(p\nmid Nx\), and zero if \(p\mid Nx\).
Product-BV at \(q\le N^\theta\), in the same genuine source boxes,
pays the weighted remainder with actual divisor multiplicity.
The sifting product at \(z\) is
\((1+o(1))e^{-\gamma_{\!E}}\mathfrak S(Nx)/(aL)\) uniformly;
all actual primes of \(x\) are already above \(z\), and the
target-prime tail is \(O(L/z)\). The upper sieve weights may
be evaluated separately at these exact reduced models, which
have the uniform dimension-one ratio bound: deleting an allowed
prime only decreases that ratio. For \(3<s=\theta/a<4\), the
[usual linear sieve formula](https://www.impan.pl/shop/publication/transaction/download/product/102606)
gives
\(sF(s)/(2e^{\gamma_{\!E}})
 =1+\int_3^s\log(t-2)/(t-1)\,dt
 \le1+(s-3)^2/4\).
This yields (11) with no independent simultaneous-prime
assumption. The only distribution input is for genuine source
products against the short sifted moduli.

## 4. Both orientations counted once

On the union in (1) the exact signed contribution is
\[
              -\langle S,H\rangle-\langle H,S\rangle
                             -\langle S,S\rangle .
\]
Indeed the first two terms count a row with two negative rough
arms twice, whereas its actual contribution is positive and
must be counted once. Equations (7), (10), (11), and the
nonnegativity of the two genuine prime cross terms bound this
expression below by \(-(2+b_*A(a))m(a)M+o(M)\).
The companion [exact rational check](check_debit.py) majorizes (8)
by endpoint rectangles of width \(10^{-4}\) (its first factor
increases and its bracket decreases), and gives respectively
\[
 (2+b_*A)m < .969196,\quad .708596,\quad .583570 .
\]
This proves (1). No signed comparison is asserted for the
unpaid physical rows where an adverse arm has a smaller factor.
