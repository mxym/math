# Sharper rank-four and rank-five prices in the compensated half-zero comparison

Keep the fixed even target \(N\), the actual pairing, \(L=\log N\),
\(M=|J|N\mathfrak S(N)\), the half-zero quartic score \(H\), and all five
physical banks \(Q=R_3+R_4+R_5+W_1+W_2\) from the
[compensated comparison](CompensatedDebit.md). In particular \(R_4\)
is the full negative score on squarefree exact rank-four integers
all of whose prime factors exceed \(N^{.145}\).
Write \(\widetilde H=H+Q\), exactly as before.

**Theorem.** Uniformly through the even targets, the same compensated
comparison improves to
\[
 \langle H,H\rangle\ge\langle\widetilde H,\widetilde H\rangle-.584M+o(M),
 \qquad
 R_J\ge .416M+\langle\widetilde H,\widetilde H\rangle+o(M).             \tag{1}
\]
This supersedes the earlier numerical constants \(.693\) and \(.603\),
without changing any source support, prime rebate, or score.
It does not establish a sign on the remaining actual covariance.

## 1. Use all four literal labels in the positive receiver

Set \(a=.145\), \(c=.354\), and \(\theta=.499\). Let \(n\) be an actual
squarefree rank-four row in \(R_4\), and put \(u_i=\log p_i/L\)
for its four distinct prime factors. The target-angle sum is
\(\sum_i u_i=\log n/L\le 1\), and \(u_i>a\) for every \(i\).
Thus
\[
 \sum_{i=1}^4(c-u_i)_+\ge 4c-1>0.
\]
The exact quartic identity in [the half-zero theorem](Proof.md) and
AM--GM on the other three factors give, for **each** actual \(p_i\),
\[
 \frac{R_4(n)}L
  =144\left(\frac L{\log n}\right)^3\prod_{j=1}^4u_j
  \le (1+O_J(L^{-1}))\frac{144}{27}\,u_i(1-u_i)^3 .
\]
Multiply each of the four bounds by its own nonnegative
\((c-u_i)_+\), and sum. In particular,
\[
 \frac{R_4(n)}L\le
 (1+O_J(L^{-1}))\frac{144}{27(4c-1)}
      \sum_{\substack{p\mid n\\ N^a<p\le N^c\\p\ {\rm prime}}}
             \frac{\log p}{L}
            \left(1-\frac{\log p}{L}\right)^3
            \left(c-\frac{\log p}{L}\right).                       \tag{2}
\]
This is one pointwise majorization of the original row, not four
independent copies of a bound. It also puts no least-factor restriction
on the distinguished label.

For a true nonnegative compact prime-product source \(Z\) as in
[the existing positive receiver](CompensatedDebit.md#1-uniform-positive-receivers-for-the-three-exact-rough-ranks),
open each genuine \(p\) in (2), and upper-sift the actual quotient
\(n/p\) at exponent \(z(u)=\min(a,(\theta-u)/2)\), \(u=\log p/L\).
All three other primes exceed \(N^a\), so every actual occurrence in
(2) is retained by this sifting. The level on the quotient has
exponent \(\theta-u\), using slightly smaller fixed margins before
refinement. In the limiting parameter choice,
\(2\le(\theta-u)/z(u)\le(.499-.145)/.145<2.442\), so the same
\(sF(s)=2e^{\gamma_E}\) range applies throughout. The moduli are the
literal joined \(pd\), at level at most \(N^\theta\); divisor-bounded
multiplicity and true source product-BV are the same as in the
previous receiver construction. Retain the literal unit mask \(Nx\)
with \(x\) the source integer. Omission of \(p\) from the upper sieve
only enlarges its set and changes the conditional local product by
\(1+o(1)\); \(p\) is polynomially large. There is no opening of any
large free prime in the opposite quotient.

Writing \(M_Z=\mathfrak S(N)\sum_{x\in NJ,(x,N)=1}Z(x)\), the conditional
local weight including the true marked factor is therefore
\((1+o(1))\,2\mathfrak S(N)/(p(\theta-u)L)\), as in the old receiver.
The \(u\) in (2) cancels the \(1/u\) in the true prime harmonic
\(du/u\). Keeping the reflected interval and then refining fixed
angle cells gives, in either orientation,
\[
 \langle Z,R_4\rangle\le U_4^{\rm all} M_Z+o(M),
 \qquad
 U_4^{\rm all}=\frac{288}{27(4c-1)}
     \int_a^c(1-u)^3\,\frac{c-u}{\theta-u}\,du
       < .965 .                                                     \tag{3}
\]
The harmless \(O_J(L^{-1})\) in (2) is absorbed here since the same
positive receiver bounds the sum without it. The integrand in (3)
is decreasing: both \((1-u)^3\) and \((c-u)/(\theta-u)\) are
nonnegative and decreasing on this interval. A rational left Riemann
sum of mesh \(10^{-5}\) verifies the displayed upper.

## 2. Direct upper integration of the original rank-five score

Continue with \(a=.145\). The ordered own-log prime factor angles
\(a\le u_1\le\cdots\le u_5\) sum to one, so \(u_5\le1-4a=.42\).
In particular every singleton is below the half-root boundary.
Pairing each subset with its complement, the exact normalized
rank-five detector is
\[
 h_5(\mathbf u)=1-\sum_{i=1}^5P(u_i)
                        +\sum_{1\le i<j\le5}\psi(u_i+u_j),
 \qquad
 \psi(t)=\begin{cases}P(t),&t\le 1/2,\\-P(1-t),&t>1/2.\end{cases}
\]
The singletons have negative Möbius sign, and in a complementary
pair of a two-label and three-label set the latter has negative
sign. At equality the polynomial vanishes. Both \(P\) on
\([0,1/2]\) and \(\psi\) on \([0,1]\) are decreasing; here
\(P(t)=(1-2t)^2[7-3(1-2t)^2]/4\).
In the same ordered angular harmonic measure as before,
\[
 \frac{M_{R_5}}M
 \le
 \int_{\substack{a\le u_1\le\cdots\le u_5\\ u_1+\cdots+u_5=1}}
          \frac{[-h_5(\mathbf u)]_+}{u_1u_2u_3u_4u_5}
                                      \,du_1du_2du_3du_4+o(1).
\]
This is an ordinary upper bound from the actual prime factors,
not an estimate on their simultaneous reflected distribution.
There is no factorial with ordered angles.

Use units \(D=256000\), mesh \(h=275\), and endpoints
\(q_i=37120+h j_i\) for \(1\le i\le4\).
Keep exactly the box indices \(0\le j_1\le j_2\le j_3\le j_4\)
with \(j_1+j_2+j_3+2j_4\le256\): the inequality is necessary for
the true fifth angle to be at least the fourth. Use the lower
endpoint \(q_5=\max(q_4,D-\sum_{i\le4}q_i-4h)\).
All first-four pair arguments have upper endpoints
\(q_i+q_j+2h\); the upper for a pair containing the fifth
angle and \(i\le4\) is \(D-\sum_{j\le4,\,j\ne i}q_j\).
The sign and monotonicity just proved upper
\([-h_5]_+\) by using singleton lower and pair upper endpoints:
if \(S\) denotes its nonnegative upper numerator with
denominator \(4D^4\), the integrand times box volume is at most
\[
       \frac{S h^4}{4D^3\prod_{i=1}^5q_i\;\prod_\ell r_\ell!},
\]
where the \(r_\ell\) are the sizes of tied cells among the first
four labels. The factorials here refer only to box volume:
the equal-cell coordinates are ordered and the corresponding
fraction of the box volume is \(1/r_\ell!\). Any truncation by
the true fifth-angle boundary can only make that volume smaller.
The exact integer sum of upper endpoints, rounding each box
outward on the \(10^{-15}\) grid, gives
\[
                       m_5\le .006124352113757 < .006125 .
\]
The actual rank-five receiver \(U_5\) is unchanged.

## 3. Reassemble the original five banks once

Use the same masses \(m_i\), genuine prime rebates \(p_1,p_2\),
and positive receiver constants \(U_i\) as in
[the five-bank ledger](CompensatedDebit.md), except put \(U_{R_4}=.965\) and \(m_5=.006125\).
For every ordered pair the actual positive overlap still has bound
\(\min(m_i U_j,m_j U_i)M+o(M)\), by (3) in the applicable orientation
and the earlier estimates in all others. This includes the \(R_4\)
diagonal; it is not omitted, and no overlap is counted twice beyond
the ordered-pair expansion of \(\langle Q,Q\rangle\).
The exact previous covariance identity and signed linear transfers
give the debit
\[
 2\left(\sum_i m_i-p_1-p_2\right)
             +\sum_{i,j}\min(m_i U_j,m_j U_i)
   < .583718 < .584 .
\]
The [rational checker](check_allmark_rankfour_overlap.py) reproduces
(3), the direct rank-five integral upper, and the complete debit using the outward endpoints
of the earlier bounds. Both the residual and its small-factor/high-rank
issues are unchanged.
