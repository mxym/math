# A sharper true rank-four receiver in the compensated half-zero comparison

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
 \langle H,H\rangle\ge\langle\widetilde H,\widetilde H\rangle-.603M+o(M),
 \qquad
 R_J\ge .397M+\langle\widetilde H,\widetilde H\rangle+o(M).             \tag{1}
\]
This supersedes the numerical constant \(.693\) in the earlier theorem,
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

## 2. Reassemble the original five banks once

Use the same masses \(m_i\), genuine prime rebates \(p_1,p_2\),
and positive receiver constants \(U_i\) as in
[the five-bank ledger](CompensatedDebit.md), except put \(U_{R_4}=.965\).
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
   < .602540 < .603 .
\]
The [rational checker](check_allmark_rankfour_overlap.py) reproduces
(3) and the complete numerical debit using the outward endpoints
of the earlier bounds. Both the residual and its small-factor/high-rank
issues are unchanged.
