# A reciprocal seam in the actual giant-score double remainder

Use the exact even target, \(z,V,D,B,S,I,J,J_0\), \(Q_y(m)\), and
fully opened double remainder of [DoubleRough.md](DoubleRough.md).
Thus \(x=a f g\in NJ\), \(y=N-x=m c h k\), \(c h k\in I\),
and the signed coefficient is
\[
             \mu(a)\Lambda(f)\mu(c)\Lambda(h)Q_y(m)
\]
on the stated rough, unit and Vaughan-cutoff support. Write
\[
                P_0=a f,\qquad Q_0=m c h .
\]
**Claim.** For every fixed \(A>0\), the part on the literal rectangle
\[
         N^{.49}\le P_0\le N^{.51},\qquad
         N^{.49}\le Q_0\le N^{.51}                              \tag{1}
\]
is \(O_{A,J_0}(N L^{-A})\) at every prescribed even \(N\).
This includes genuine supercritical products \(P_0Q_0>N\),
so it is not the elementary two-free-coordinate region
\(P_0Q_0\le N/S^\epsilon\). The rest of the double
remainder is unbounded in sign by this result.

The arithmetic input is the same [Bettin--Chandee trilinear estimate,
Theorem 1](https://arxiv.org/pdf/1502.00769) used in the
[reciprocal seam for a tagged semiprime](../DoubleVaughanReciprocalSeam.md).
That earlier theorem operates on a separately tagged score. Here we
first show the necessary separation for the original, untagged
giant score with the moving short divisor cutoff, and also retain
the actual rough masks. We do not improve the underlying
trilinear bound.

## 1. Freeze only real gates, and pay their actual boundary

Split the central \(y\)-interval into \(O(L^F)\) cells of length
at most \(\Delta N\), with \(\Delta=L^{-F}\). Freeze \(T_y=y/B\)
and the two bounds for \(m\) from \(y/m\in I\) at an endpoint of
each cell; call the resulting literal cuts \(d<T\) and \(m\in
[M_-,M_+]\), with the original endpoint side conventions.
For the displaced \(d\) boundary, actual changed tuples have
\(d\mid y\), \(d\ll S\), \(|y-Bd|\ll\Delta N\). The number of
such \(y\) is at most
\(\sum_{d\ll S}O(\Delta N/d+1)\ll \Delta N L+S\).
For either displaced \(m\) boundary at an endpoint \(E\) of \(I\),
use \(m\mid y\), \(m\le\sqrt N\), \(|y-E m|\ll\Delta N\);
the count is \(O(\Delta N L+\sqrt N)\).
These counts are taken globally once per boundary, not repeated
over the mesh cells. The central margins imply \(m\le\sqrt N\)
both for the retained and the frozen rows, since
\(I\subset[\sqrt N S^2,B]\).

At each actual \(x\) all divisor choices of both sides, even
after opening \(Q_y\), have absolute weighted size
\(O(L^C\tau(x)^C\tau(N-x)^C)\) for an absolute constant \(C\).
Use Cauchy and the fixed divisor moments to make these mesh
errors \(O_A(N L^{-A})\) by choosing \(F\) large.
Also smooth the cell and central \(x\)-endpoints inside thinner
intervals of length \(NL^{-F'}\). With \(F'\) chosen larger
after \(F\), their union has at most
\(O(NL^{F-F'}+L^F)\) integers, so the same argument pays the
rounding, including an arbitrarily small original \(J\).
We now have a smooth factor \(\Psi(x/N)\) on each cell, with
each fixed derivative bounded by a fixed power of \(L\).
The actual short score there is \(Q_T(m)=\sum_{d\mid m,d<T}\mu(d)\).
No primality or equidistribution is used to pay these boundaries.

Keep the \(z\)-roughness masks on \(a,f,c,h\) individually.
On the free integers \(g,k\) open their actual roughness
by \(e_1\mid g,\ e_2\mid k\), on primes at most \(z\)
outside \(N\), using the Bonferroni depths of DoubleRough §1.
The positive errors can be bounded **before** opening
progressions: whenever one extra label \(e\) occurs, \(e\)
is an actual divisor of \(x\) or \(y\). By counting integer
multiples \(\le N\), their total event count is bounded
by \(O(N\sum_e1/e)\), with \(e\) of the first omitted
order. There is no \(+1\) per outer product at this stage.
The opposite truncated factors and possible repetitions
cost only fixed divisor powers on the physical \(x,y\),
so Cauchy with the factorial harmonic bound gives arbitrary
log savings for these errors, also after smoothing and
dyads. This is why the openings are legal even above (2)
of the preceding note, where a per-product floor error
would be too large.

For fixed \(e_1,e_2\), absorb the labels:
\(P'=P_0 e_1,\ Q'=Q_0 e_2,\ g'=g/e_1,\ k'=k/e_2\).
The equation is the exact
\[
              P'g'+Q'k'=N,\qquad (P'g',N)=1.
\]
On each independently dyadically supported pair of
\(P',Q'\) the weights are now separated:
\[
 \alpha(P')=\sum_{a f=P'/e_1}\mu(a)\Lambda(f),\qquad
 \beta(Q')=\sum_{m c h=Q'/e_2}\mu(c)\Lambda(h)Q_T(m)
\]
with all previously frozen and independent factor constraints in
their own sums. In particular (1) remains an independent
mask on \(P'/e_1,Q'/e_2\).
The factors \(P',Q'\) are target units; their mutual gcd
is one on any physical unit row and may therefore be
kept as an outer condition. The weights are divisor-bounded,
both in pointwise size and in mean square:
on dyadic scales \(M,P\), respectively,
\(\|\alpha\|_2\ll M^{1/2}L^C\),
\(\|\beta\|_2\ll P^{1/2}L^C\).
No logarithmic pointwise bound for the unrestricted \(m\)-sum
is needed.

## 2. Target units, Poisson and the exact zero term

At the physical equality expand
\(1_{(P'g',N)=1}=\sum_{u\mid(g',N)}\mu(u)\).
Since \(P',Q'\) are target units, every retained \(u\)
also divides \(k'\). Truncate \(u\le \exp(L^{3/4})\)
with arbitrary log accuracy before Poisson.
Indeed on \(u\mid x,y\) write \(x=u x_0,\ y=u y_0\);
the divisor-moment bound on \(x_0+y_0=N/u\) and
\(\tau(u x_0)\le\tau(u)\tau(x_0)\) give
\(O((N/u)\tau(u)^C L^C)\) total absolute weight.
The reciprocal divisor tail over squarefree \(u\mid N\)
is at most
\[
  e^{-\frac14 L^{3/4}}
       \prod_{\lambda\mid N}(1+C'/\lambda^{3/4})
     \le \exp(-c L^{3/4}).
\]
For the last bound split the target primes at \(L^2\):
the small integer reciprocal-power sum is \(O(L^{1/2})\),
and at most \(O(L)\) larger target primes give a bounded
contribution. The outer part has already been bounded by
fixed divisor powers, which include all rough-label
representations on the actual equation.

Write \(g'=u G,\ k'=u K\). At each unit,
coprime \(P',Q'\), the progression for \(G\) is
\[
      G\equiv (N/u)\overline{P'}\pmod {Q'} .
\]
The central support ensures both free coordinates are positive
in this parametrization, so positive-integer endpoints can
be extended to the whole progression. Poisson gives terms
\[
 \frac{N}{uP'Q'}\,\widehat\Psi\!
         \left(\frac{\nu N}{uP'Q'}\right)
       e_{Q'}\!\left(\nu(N/u)\overline{P'}\right),
           \qquad \nu\in\mathbb Z.                              \tag{2}
\]
This normalization follows by writing the smooth weight as
\(\Psi(uP'G/N)\); \(Q'\) is the progression modulus.

At \(\nu=0\), leave \(f,m,c,h,e_1,e_2,u\) fixed. The
\(\mu(a)/a\) in the \(1/(P'Q')\) factor is the true rough
harmonic on an interval, \(a>D\), with coprime restriction
\((a,N Q')=1\). The dyadic \(P'\)-support and (1) only
change its interval endpoints. All other gcd choices are
independent of \(a\). Use (3) of DoubleRough to pay this
zero term. Its remaining factors are summed with their
actual reciprocal weights, giving fixed log powers,
including \(\sum_{e_1,e_2}1/(e_1e_2)\) and
\(\sum_{u\mid N}1/u\). In particular we do **not** pay the
zero mode by multiplying an arbitrary-log saving by the
whole \(S^{o(1)}\) label count.

## 3. Nonzero reciprocal sums

For fixed presieve labels, unit divisor and dyadic scales
\(P'\asymp M,\ Q'\asymp P\), put
\(g_0=\log_N(MP)\) and \(m_0=\log_N\max(M,P)\).
Because the added labels are subpower and the starting box
is (1), each scale exponent eventually lies in
\([.489,.511]\). By rapid Fourier decay,
\(|\nu|>N^\rho(1+MP/N)\) costs an arbitrarily strong
power saving for any sufficiently small fixed \(\rho>0\):
the cut \(u\le \exp(L^{3/4})=N^{o(1)}\) is smaller than
the fixed-power reserve. Derivative constants of \(\Psi\)
only cost log powers.

On a signed dyad \(|\nu|\asymp T_1\), smoothly separate
\(\widehat\Psi(\nu N/(uP'Q'))\) by Mellin inversion in
\((|\nu|/T_1)(M/P')(P/Q')\) on its compact normalized
interval. At each retained scale the transform has uniformly
log-bounded \(L^1\)-norm: fixed derivatives of the rescaled
Fourier function are bounded by fixed log powers using rapid
Fourier decay, and two integrations by parts suffice for
Mellin integrability. The factors \(1/P',1/Q'\) in (2)
can be separated at their actual dyadic scales. The coefficient
norms then cost \((T_1MP)^{1/2}L^C\). Bettin--Chandee
Theorem 1 applies with phase multiplier \(N/u\),
summation modulus \(Q'\), and reciprocal of \(P'\);
its factor
\((1+(N/u)T_1/(MP))^{1/2}\) is at most
\(N^{(\max(0,1-g_0)+\rho)/2+o(1)}\).
Restoring the factor \(N/(uMP)\) of (2), the two
exponents relative to \(N/u\), apart from arbitrarily
small fixed losses, are bounded by
\[
 \begin{array}{ll}
 .7 g_0+.25m_0-.85,\quad .875g_0+.125m_0-1,
                                  &g_0\ge1,\\[2pt]
 .5-.65g_0+.25m_0,\quad .5-.625g_0+.125m_0,
                                  &g_0<1 .
 \end{array}                                                       \tag{3}
\]
For instance insert \(T_1\le
N^{\max(0,g_0-1)+\rho+o(1)}\)
in the two terms (1.2) of the cited theorem, multiply by
\((T_1 M P)^{1/2}/(MP)\), and include the displayed
phase factor; this gives (3) in each branch.
For \(g_0\ge1\) use \(g_0\le1.022,\ m_0\le.511\);
the first exponent is at most \(-.00685\) and
the second at most \(-.041875\).
For \(g_0<1\) use \(g_0\ge.978,\ m_0\le.511\):
the respective upper bounds are \(-.00795\) and
\(-.047375\). Choose \(\rho\) and the analytic epsilon
small enough to retain a fixed power saving.
All presieve label counts, truncated unit divisor counts
and mesh/dyadic costs are \(N^{o(1)}\); even their absolute
counts preserve the fixed power saving for these nonzero
terms. Together with the separate zero-mode argument,
this proves (1).

The estimate can be used with the elementary deletion
from DoubleRough without double counting: either keep
the two scopes separate, or subtract their already
paid intersection, for which (1) simply adds two
intervals to the CRT and short-harmonic proof.
This leaves actual imbalanced and/or larger-product
boxes of the original giant score, not a one-sided
bound or a binary representation theorem.
