# A disjoint both-negative block in the original sextic residual

Use the fixed even target \(N\), \(L=\log N\), the actual
central unit pairing \(x+y=N,\ x\in NJ,\ (x,N)=1\), and
\(M=|J|N\mathfrak S(N)\) as before. Use **exactly** the score
\(S=G_b+W\) from [the full medium cohort](FullMediumCohort.md),
with \(b=.003\), original \(H,Q\), and the same \(W\).
The [true positive-arm block](RoughPositiveCredit.md) \(\mathcal E\)
already removed consists of both actual ranks 2 or 3 with all
factors above \(N^{.150}\).

Here is an additional, disjoint physical set \(\mathcal F\).
On each of its two coordinates, the actual two least primes
are in distinct ordered target-log cells
\((i/500,(i+1)/500]\), \((j/500,(j+1)/500]\), with \(3\le i<j\).
Their lower endpoints have sum \(>.065\), upper endpoints have
sum \(\le .170\), and the second upper endpoint is \(<.110\).
The remaining factor is a true squarefree product of one,
two, or three distinct primes, all \(>N^{.110}\).
 
**Theorem.** On every \(\mathcal F\) row, both original compensated
scores are strictly negative, and this physical block has
\[
          \sum_{(x,y)\in \mathcal F}S(x)S(y)>.156M+o(M).
\]
Consequently, with \(\mathcal E\) and \(\mathcal F\) excluded once each
from the same actual pair sum,
\[
 R_J\ge .883M+
    \sum_{\substack{x+y=N,\ x\in NJ,\ (x,N)=1\\
                        (x,y)\notin\mathcal E\cup\mathcal F}}
             S(x)S(y)+o(M).                                      \tag{1}
\]
The term on the right retains its true signs; its sign is not
proved. This counts no prime pair or designated equality of the
completed ranks.

## 1. One common real ambient for each two-cell pair

Write \(a=.110,\ z=N^a,\ \theta=.499,\ \Delta=1/500\).
For one chosen two-tag cell \(i\), write \(u_i,v_i\)
for the upper endpoints, \(s_i=u_i+v_i\), and \(h=p_1p_2\)
for the two actual marks. Each tag must be a target unit.
For two prescribed cells \(i,j\), let the ambient consist of
all actual target-unit rows with their corresponding mark
products \(h,h'\) and both physical quotients \(r=x/h,\ r'=y/h'\)
having least factor \(>z\). These quotients need not have any
specific rank in the ambient. They make the marked primes
the two actual least primes, uniquely on each arm. Give every
ambient row the actual positive weight
\(t_1t_2t'_1t'_2\), where all four \(t\)'s are its marked
angles with denominator \(L\).

For the ambient upper, fix the actual marked products.
They are coprime, since the original row is a target-unit
row. The true primitive affine lattice is
\(h r+h'r'=N\) at length \(|J|N/(hh')+O(1)\).
At \(p\mid N\) the two forbidden roots coincide (including 2).
At \(p\mid hh'\) one affine slope vanishes and its constant
coordinate is nonzero by the target unit and coprimality
conditions, so exactly one root remains. All other primes have
two distinct roots. These are the genuine root counts on this
lattice, not a product model for the quotients.
Dropping its remaining target-unit mask only enlarges the upper.

Use the Selberg square at support
\(D_{ij}=N^{\theta(1-s_i-s_j)}\) in this lattice parameter.
The literal modulus is \([d,e]\); \(|\lambda_d|\le3^{\omega(d)}\)
and \(2^{\omega([d,e])}\) actual floors give the same
\(O(D_{ij}^2L^{10})\) error as in
[the positive-arm block](RoughPositiveCredit.md). Relative
to the true available length this is power-small, uniformly
for all marks in the cells, since \(1-s_i-s_j\ge.660\).
Thus the floors can be summed with their real tag weights
and \((hh')^{-1}\) harmonics.

Its normalized Selberg denominator has the same independent
Bernoulli variables used for the positive-arm block, except
that the one-root primes are now those of \(Nhh'\).
All the changes at \(p\mid Nhh'\) in its normalized log law
are \(o(1)\) uniformly, by the same small/large prime split
and \(Nhh'\le N^{O(1)}\).
The continuous limit is the same Dickman-2 distribution
with density \(e^{-2\gamma_E}\rho_2\). The chosen support
uses the fixed upper edges of the two cells, not a model for
the varying \(h,h'\). Its finitely many normalized cutoffs
are all continuity points of that law, uniformly over the
actual marks and target factors.
The exact Mertens normalizer has \(\mathfrak S(Nhh')=
(1+o(1))\mathfrak S(N)\) since the four tagged primes
are all polynomially large. So the actual weighted ambient
for these cells has upper
\[
 (C_{ij}+o(1))\Delta^4 M/L^2,\qquad
 C_{ij}=\left(a^2\int_0^{\theta(1-s_i-s_j)/a}
                        \rho_2(t)\,dt\right)^{-1}.               \tag{2}
\]
Indeed each true tag factor \(t\) cancels its own reciprocal
prime harmonic, giving \(\Delta\) per slot. Omitting tag
collisions in this upper is harmless; the actual fibers
are only those with distinct labels. Both observed marginals
below lie in this very same weighted ambient.

## 2. Actual reflected lower marginals, averaged only over the labels

For one prescribed cell \(i\), select a nonempty subset of
the three completed ranks 3, 4, 5 (quotient ranks 1, 2, 3).
Write \(m_i\) for its ordinary quotient coefficient per unit
two-tag area. The true prime-product angular density of each
quotient rank \(r\) is \(J_r(T/a)/T\), with
\(T=\log(x/h)/L=1-t_1-t_2+O_J(1/L)\), and \(J_r\) as in
[the genuine two-tag proof](../halfzero_detector/TwoLeastPrimeRebate.md).
With \(T_-=1-s_i\) and \(T_+=1-(u_i-\Delta)-(v_i-\Delta)\),
each such rank's ordinary coefficient is at least
\(J_r(T_-/a)/T_+\) in the limit, by nonnegativity and
monotonicity. The positive tag harmonic cancels \(t_1,t_2\);
the unweighted true source normalization with that tag
weight is \((m_i+o(1))\Delta^2 |J|N/L\).

Keep the opposite cell \(j\). Open its genuine \(h'\)
and lower-sift its true quotient with level \(N^{\theta-s_j}\)
and cut \(N^a\). Use true product BV on the actual selected
source \(x\) (the two true primes of its own cell times one
to three true quotient primes). The source is a finite-rank
angular product, as in [the original positive-arm block, §2](RoughPositiveCredit.md).
The actual moduli \(h'd\) do not exceed \(N^\theta\),
the residue is \(N\), and the reduced model retains the
actual source and target units \(Nx\).
After opening the opposite actual marks the conditional
root density on tested primes is \(1/(p-1)\) off \(Nxh'\),
and zero on the excluded primes. The external tag density
is \(1/\varphi(h')\); one omits the tagged primes from the
quotient sieve, with \(1+o(1)\) local cost.
Since all source factors are polynomially large and there
are at most five, their unit exclusions also give \(1+o(1)\)
in the local density. In summing the opposite tag harmonic,
any alternatives sharing one of these factors are absent
and cost \(o(1)\) of that fixed cell's harmonic. The unit
factor \(N\) stays in \(\mathfrak S(N)\).

The parameter \((\theta-s_j)/a\) is between 2 and 4,
so the true linear lower coefficient is
\[
       k_j=\frac{2}{\theta-s_j}
                 \log\left(\frac{\theta-s_j}{a}-1\right).
\]
The resulting genuine weighted marginal is at least
\((k_jm_i+o(1))\Delta^4M/L^2\), with the corresponding
reflection lower \((k_i m_j+o(1))\Delta^4M/L^2\).
These are aggregate counts over **both** specified tag cells,
not claims of BV for any fixed \(h,h'\).
Spatial intervals and own-log angles may first be put on
interior finite angle boxes and reflected intervals of the same
length; source and receiver log normalizations agree up to
\(O_J(1/L)\). The weights \(t_1t_2\) are genuine at the
physical tags; approximation by fixed cells does not detach
a label from its source. Actual squares of polynomial primes
remain power-small in the fixed-rank sources. In the receiver,
the sieve omitted the two named primes of \(h'\), so explicitly
delete all rows with either of these primes dividing \(r'\):
such a row has \(p^2\mid y\) for a genuine \(p>N^{.006}\).
The sum of true progression floors is
\(\sum_{N^{.006}<p\le\sqrt N}(N/p^2+1)
     =O(N^{1-.006}+N^{1/2})\).
Possible alternative tag products on either coordinate have
divisor-bounded multiplicity \(N^{o(1)}\) and bounded weights,
even without a receiver rank cutoff. Thus these extra rows are
\(o(M/L^2)\), and the lower marginal actually lies in the stated
rough ambient. That upper ambient may include other squares. Thus Fréchet in the shared weighted
ambient gives the lower
\[
       [k_jm_i+k_i m_j-C_{ij}]_+\Delta^4M/L^2+o(M/L^2)          \tag{3}
\]
for the actual intersection of the selected completed ranks.

## 3. Literal P6 negative sign and three amplitude layers

On each selected cell let \(T=T_-\), \(T'=T_+\),
\(q_0=(u_i-\Delta)^2+(v_i-\Delta)^2\).
Normalize the true negative score by \((\log n)t_1t_2\).
At rank 3 the single quotient prime is a giant, so the
normalized negative weight is at least
\[
 w_3=-\int_0^1\!\int_0^1 F''(u_i \alpha+v_i\beta)
                                 \,d\alpha\,d\beta-o(1).
\]
Indeed \(F''\) increases on \([0,.170]\):
\(F''''<0\) there and \(F'''(.170)>0\).
At rank 4 let
\(A_4=1680(q_0+T^2)-528,\ V_1=a(T-a),\ V_2=(T')^2/4\).
The exact even-rank formula gives lower
\[
       w_4=\min_{V\in\{V_1,V_2\}} V(A_4-3360V).
\]
In fact the two quotient angles have product in
\([V_1,V_2]+O_J(1/L)\), and the lower quadratic is concave.
The formulas are used only on true sorted distinct primes.

For rank 5 partition the largest of the three quotient angles
into tiles \([l,r]\) of width \(1/1000\) covering
\([T/3,T'-2a]\). The other two have total at least \(B=T-r\)
and their smaller angle is at least \(a\), also at least
\(T-2r\). Put \(v_*=\min(B/2,\max(a,T-2r))\).
Their true product is bounded below by \(v_*(B-v_*)-o(1)\);
for a fixed total the product increases with the smaller
angle up to half, and increasing the total increases this
lower bound. The sum of squares of the five angles is at
least \(q_*=q_0+l^2+B^2/2-o(1)\).
The same true sextic negative slice bound as before,
\(b_5(0)\le\sqrt{2/q}\), \(\mathbb E|Y_5|\ge\sqrt{q/24}\),
therefore gives the weight lower in this tile
\[
       (40320\sqrt{q_*/24}-1056\sqrt{2/q_*})\,l\,v_*(B-v_*).
\]
Use the minimum over the finite covering tiles for \(w_5\).
The coefficient is increasing in \(q_*\) and strictly positive
on the cells in use. The lower-angle and upper-angle
approximations all have only \(O_J(1/L)\) own-log changes.
The exact checker shows \(w_3,w_4,w_5>0\) on all 961 cells.
Thus these rows have the original \(H<0\) on both arms.
They are untouched by \(Q\) (a tag is \(<.110\)), the
.003 gate (each tag is \(>.006\)), and \(W\) (their tag sum
is \(>.065\)). Nor do they meet either arm of \(\mathcal E\).

Use three strict amplitude thresholds per cell, slightly
below the displayed certified lower weights for the three
ranks. Sort them increasingly; at each threshold select all
ranks with their lower weight at least that threshold.
Multiply the genuine weighted intersection (3) for each
two-threshold pair by the two increments of thresholds
above their preceding values (starting at zero). This is a
pointwise lower of the actual product of the two normalized
negative amplitudes; multiply back by the physical
\(\log x\log y=L^2(1+O_J(1/L))\).
The source and ambient upper are on the exact same row
weights for each comparison, with no independence asserted
for any two completed factors. Sum across distinct cell
pairs; physical uniqueness ensures no duplicate allocation.

The [rational checker](check_tagged_negative_credit.py)
uses the same outward monotone Dickman-2 interval recursion
as the positive-arm proof, at lower tiled endpoints of
the 101 actual ambient cutoff values. It uses lower
one-sided integration of \(J_r'\), lower logarithms,
outward square-root bounds, and the three strict amplitude
layers. The sum just described is \(>.156\) in units of \(M\).
These are all ordinary angular calculations or ambient
denominator enclosures; the interaction is the literal
fixed-target (2)--(3). The resulting positive true block
is disjoint from the positive-arm block, already counted
at .470. Removing both exactly once from the same
\(\langle S,S\rangle\) and using the previous .727
comparison proves (1).
