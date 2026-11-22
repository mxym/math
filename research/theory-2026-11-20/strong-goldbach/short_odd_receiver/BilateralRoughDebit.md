# A bilateral very-rough debit cap, including the actual seams

We use the summands \(H\) in
[the exact short odd-receiver identity](Proof.md), with the same
\(\lambda=.0001,\ U=N^\lambda,\ v=.498,\ \rho=.999\) and \(k=(1-\lambda)^{-1}\).
In addition choose the fixed low cutoff cap \(\chi\) so that \(\chi\leq\psi\).
For example, the original \(\chi\) can be one through \(.4985\) and zero
from \(.4988\); this respects every hypothesis of the preceding identity.
We require no monotonicity of the two caps. The profile \(F(t)=(1+kt)C(t)\)
has \(0\leq C\leq1\), is affine through \(.4992\), and is zero from \(.4996\).

Let \(N\) be an individual even target, \(L=\log N\),
\(J\Subset(0,1)\) a fixed nondegenerate interval, \(x\in NJ\), \(y=N-x\), and
\(M=|J|N\mathfrak S(N)\), with the ordinary binary singular series.
Every summation below is on the actual target units \((x,N)=1\).
Put \([z]_-=\max(0,-z)\).

**Theorem.** As \(N\) tends to infinity through even integers,
\[
 \frac1M
 \sum_{\substack{x\in NJ,\ (x,N)=1\\P^-(x),P^-(y)>N^a}}
                 [H(x)H(y)]_-
 \ \leq\ C_a+o(1),
 \qquad
 C_{.145}=.933,\quad C_{.150}=.645.                         \tag{1}
\]
Here \(P^-(n)\) is the least actual prime factor. These bounds cover the
whole indicated physical sector, including all its actual near-half
subset seams, both signs on each arm, and both orientations.
They do not bound the contribution of rows where **either** least
factor is \(\leq N^{.145}\), and give no global covariance or binary
Goldbach lower bound. In particular no signed credit from the earlier
\(T\)-scores is used.

## 1. Literal coefficients and pointwise sign envelopes

On this sector any integer has at most six factors counted with
multiplicity since \(7a>1\). A row with a repeated prime incurs only
\(O_J(L^2)\) weight: there are boundedly many divisor choices, and all
profiles and normalized log weights are bounded. The actual repeated
prime is \(>N^a\), so such rows cost
\(O_J(L^2N\sum_{j>N^a}j^{-2})=o(M)\) in both orientations.
A central genuine prime has \(H=0\). Work henceforth on squarefree
composites with two through six distinct factors.

For a fixed central \(n\), write \(\theta_p=\log p/L\),
\(u=\log n/L=1-\kappa\), where \(\kappa=O_J(1/L)\); write its own angles
\(\xi_p=\theta_p/u\), which sum to one. They all exceed \(a\).
For any subset \(A\) of its factors let \(t=\sum_{p\in A}\xi_p\) and
\(s_2=\sum_{p\in A}\xi_p^2\).
Expand \(H/L\) as a true signed sum of subset coefficients as follows.
In \(P_F\) the coefficient for its actual divisor is
\((u-\sum_{p\in A}\theta_p)F(\kappa+\sum_{p\in A}\theta_p)\),
since all factors outside the divisor are eligible marks (\(p>U\)).
In \(-B\) collect terms by their actual \(rd\), with \(r\in A\); the
change in the Möbius sign when \(r\) is removed gives the plus sign
in the coefficient. In \(-C_\psi\) the coefficient is
\(-k\psi(\sum_{p\in A}\theta_p)(\sum_{p\in A}\theta_p-\sum_{p\in A}\theta_p^2)\).
Here the squarefree indicator in \(C_\psi\) is exactly one.

In smooth coefficients we may use \(t,s_2\) at a cost \(O_J(L^{-1})\)
for \(H/L\), keeping the **literal** hard mark gate
\(r\leq N^v\). For \(|A|\geq2\), whenever the \(B\)-coefficient is nonzero,
all its possible constituent marks pass this gate: each has target
angle at most \(.499-a<v\). Every \(F\)-argument in that coefficient
lies in its affine part. Thus the normalized unsigned coefficient is
\[
 b_A=(1-t)F(t)+\chi(t)\{t(1+kt)-ks_2\}
                           -k\psi(t)(t-s_2)                  \tag{2}
\]
for \(|A|\geq2\), up to the indicated uniform error in the final sum.
The singleton formula instead uses a \(B\)-coefficient
\(t\,1_{\theta_p\leq v}\); wherever this indicator is one,
the true cap \(\chi(\theta_p)=1\). The empty coefficient is \(1\).
Consequently
\[
                  H(n)/L=\sum_A(-1)^{|A|}b_A+O_J(L^{-1}).     \tag{3}
\]

All these coefficients lie in \([0,1]\), vanish for \(t\geq .4996\),
and equal one if \(t\leq v\) (then \(\theta_p=ut\leq v\) also for
a singleton). To check the bounds, within the support of \(\psi\),
\(F(t)=1+kt\) and the lower bound from omitting the nonnegative
\(B\)-term is
\(1-t-kt^2+ks_2\geq0\). If \(\psi(t)=0\), the \(B\) term vanishes
too. For \(|A|\geq2\) and \(t>v\), use \(\chi\leq\psi\) to bound
the correction in (2) above by \(\chi(t)t(1-k+kt)\). On its support
\(F\) is affine, so adding this bound gives at most one. Outside
that support \((1-t)F(t)\leq1\) for \(t>v\).
For singletons, an ineligible mark only removes the nonnegative
\(B\)-term; its remaining lower bound on the \(\psi\) support is
\(1-t\). An eligible singleton with \(t>v\) has \(t=v+O_J(1/L)\),
so lies in the common fixed plateaux of both caps (and the affine
part of \(F\)). Its coefficient in (3) is exactly one.
Each complementary pair of subsets has at most one nonzero
coefficient, because their own angles sum to one.
In the rest of this section all signs and bounds refer to the
main sum in (3), with its \(O_J(L^{-1})\) error restored in §3.

Put \(w=1-2v=.004\). The following real angular envelopes suffice.

* **Rank two.** The sum is nonnegative and at most \(1\).
  It is zero unless the smaller factor's own angle is in
  \([v,1/2]\).
* **Rank three.** The sum is in \([-2,0]\). If the largest factor
  has angle at most \(v\), all singles are fully included and
  all pairs are above the support. Otherwise the two small
  singletons are fully included; the large singleton and their
  pair are complementary, contributing a difference of magnitude
  at most one. Pairs containing the large label are above support.
* **Rank four, largest angle at most \(v\).** The sum is in
  \([-3,0]\), with the initial \(1-4\), no triples, and
  three complementary pair slots. It is at least \(-2\) unless
  all three slots have their smaller sum in \((v,1/2]\).
  Denote this exceptional simultaneous collar by \({\cal E}_4\).
  If the largest factor has angle \(t>v\), the other three
  singletons and all their pairs are fully included: their
  pair angles are at most \(1-v-a<v\).
  No subset containing the largest label and another label
  contributes. The sum is \(1-b_{\rm large}-b_{\rm small\ triple}\),
  in \([0,1]\) by complementarity. It vanishes unless
  the largest angle is in \((v,1-v)\), since otherwise
  the small triple is fully included.
* **Rank five.** All singles are fully included (largest
  \(\leq1-4a<v\)); all quadruples are above support.
  Pair/triple complement slots contribute between \(-1\) and one.
  A pair of angle \(\leq v\) contributes one. Any two pairs
  of angle \(>v\) must intersect, since \(2v+a>1\).
  A pairwise-intersecting family of edges on five vertices has
  at most four edges: either all meet at a common vertex, or
  they are contained in a triangle. Thus the sum is between
  \(1-5+6-4=-2\) and \(1-5+10=6\).
* **Rank six.** Every single and pair is fully included, and
  every quadruple is above support (largest pair \(\leq1-4a<v\)).
  In each of the ten complementary triple slots, the combined
  unsigned coefficient is in \([0,1]\), and is one if its
  smaller angle is \(\leq v\). The initial \(1-6+15=10\)
  is therefore reduced to a nonnegative sum, bounded above
  by the number of triple slots with sums in \((v,1-v)\).

In particular define the nonnegative majorant \(p(n)\) by
the rank-two or the large-rank-four collar indicator above,
by \(6\) on rank five, and by the number of the indicated
triple slots on rank six; set it to zero on the other ranks.
Let \(e(n)=1_{{\cal E}_4}(n)\). These are literal angular tests
on actual prime products. The normalized positive part is
at most \(p(n)+O_J(1/L)\), with \(p(n)\leq10\). The normalized
negative part is at most \(2+e(n)+O_J(1/L)\).

## 2. Unopposed angular masses and exact constants

For the squarefree rank \(j\) source with all own angles \(\geq a\),
the ordinary unopposed \(L\)-weighted angular density relative
to \(|J|N\) is
\[
     \frac{dt_1\cdots dt_{j-1}}{j!\,t_1\cdots t_j},\qquad
                    t_j=1-\sum_{i<j}t_i .                   \tag{4}
\]
This is the form for symmetric tests on labelled angles. Equivalently,
omit the factorial and order the angles. Fix the \(j-1\) smaller
actual primes in an ordered source; the largest prime on a fixed
angular/spatial box is counted by the PNT at scale
\(N/\prod_{i<j}p_i\geq N^{a+o(1)}\).
Each of the remaining primes has its actual reciprocal PNT measure
\(dt_i/t_i\) on compact positive angles. Approximating the indicated
angular tests by a finite box mesh and taking its refinement after
\(N\to\infty\) gives (4). The walls have measure zero, since proper
nonempty subset angles are nonconstant linear forms and the
denominator on the compact simplex is bounded below. Squarefree and
target-unit exclusions can only reduce these positive unopposed
upper bounds. The actual threshold \(P^->N^a\) implies the own-angle
lower bound used here, so its upper mesh remains valid.

The following constants bound the indicated integrals:
\[
\begin{split}
 I_2&=\log((1-v)/v),\\
 I_{4,+}&=\frac{w(1-v-3a)^2}{12v a^2(v-2a)},\qquad
 I_{4,{\rm ex}}=\frac{w^3}{48a^4},\\
 I_5&=\frac{(1-5a)^4}{2880a^5}
 \left(\frac{5/6}{1+c+(2/5)c^2}+\frac{1/6}{1+c}\right),
                         \quad c=(1-5a)/a,\\
 I_{6,+}&=\frac{10}{720}\frac{w(1-v-3a)^4}
                                  {4a^4(v-2a)^2}.
                                                               \tag{5}
\end{split}
\]
Indeed the rank-two positive cap is at most
\(\int_v^{1/2}dt/(t(1-t))\).
For rank four with the largest angle in \([v,1-v]\),
fix this unique designated largest factor at \(t\). The other
three have total \(1-t\); their two-variable simplex is of volume
\((1-t-3a)^2/2\). It is counted with factor \(1/3!\), and their
product is at least \(a^2(1-t-2a)\), by concavity of the sum of
logarithms (minimum at a corner). For all three exceptional
complementary pair slots in rank four, each of the three sums
\(t_1+t_2,t_1+t_3,t_1+t_4\) is in \((v,1-v)\).
The map from three independent coordinates to those sums has
Jacobian of absolute value \(2\); use volume at most \(w^3/2\),
\(1/4!\) from (4), and denominator at least \(a^4\).
For rank six, fix one of the ten triple slots and one designated
side of it, of total \(t\in(v,1-v)\). The two independent
three-factor groups have totals \(t,1-t\), volumes
\((t-3a)^2/2\), \((1-t-3a)^2/2\), and products at least
\(a^2(t-2a)\), \(a^2(1-t-2a)\). The change to \(t\) and two
free coordinates on each side has determinant of absolute
value one. Counting all slots with \(10/6!\) gives the last
line of (5); no extra factor of two is needed for the two
sides of a slot.

For the rank-five upper, write \(t_i=a+(1-5a)x_i\) on the
uniform unit simplex and \(s=\sum_i x_i^2\). The denominator is
at least \(a^5(1+c+\tfrac12c^2(1-s))\), by expanding the product
and keeping its first three nonnegative terms. The reciprocal of
the displayed affine function of \(s\) is convex on
\([1/5,1]\), hence lies below the secant joining the endpoints.
The simplex average of \(s\) is \(1/3\):
each \(x_i\) has density \(4(1-t)^3\) on \([0,1]\) and second
moment \(1/15\). The upper endpoint of the secant therefore has
average coefficient \(1/6\). Using volume \(1/4!\), scale
\((1-5a)^4\), and \(1/5!\) from (4) yields \(I_5\).

Thus the \(L\)-weighted unopposed mass of \(p\) is bounded by
\((P_a+o(1))|J|N\), and that of \(e\) by
\((I_{4,{\rm ex}}+o(1))|J|N\), where
\[
                       P_a=I_2+I_{4,+}+6I_5+I_{6,+}.          \tag{6}
\]
All estimates also hold on the reflected interval \(1-J\).

## 3. At the fixed target: genuine source products and rough opposition

For each of these nonnegative compact angular source tests, the
upper linear sieve on the **actual reflected integer** \(y=N-x\),
to \(z=N^a\) and level \(Q=N^{d_*}\), \(d_*=.49\), costs at most
\[
     \frac{\mathfrak S(N)}{L}(A_a+o(1)),\qquad
       A_a=\frac{2}{d_*}
             \left(1+\frac{(d_*/a-3)^2}{4}\right),             \tag{7}
\]
times its unopposed real moment. Here a moment can be the number
of tuples on the source or that count multiplied by \(L\).
This is not a postulated independence of the two arms.

For clarity, use the genuine product distribution in
[WholeMarkPrimeTransfer, §1](../nearfull_high_vaughan/WholeMarkPrimeTransfer.md).
On each fixed angular box the largest source factor is the
actual long prime variable; the remaining factor product
has divisor-bounded coefficients counting the true tuples.
A source factor \(L/\log r\) if needed is bounded with bounded
variation for the largest prime \(r\geq N^{a+o(1)}\).
The proof of that distribution gives arbitrary log accuracy
at the reduced residue \(N\) for each such box up to the
strictly sub-root \(Q\), with fixed divisor weights and the
literal spatial interval retained. In applying it one can
keep the source's \(N\)-unit mask. Angular mesh majorants are
positive, impose independent factor windows (overcounts
at walls vanish in the refinement limit), and the total
nonnegative source density tends to the angular upper in (5).
All opposite rough counts in the sieve are counts on the
actual source, not the unopposed approximation.

The reduced progression main term retains \((x,q)=1\).
Inserting the sieve weights and reassembling the source
therefore gives local density \(1/(p-1)\) for \(p\nmid Nx\)
and zero for \(p\mid Nx\). The prime \(2\) is absent because
\(N\) is even and we work on target units.
The corresponding product to \(z\) is uniformly
\((1+o(1))e^{-\gamma}\mathfrak S(Nx)/(aL)\).
The prime factors of \(Nx\) above \(z\) affect the tail by
\(o(1)\), since \(\omega(Nx)\ll L\).
The dimension-one local product ratio bound is uniform here:
deleting primes dividing \(Nx\) can only decrease the ratio,
and the standard full dimension-one ratio away from \(2\)
has the required uniform Mertens bound.
Finally \(\mathfrak S(Nx)/\mathfrak S(N)=1+o(1)\) uniformly,
since there are at most six additional prime factors and
all exceed \(N^{a+o(1)}\).

Use the [Rosser–Iwaniec upper sieve](https://www.impan.pl/shop/publication/transaction/download/product/102606)
with \(3<s=d_*/a<5\). In this range its upper function is
\(2e^\gamma s^{-1}(1+\int_3^s\log(t-2)/(t-1)\,dt)\);
see also [Weighted sieves with switching, (2.5)](https://www.cambridge.org/core/journals/mathematical-proceedings-of-the-cambridge-philosophical-society/article/weighted-sieves-with-switching/986429394BA969687D48224E177E2F1C).
Since \(\log(t-2)\leq t-3\) and \(t-1\geq2\), (7) follows
with the exact dimension-one normalizer.

Apply (7) also to the finitely many full rough source ranks
to see that the total count of squarefree bilateral rough
composite pairs is \(O(M/L^2)\); thus all the \(O_J(L^{-1})\)
errors in (3), in the normalized products, cost \(o(M)\).
By (6)–(7), the orientation with \(H(x)>0>H(y)\) is bounded by
\[
 A_a\bigl(2P_a+10 I_{4,{\rm ex}}\bigr)M+o(M):
\]
pointwise use \(p(x)(2+e(y))\leq 2p(x)+10e(y)\) while
retaining the bilateral rough constraint. The opposite
orientation obeys the same estimate. The checked rational
upper bound for \(2A_a(2P_a+10I_{4,{\rm ex}})\) is strictly
below \(.933\) at \(a=.145\) and strictly below \(.645\)
at \(a=.150\). The [arithmetic checker](check_rough_debit.py)
uses a rational upper on \(I_2\); it makes no empirical
assumption on fixed-target prime products. This proves (1).
