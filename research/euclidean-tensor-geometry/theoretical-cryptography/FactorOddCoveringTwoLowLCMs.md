# Two possible low LCMs and mandatory moduli for odd distinct covers

Let a finite family of residue classes with pairwise distinct odd
moduli greater than one cover \(\mathbb Z\), and let Q be its least
common multiple.

**Theorem.** If \(Q<473\,824\,157\,932\,125\), then
\[
 Q\in\{168\,131\,152\,814\,625,\;320\,977\,655\,373\,375\}.
\]
In the prime order \(3,5,7,11,13,17,19,23,29\), the respective
exponent vectors are \((4,3,2,2,1,1,1,1,1)\) and
\((5,3,3,1,1,1,1,1,1)\). The first possible LCM forces 70
particular moduli, and the second forces 131 particular moduli,
as listed with one checkable schedule each in
[the certificate table](odd_covering_two_exception_schedules.json).
Each so listed progression is indispensable in any putative cover
at the corresponding ambient period, even if deleting it leaves a
family with smaller LCM.

This strengthens the necessary conditions of the
[pinned finite-support note](https://github.com/mxym/math/blob/7e450d3f8daea8a6877f260b8e20754de76bb4b0/research/euclidean-tensor-geometry/theoretical-cryptography/FactorOddCoveringFiniteSupportLCM.md);
the **numerical lower bound remains \(168\,131\,152\,814\,625\)**.
Neither LCM is proved attainable or impossible, and the general
odd distinct covering problem is not settled. In particular, the
two exceptional exponent vectors are not two covering examples.
The initial search and frozen threshold choices are credited to
the Dreamer research contribution; both the omission comparison
and the arithmetic were independently rechecked for this note.

## 1. From two packed exceptions to two actual LCMs

We import two conditions on actual covers, as in the pinned note:
\(45\mid Q\) from [Dai–Li–Li–Yi](https://arxiv.org/abs/2611.15110)
and \(\omega(Q)\ge9\) from
[Schroeder's rank-nine theorem](https://michaelschroeder.ai/research/NinePrimeSupport/companion).
For a fixed exponent vector and a schedule by sorted prime position,
the pinned distortion/scalar bound weakly increases as the
support primes are replaced coordinatewise by smaller primes.
The least possible rank-13 product, with the mandatory extra
factor 3, is already above the displayed cutoff.

For ranks \(9,\ldots,12\), enumerate the positive exponent vectors
on the first r odd primes with product strictly below the cutoff
and with first exponent at least two. This cap, combined with
the other positive exponents, includes every actual cover
satisfying the two imported theorems. The two schedules of the
pinned note leave just the two indicated rank-nine exponent
vectors unexcluded. Here ppm denotes rounding *up* to a millionth,
performed after exact rational evaluation.

| Rank | Packed profiles | Maximum ppm on excluded profiles | Exceptions |
|---:|---:|---:|---:|
| 9 | 1081 | 998264 | 2 |
| 10 | 211 | 993646 | 0 |
| 11 | 20 | 843424 | 0 |
| 12 | 1 | 561855 | 0 |

For either exceptional vector, any different actual rank-nine
support is coordinatewise at least
\((3,5,7,11,13,17,19,23,31)\), since the first nine odd primes
are exactly the odd primes through 29. On this shifted support,
use the two old schedules and also the following schedule
from \(j=3\) onward. Entries are
(delete the pure tower, threshold in units of \(1/10000\)):
\[
(0,3265),(0,3967),(0,4615),(0,4706),(0,4211),(1,5000),(1,5000).
\]
The smaller loss bounds on the shifted support round upward to
996519 and 995453 ppm, respectively. Monotonicity with fixed
exponents and a fixed choice of schedule rules out all other
actual supports. The product of the minimal support primes to
the specified powers gives the claimed two integers.

## 2. The exact loss bound with one omitted modulus

We recall the notation of the pinned note. Let \(p_j\) be the
sorted primes, \(a_j\) their caps, \(s_j=\sum_{e=1}^{a_j}p_j^{-e}\),
and \(\eta_j\in\{0,1\}\) indicate that the pure \(p_j\)-power
classes are removed from the reference coordinate law. Put
\(g_j=(1-s_j)^{-\eta_j}\), \(c_j=(1-\delta_j)^{-1}\), and take
\(\eta_1=\eta_2=1,\delta_1=\delta_2=0\). On the surviving reference
product, the distortion/scalar comparison uses mutually
independent variables \(D_i\) with
\(\mathbb P(D_i\ge e+1)=c_i g_i p_i^{-e}\) for \(1\le e\le a_i\),
and zero tail beyond this. With \(X_j=\prod_{i<j}D_i\) it
bounds stage j by
\[
  c_j\mathbb E\big[g_j s_j(X_j-\eta_j)-\delta_j\big]_+ .
\tag{1}
\]
This also includes stage 1 (zero) and stage 2 (the product of
the two capped pure tower sums adjusted by \(g_1,g_2\)). The
condition that the sum of these upper bounds is strictly below
one contradicts covering.

Now posit that one specified divisor \(m>1\) of the ambient Q
does not occur as a modulus. Write \(m=\prod_{i\le j}p_i^{e_i}\)
with \(e_j>0\) and preceding exponents \(e_i\ge0\).

* If m is a pure \(p_j\)-power and \(\eta_j=1\), the mass
  deleted at coordinate j is at most \(s_j-p_j^{-e_j}\).
  Replace \(g_j\) by \((1-s_j+p_j^{-e_j})^{-1}\) everywhere,
  including in the law of \(D_j\) in subsequent stages.
  Keep the mixed-modulus weight sum \(s_j\) unchanged:
  a missing pure power does not forbid a mixed modulus with
  that same \(p_j\)-exponent.
* Otherwise the permissible list of stage-j prefix terms
  omits exactly the tuple for m. For a fixed preceding real
  coordinate value, every other modulus contributes at most
  \(g_jp_j^{-e}\) times its prefix indicator, one per modulus
  by distinctness. Apply the same convex scalar comparison
  without introducing the omitted term: each remaining weight
  is nonnegative. Replacing coordinates in reverse order gives
  the comparison indicator of the omitted tuple
  \[
   \mathbf1_A,\qquad
   A=\bigcap_{i<j}\{D_i\ge e_i+1\}.
  \]
  Thus, in (1) at the one stage j, subtract
  \(g_jp_j^{-e_j}\mathbf1_A\) *inside* the positive part.
  For an undeleted pure power, A is the whole sample space.
  All other stages and the common conditional bounds on later
  transitions are unchanged.

In the mixed case the event A is not averaged before taking the
positive part. Equivalently, if \(Y=g_js_j(X_j-\eta_j)-\delta_j\)
and \(w=g_jp_j^{-e_j}\), the gain is
\(\mathbb E[\mathbf1_A\min(Y_+,w)]\), multiplied by \(c_j\).
This is why the grouped replay can track both the unconditional
and the A-restricted joint mass with the same denominator.
The independent replay instead directly integrates the two
possible payoffs over the Cartesian coordinates.

Every omitted-modulus row in the certificate table yields
strictly subunit loss for some rational schedule. The smaller
ambient Q has 70 such certified necessities with maximum
999828 ppm; the larger has 131 with maximum 999993 ppm.
No claim is made that another modulus can be omitted. The
omission calculation needs only that all remaining moduli
divide the prescribed ambient Q; it does not re-use the
imported 45-divisibility or rank conditions after a deletion.
Thus if any mandatory class were redundant its deletion
would contradict that row of the table. In particular, two
mandatory classes with comparable moduli cannot be nested;
two different mandatory powers of the same prime must have
disjoint residue sets.

## 3. Verification and finite schedules

From this directory run:
~~~sh
node verify_factor_odd_covering_two_exceptions.mjs odd_covering_two_exception_schedules.json
python3 verify_factor_odd_covering_two_exceptions.py odd_covering_two_exception_schedules.json
~~~
Both runs use exact arithmetic. The Node check uses multiplicative
convolution of independent integer masses, with a second
convolution restricted to the prefix event when needed.
The independent Python check enumerates smooth excess integer
factors for the packed census, uses independently normalized
coordinate probabilities, and sums over actual Cartesian
tuples at each stage, including direct conditional omission.
Both check all 201 omission rows and both shifted supports.
Neither solver is needed to discover thresholds in order to
verify the claims. All exact denominators are positive; the
integral product keys in the Node convolution are below
\(2^{53}\), since \(\prod_i(a_i+1)\le\prod_i p_i^{a_i}\), and
all supports passed to that convolution have product below \(2^{53}\).

For possible further threshold searches, with deletion flags
fixed, set \(c_j=(1-\delta_j)^{-1}\in[1,2]\). Conditional on the
finite comparison coordinates, the payoff at stage j has form
\([1+c_j(z-1)]_+\), with z independent of \(c_j\).
Breakpoints inside the interval can only occur when
\(\delta_j=z\) lies in \([0,1/2]\). In an omission case include
both \(z=g_js_j(X_j-\eta_j)\) and the z with the term removed
on A. Each coordinate law is affine in its own \(c_j\),
so on each resulting Cartesian box the full bound is
multiaffine and a minimum is obtained at a box corner.
This observation is not needed for the finite certificates
above, and we do not claim the listed schedules minimize loss.
