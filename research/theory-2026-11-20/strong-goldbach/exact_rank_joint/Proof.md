# Both summands can be genuine rough composites of rank two or three

Let \(N\) be an individual even integer and \(J\Subset(0,1)\)
a fixed interval of positive length. Set \(L=\log N\), \(z=N^{1/8}\),
and use the usual binary singular series \(\mathfrak S(N)\).
Then, for all sufficiently large even \(N\), there are at least
\[
       \frac{1}{25}\frac{|J|N\mathfrak S(N)}{L^2}                 \tag{1}
\]
distinct ordered actual pairs \(x+y=N,\ x\in NJ,\ (x,N)=1\),
having the following property: **each** of \(x,y\) is a product
of either two or three distinct primes, and every one of the
prime factors exceeds \(z\). A prime coordinate is not an option.
No choice between the two ranks on either arm, or even equality
of the two ranks, is concluded in this first assertion.

There are also two strengthened, separate assertions at the
slightly smaller common floor \(z_1=N^{.092}\). In each case
the number of pairs is \(\gg_J |J|N\mathfrak S(N)/L^2\).
On all these pairs the genuine factors are distinct in each
summand, exceed \(z_1\), and the target-unit condition holds.

* One prescribed arm \(x\) can be a genuine semiprime
  with a prime factor \(>N^{.518}\), while the other arm
  is a product of two or three primes.
* Alternatively both arms can be products of two or three
  primes and **each** can have a prime factor \(>N^{.518}\).

These two lower bounds may overlap. They are not added,
and they do not jointly require two high marks and a
prescribed semiprime on one arm. In particular none
implies a representation by two semiprimes.

The argument is a quantitative use of inclusion-exclusion in
one actual rough ambient set. Its arithmetic inputs are
ordinary below-root distribution for actual prime products
and a dimension-two Selberg upper with an explicit
one-sided variance bound. It is related to the older
[Uchiyama, *On the representation of large even integers as sums of two almost primes II*](https://eprints.lib.hokudai.ac.jp/repo/huscap/all/56054/JFSHIU_18_N1-2_069-077.pdf),
which studies almost-prime decompositions using this same
type of bilateral rough ambient set and discusses the
at-most-three problem. Here the quantified conclusion
counts central pairs with **both** summands composite,
squarefree, and genuinely polynomially rough. No priority
claim or binary Goldbach implication is made.

## 1. One common actual ambient upper

Use the exact local factors
\[
 V(z)=\prod_{p\le z}(1-1/p),\qquad
 V_N(z)=\prod_{\substack{p\le z\\p\nmid N}}
                  (1-1/(p-1)),\qquad B_0=|J|N V(z)V_N(z).
\]
At \(p\mid N\) the two forms \(x,N-x\) have coincident roots,
including at \(p=2\). At \(p\nmid N\) there are two distinct
roots. Thus their joint root density is \(\nu(p)/p\) with
\(\nu(p)=1\) at \(p\mid N\) and \(2\) otherwise, and their
exact no-root product is \(V(z)V_N(z)\).

Let \(\mathcal B\) be the actual integers \(x\in NJ\)
with \((x,N)=1\) and both \(x,N-x\) having no prime factor
at most \(z\). For an upper bound one may omit the target
unit condition. Apply the positive Selberg square at
label cutoff \(D=N^{.498}\). Its main term is
\[
 \frac{|J|N}
 {\sum_{d\le D,\ d\mid \prod_{p\le z}p}
              \prod_{p\mid d}\nu(p)/(p-\nu(p))}.
\]
The standard Selberg coefficients have magnitude at most
\(\prod_{p\mid d}(1-\nu(p)/p)^{-1}\le3^{\omega(d)}\).
For fixed \(d,e\) the actual squarefree modulus is
\([d,e]\); CRT counts at most
\(2^{\omega([d,e])}\) individual residue floors.
Thus the floor is
\(O((\sum_{d\le D}6^{\omega(d)})^2)=O(D^2 L^{10})\).
Here \(6^{\omega(d)}\le\tau_6(d)\).
This is power-small, since \(D^2=N^{.996}\).
The formula and coefficient bound are also spelled out in
[the fixed-quotient Selberg calculation](../nearfull_high_vaughan/PolynomialSmoothedGiantReduction.md).

Normalize the full, positive denominator Euler product
to a probability measure; the independent event \(p\mid d\)
has probability \(\nu(p)/p\).
The variable \(\log d\) has mean at most
\(2\log z+O(1)=L/4+O(1)\) and variance at most
\((\log z)^2+O(\log z)=L^2/64+O(L)\).
Indeed its first moment is bounded by
\(2\sum_{p\le z}(\log p)/p\); use the same bound with
\((\log p)^2\) for the variance and ordinary partial
summation from the prime log harmonic.
Cantelli's one-sided variance bound gives
\(\Pr(\log d\le\log D)\ge
h^2/(h^2+\mathrm{Var})\) with
\(h\ge(.498-.25)L-O(1)\).
Consequently
\[
       |\mathcal B|\le
        \left(1+\frac{(1/8)^2}{(.498-.25)^2}+o(1)\right)B_0
                              <1.255B_0                         \tag{2}
\]
for large \(N\).

Uniformly in the individual even target, the usual Mertens
law and the local factor comparison give
\[
   V(z)\sim \frac{e^{-\gamma_E}}{(1/8)L},
   \qquad
   V_N(z)/V(z)=(1+o(1))\mathfrak S(N).                           \tag{3}
\]
At any prime \(p\nmid N\) the ratio is
\(p(p-2)/(p-1)^2\), while at \(p\mid N\) it is
\((1-1/p)^{-1}\). The non-target omitted tail converges
absolutely; the omitted target-prime correction is
\(O(L/z)\). In particular the floor in (2) is \(o(B_0)\),
without a bound on the radical of \(N\).

## 2. Actual low-rank product marginals

Write \(\beta=1/8\).
On one arm take the genuine numbers that are a product
of two or three distinct primes \(>z\), and retain target
units. Their **ordinary, unopposed** count in \(NJ\) is
\[
       \frac{|J|N}{L}\bigl(I_2+I_3+o(1)\bigr),\qquad
 I_2=\log 7,\quad
 I_3=\int_{1/8}^{1/3}
         \frac{\log((1-2u)/u)}{u(1-u)}\,du .                      \tag{4}
\]
For rank two order the factor angles \(u\le v=1-u\);
the density is \(du/[u(1-u)]\) for \(\beta<u<1/2\).
For rank three use ordered angles
\(u\le v\le 1-u-v\). The density is
\(du\,dv/[u v(1-u-v)]\); integrating from \(v=u\)
to \(v=(1-u)/2\) gives the integral in (4).
These orbital source densities follow by applying
the ordinary prime number theorem on the real interval
for the largest factor, after fixing the other one or
two genuine factors, and the prime reciprocal harmonic
on the latter variables. For precision one may approximate
the two compact strictly ordered angle interiors by
finitely many disjoint exponent boxes. On a box the
largest factor interval has power-sized scale, and the
PNT can be used on the two actual prefixes even near a
product boundary. Fixed-factor spatial localization alters
the exponent sum by \(O_J(1/L)\).
The boundary sets have zero angular measure and all
individual angles are bounded away from zero.
Actual repeated factors are already excluded on the
strictly ordered interior; globally prime squares
above \(z\) have \(O(N/z)\) possible multiples.
The same \(O(NL/z)\) crude integer bound disposes
of nonunits on this rough source.

To use positive lower sifting on the other arm it
suffices to keep a finite union of such genuinely
ordered boxes with source constant arbitrarily close
to \(I_2+I_3\) from below. Separate the actual
largest prime \(r\) from the other factor product \(m\).
On each box the \(r\) and \(m\) coefficients are independent:
for rank two \(m\) is an actual prime in its box;
for rank three it is a product of two actual primes in
disjoint ordered exponent intervals. The latter
\(m\) coefficient is bounded by \(\tau(m)\) and the
prime factorization is unique on these labels.
The congruence needed for every genuine sieve label is
\(r m\equiv N\bmod d\) with \(d\le D\), prime factors of
\(d\) at most \(z\) and coprime to \(N\).
Use the weighted ordinary product BV calculation of
[WholeMarkPrimeTransfer, §1](../nearfull_high_vaughan/WholeMarkPrimeTransfer.md)
with the actual prime \(r\) and arbitrary short
\(m\)-coefficient. Its power margins are available since
both variables have positive polynomial length and
\(D=N^{.498}\). To pass to unweighted primes insert
\(L/\log r\) into its true log-prime coefficient and
divide by \(L\); on these polynomial dyads this is a
bounded smooth factor as in the original proof.
The product condition \(rm\in NJ\) is the real fixed
interval reconstruction in that theorem.
The finite number of boxes multiplies the BV error by
a constant, and the accuracy is chosen after the boxes
and sieve coefficients. Each genuine factor of \(x\)
exceeds \(z\), so \((x,d)=1\) is automatic in the
reduced principal. Its value is exactly the ordinary
source mass divided by \(\varphi(d)\).
There is no unproved dispersion estimate at a modulus
above the square root and no averaging over \(N\).

Apply the [ordinary linear lower sieve](https://doi.org/10.4064/aa-37-1-307-320)
of level \(D\) to \(y=N-x\) for this true product
source. Its local density is \(1/(p-1)\) at \(p\nmid N\);
target primes are already excluded by the physical
unit condition. This density has uniform dimension-one
constants: after removing 2 it is bounded on interval
products by Mertens' dimension-one product times
\(\prod_p(1+O(p^{-2}))\) with the corresponding
uniform tail. The linear lower main factor is
\[
      f(s)V_N(z),\qquad s=.498/\beta=3.984,\qquad
      f(s)=2e^{\gamma_E}\log(s-1)/s,\quad 2<s<4 .
\]
Absolute weighted product BV pays the genuine sieve
errors with arbitrary log saving. Let \(\mathcal B_x\)
denote the actual part of the common \(\mathcal B\)
where \(x\) is squarefree of rank two or three.
By (3)--(4), choosing the fixed angle boxes arbitrarily
fine before \(N\to\infty\) yields
\[
 |\mathcal B_x|\ge
   \left(e^{\gamma_E}\beta f(s)(I_2+I_3)-o(1)\right)B_0
                           >.685 B_0.                            \tag{5}
\]
The liminf interpretation of the first inequality
is sufficient: all approximations and tolerances can
be taken fixed within the final strict numerical margin.
Reflect the computation, now using the actual central
interval \(1-J\) for \(y/N\), to obtain
the identical lower for \(\mathcal B_y\subset\mathcal B\).
Neither estimate assumes that the opposite arm has low
rank; only its real rough and target-unit mask is used.

The [rational certificate](check.py) checks the constants
in (2), (5) using \(e^{\gamma_E}>1.78\),
\(f(s)>.976\), \(I_2>1.945,\ I_3>1.211\).
For the last estimate the displayed \(I_3\) integrand
is nonnegative and decreasing, so right endpoints on
512 equal intervals give a lower Riemann sum.
The logarithms use positive odd-power expansions, with
their bounded geometric tails where needed.
There is no numerical integration with unverified rounding.

## 3. Both coordinates are composite in the actual intersection

There is just one common rough set \(\mathcal B\),
not two separate independent sieve models. The actual
inequality
\[
     |\mathcal B_x\cap\mathcal B_y|
        \ge|\mathcal B_x|+|\mathcal B_y|-|\mathcal B|
        > .110 B_0
\]
holds for all large even \(N\) by the explicit bounds.
Each coordinate in the intersection is already
one of the true squarefree rank-two or rank-three
products, with no prime alternative or weighting.
Since \(B_0=(1+o(1))|J|N\mathfrak S(N)
e^{-2\gamma_E}/(\beta L)^2\) by (3), this implies the
weaker clean constant in (1); even \(e^{\gamma_E}<3\)
suffices for that implication. In fact the displayed
strict \(.110 B_0\) is the more informative lower.
Distinct \(x\)'s are distinct ordered actual pairs.
Nothing in this inclusion-exclusion separates the
three possible rank arrangements \((2,2),(2,3),(3,3)\).


## 4. A sharper ambient upper at the .092 floor

Now use \(\beta=.092=23/250\), \(z_1=N^\beta\) in
the same ambient set and write
\[
 B_1=|J|N V(z_1)V_N(z_1),\qquad s=.498/\beta=249/46 .
\]
All local factors in §1, including those for primes
dividing the target, remain exact. Keep the identical
Selberg label cutoff \(D=N^{.498}\) and its floor error.
On the normalized complete denominator let
\(S=\log d/\log z_1\) and fix \(t=7/4\). Then
\[
 \begin{split}
 \log\mathbb E e^{t S}
  &=\sum_{p\le z_1}
    \log\!\left(1+\frac{\nu(p)}p
              (e^{t\log p/\log z_1}-1)\right)\\
  &\le 2\sum_{p\le z_1}\frac{e^{t\log p/\log z_1}-1}{p}
    =2\sum_{j\ge1}\frac{t^j}{j\,j!}+o(1).
 \end{split}                                                       \tag{6}
\]
Here \(\nu(p)\le2\) only enlarges an upper bound;
it does not replace the exact denominator normalization.
The final expression follows by the prime log harmonic
and partial summation: for fixed \(j\ge1\),
\(\sum_{p\le z_1}(\log p)^j/p
=(\log z_1)^j/j+O_j((1+\log z_1)^{j-1})\).
The exponential series may be summed by domination,
since \((\log p/\log z_1)^j\le\log p/\log z_1\)
for every \(j\ge1\). All errors are uniform in \(N\).
Exponential Markov and the rational certificate give
\[
 \limsup \Pr(S>s)
   \le \exp\!\left(2\sum_{j\ge1}\frac{t^j}{j\,j!}-t s\right)
   < .02791.
\]
Indeed the exponent is \(<-3.579\); a finite positive
series for \(e^{3.579}\) proves the strict probability
bound. Thus the whole actual rough ambient satisfies
\[
                       |\mathcal B|<1.0288 B_1                    \tag{7}
\]
for all large \(N\). This upper is for the same common
ambient in both subsequent comparisons.

## 5. True high-mark and exact-rank marginals

Let \(\rho=.518=259/500\). The ordinary source integrals
\(I_2,I_3\) have the same expressions as (4) with
\(\beta=.092\). The true condition that the largest
prime exceed \(N^\rho\) changes the integrals to
\[
 \begin{split}
  I_{2,H}&=\log\frac{(1-\rho)(1-\beta)}{\rho\beta},\\
  I_{3,H}&=\int_\beta^{(1-\rho)/2}
     \frac{\log\!\bigl((1-\rho-u)(1-2u)/(\rho u)\bigr)}
          {u(1-u)}\,du .
 \end{split}                                                       \tag{8}
\]
Indeed for rank three with ordered small angles \(u\le v\),
the largest angle is \(1-u-v>\rho\); hence
\(v<1-\rho-u\), which lies strictly below \((1-u)/2\).
Integrating the same \(v\)-density gives (8). The
largest prime on these true \(H\) rows is unique,
since \(\rho>1/2\). The literal \(>N^\rho\) gate is
included on each finite interior angle box; the shift
\(\log x/L=1+O_J(1/L)\) only affects a vanishing
boundary collar of these compact angle domains.
Equivalently, one can use a successively tighter
fixed box approximation from inside the strict
polyhedra before the large-\(N\) limit, as in §2.
There is no assumed distribution in a varying prime
interval of vanishing relative width.

The ordinary linear lower sieve is still at the actual
level \(D=N^{.498}\), now with \(s>4\).
The standard delay equation \((s f(s))'=F(s-1)\)
and \(F(v)\ge1\) for the linear upper function give
\[
             f(s)\ \ge\
            \frac{2e^{\gamma_E}\log 3+s-4}{s}.                    \tag{9}
\]
This uses the value \(4 f(4)=2e^{\gamma_E}\log3\)
at the end of the first lower branch. No extrapolation
of that branch past \(4\) is used.

Let \(A_x\) be the actual rank-two-or-three part of the
rough ambient, \(H_{2,x}\) the actual rank-two part
with the largest prime \(>N^\rho\), and \(H_x\) the
actual rank-two-or-three part with that high mark.
Use the same definitions on the reflected arm \(y\).
By §2 and (8)--(9), their lower coefficients relative
to \(B_1\) are \(e^{\gamma_E}\beta f(s)\) times,
respectively,
\[
                         I_2+I_3,\quad I_{2,H},
                            \quad I_{2,H}+I_{3,H}.
\]
This is the same **actual** product BV calculation on
each finite box, ordinary short sieve on the opponent,
and normalization by \(B_1\). In particular the
\(H_{2,x}\) source consists only of genuine squarefree
semiprimes with a uniquely determined high prime.
The actual root labels on the second arm are still
coprime to the physical product and to \(N\).
The endpoint test and the small-factor interval
on each true prime are independent box masks before
\(rm\in NJ\) is reconstructed. The three lower
marginals are not assumed simultaneously independent.

The [rational certificate](check.py) gives
\[
 \begin{split}
  e^{\gamma_E}\beta f(s)(I_{2,H}+I_2+I_3)&>1.0317,\\
  2e^{\gamma_E}\beta f(s)(I_{2,H}+I_{3,H})
           -(1-.02791)^{-1}&>.063 .
 \end{split}
\]
For the second integral in (8) the logarithm is
nonnegative and decreasing on the given interval,
and \(u(1-u)\) increases. The 1024 right-endpoint
subintervals in the certificate therefore enclose
each \(I_3\) from below, including the one in (8).
Both claimed comparisons have fixed strict slack;
choose finite angular tolerances and then take \(N\)
large. Actual inclusion-exclusion using (7) shows
\[
            |H_{2,x}\cap A_y|>.0028 B_1,\qquad
            |H_x\cap H_y|>.06 B_1 .
\]
We bound these intersections separately. An actual pair
counted in both can appear twice across the statements,
but no numerical bound ever pools the statements.
Since \(B_1\asymp_J |J|N\mathfrak S(N)/L^2\),
these establish the strengthened assertions.

## 6. What the all-high cohort gives for the common wide affine score

For comparison take the actual profile of
[WholeMarkPrimeTransfer, §3](../nearfull_high_vaughan/WholeMarkPrimeTransfer.md):
\(0<\lambda\le .006\), \(F(t)=1+t/(1-\lambda)\) on
\([0,.486]\), supported in \([0,.490]\).
Let \(L_F(v)\) denote its genuine composite score restricted
to marks \(\le N^\rho\), still above \(N^\lambda\).
On the actual \(H_x\cap H_y\) cohort of §5, this is the
same original profile, not a repaired or centered variant.

For a true rank-two arm \(v=r u\), \(r>N^\rho\),
the only low mark is \(u\). The complementary divisor
\(r\) is outside the support, so
\(L_F(v)=(\log u)F(t_1(v))>.09L\).
For a true rank-three arm \(v=r u w\), the two low
marks are \(u,w\). All terms containing the genuine
large prime \(r\) are outside the support. The other
possible divisors have argument at most
\(\log(N/r)/L<.482\), so the exact affine differences give
\[
                 L_F(v)=
                 -\frac{2(\log u)(\log w)}{(1-\lambda)L}
                           <-.016 L .
\]
Both low marks really exceed \(N^\lambda\), since all
physical factors on this cohort exceed \(N^{.092}\).
Consequently its actual absolute low–low weight exceeds
\(10^{-4}|J|N\mathfrak S(N)\) for large \(N\):
use \(.016^2 L^2\) per row and \(.06B_1\) rows, with
\(e^{\gamma_E}<3\) in (3). Its terms with matching ranks
are positive and those with opposite ranks are negative.
The proved actual intersection is not a lower bound
on either **specified** rank arrangement, and it is
not a signed lower on the full low–low sector. In
particular there is no four-prime or binary conclusion.
