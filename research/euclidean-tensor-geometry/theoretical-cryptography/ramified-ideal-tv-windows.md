# Actual Gaussian mixing profiles for all dyadic ramified ideal depths

**Scope.** This is an exact total-variation calculation for a standalone
spherical Gaussian on the canonical torus of a principal ideal in the
dyadic cyclotomic family. It compares the wrapped noise to Haar, not
learning samples or a protocol, and gives no recovery algorithm or
scheme-level consequence.

The [earlier pointwise calculation](ramified-ideal-smoothing.md)
gave a first-shell estimate for the pointwise smoothing width and the
binary repeated-root code description. The same first shell does **not**
determine the actual TV curve. The analysis below computes all critical
subsequential curves, including a second contribution at depths just
above a dyadic boundary that survives even when the shortest shells
match. The contrast is between averaging signs within a coordinate
block and higher correlations between blocks forced by repeated roots.

## 1. Normalization and profile functions

Let \(d\to\infty\) through powers of two, and \(0\le a\le d\).
Write \(L_{d,a}\subset\mathbb Z^d\) for the coefficient lattice of
\((1-Y)^a\) in \(\mathbb Z[Y]/(Y^d+1)\).
It contains \(2\mathbb Z^d\); its parity image is
\[
       C_{d,a}=((1+Y)^a)\subset
              \mathbb F_2[Y]/((1+Y)^d).
\]
The normalized canonical ideal \( (1-Y)^{d-a}\) therefore has
dual isometric to \(2^{-a/d}L_{d,a}\), as explained below.
First use the torus with dual \(L_{d,a}\) in unscaled coefficient
units and let \(b=e^{-\pi s^2}\) be the single-coordinate Fourier
parameter at Gaussian width \(s\).
For the determinant-one canonical ideal with width \(s\) instead use
\(b=\exp(-\pi 2^{-2a/d}s^2)\) throughout. Haar is probability Haar.

For \(V\ge0\), let
\[
       \mathcal G(V)=\exp(\sqrt V Z-V/2),\qquad Z\sim N(0,1).
\]
For fixed integer \(j\ge1\) let \(D_j\) be the smallest power of two
at least \(j\). Let \(Z_i\) for \(0\le i<D_j\) be independent standard
real normals, and define
\[
 \mathcal M_j(T)=
  \frac{1}{|C_{D_j,j}^{\perp}|}
       \sum_{\eta\in C_{D_j,j}^{\perp}}
        \exp\!\left(
        \sqrt{T/D_j}\sum_{i=0}^{D_j-1}(-1)^{\eta_i}Z_i-T/2\right),
       \qquad T\ge0 .
 \tag{1}
\]
Here \({}^{\perp}\) is the ordinary binary orthogonal complement.
Use independent Gaussian variables when multiplying a \(\mathcal G\)
and an \(\mathcal M\). If \(D\) is any limiting likelihood listed
below, the TV limit is
\[
             \boxed{\qquad 1-\mathbb E\min(D,1).\qquad}
 \tag{2}
\]

## 2. The complete list of critical regimes

* **\(a=0\).** At \(d b^2\to T\in[0,\infty)\),
  \(D=\mathcal G(2T)\).
* **\(1\le a\le d/2\), or \(d/2<a\le3d/4\).**
  For the first range set \(\ell=1,\ N=d,\ j=a\);
  for the second set \(\ell=2,\ N=d/2,\ j=a-d/2\).
  Thus \(1\le j\le N/2\). Let \(B\) be the smallest power of two
  at least \(j\), \(H=N/B\ge2\), and take the critical scale
  \[
                  c_d=\sqrt B\,H(2b^2)^\ell .
  \]
  The following are the finite limits along subsequences:
  * If \(j=j_0\) is fixed and \(c_d\to c<\infty\), then
    \(D=\mathcal M_{j_0}(\sqrt B\,c)\).
  * If \(j\to\infty\), \(c_d\to c<\infty\), and
    \(H\to h\in[2,\infty]\), put
    \(V_0=(1-h^{-1})c^2/2\).
    The variance from even coordinate modes is \(V_e=0\) at
    \(\ell=1\), and \(V_e=c^2/(4h)\) at \(\ell=2\).
    Let \(r=j-B/2\), a positive integer in this case.
    If \(r\to\infty\), then \(D=\mathcal G(V_e+V_0)\).
    If \(r=r_0\) is fixed, then
    \[
                  D=\mathcal G(V_e+V_0)\,\mathcal M_{r_0}(c^2/2).
        \tag{3}
    \]
* **\(a>3d/4\).** Set \(j=a-3d/4\ge1\) and suppose \(db^8\to\beta<\infty\).
  If \(j\to\infty\), then \(D=\mathcal G(2\beta)\).
  If \(j=j_0\) is fixed, then
  \(D=\mathcal G(2\beta)\mathcal M_{j_0}(4\beta)\).

In each row, divergence of its critical scale (\(db^2\), \(c_d\), or
\(db^8\)) gives TV tending to one. A scale converging to zero gives TV
tending to zero. The categorization is subsequential only to allow,
for example, the depth to switch between different rows infinitely
often. Within a row the listed additional bounded integer or reciprocal
dyadic quantities always have a further convergent subsequence.

There is a concrete strict first-shell counterexample. Fix \(H=2\)
and \(B\to\infty\) dyadic, set \(d=2B\), and compare
\(a=B/2+1\) with \(a=B/2+2\) in unscaled units.
They have exactly the same shortest squared length and multiplicity
in the dual: the minimum is 2, with both signed coordinates in the
same one of \(B\) groups of size two. At the same limiting \(c>0\),
the TV in the first sequence is strictly higher than in the second.
In (3) the extra terms are respectively
\(e^{-T/2}\cosh(\sqrt{T}Z)\) and
\(e^{-T/2}\cosh(\sqrt{T/2}Z_1)\cosh(\sqrt{T/2}Z_2)\)
at \(T=c^2/2\), as proved in §6.

## 3. Exact parity reduction

The canonical coordinate map in degree \(d\) is a similarity:
its columns have squared norm \(d\) and distinct columns are
orthogonal by the sums over odd \(2d\)-th roots. In coefficient
coordinates multiplication by \(Y\) is a signed orthogonal shift.
The norm of \(1-Y\) has absolute value 2 and \((1-Y)^dR=2R\),
since the inclusion follows mod 2 and the indices agree.
Transposing the \(1-Y\) map gives \(1-Y^{-1}\), differing by a unit.
These facts give \(L_{d,a}^{*}=\tfrac12 L_{d,d-a}\) and yield
the stated determinant-one dual scaling. Equivalently one can
use the [LPR Toolkit's canonical/codifferent setup](https://web.eecs.umich.edu/~cpeikert/pubs/toolkit.pdf);
the repeated-root distance setting is classical (see
[Castagnoli–Massey–Schoeller–von Seemann](https://www.isiweb.ee.ethz.ch/papers/arch/gcasta-mass-inspec-1991-1.pdf)),
and the simple code identities we need are derived explicitly below.

Because \(L_{d,a}\subset\mathbb Z^d\), the density on its dual torus
can be lifted to the cube. By Haar pushforward or by the Fourier
characters of the quotient, its TV is exactly the TV of this lift.
Write \(f_b(x)=\sum_{k\in\mathbb Z} b^{k^2}e^{2\pi ikx}\).
Let \(g(x)\) and \(o(x)\) be its even- and odd-index harmonic
parts, and \(R(x)=o(x)/g(x)\). Thus \(g=(f_b(x)+f_b(x+1/2))/2>0\),
and the half-shift preserves \(g\) and negates \(R\).
The lift \(D_d\) of the wrapped density is the exact expression
\[
   D_d(x)=G_d(x)P_{C_{d,a}}\big((R(x_i))_{i<d}\big),
   \quad G_d(x)=\prod_{i<d}g(x_i),\quad
   P_C(X)=\sum_{u\in C}\prod_{i:u_i=1}X_i .
 \tag{4}
\]
This just sums Fourier coefficients independently within each parity
class. Whenever \(|X_i|<1\), the code polynomial is positive since
\[
    P_C(X)=\mathbb E_{\eta\in C^\perp}
                  \prod_i (1+(-1)^{\eta_i}X_i)
 \tag{5}
\]
by binary character orthogonality.

The code \(C_{d,a}\) in the indicated ranges consists of \(\ell\)
copies of a word from \(C_{N,j}\), with \((\ell,N,j)\) as in §2
and \(\ell=4,N=d/4,j=a-3d/4\) in the final range.
Indeed if \(m=d/2\) and \(a\ge m\), factor
\((1+Y)^m=1+Y^m\) to obtain equal halves and residual depth \(a-m\);
apply this twice as needed.
Consequently the code part of (4) has independent effective variables
\(X_i\), each the product of \(\ell\) independent copies of \(R(U)\)
for a cube Haar coordinate \(U\). Their variance \(v\) and moments
obey, for fixed \(\ell\in\{1,2,4\}\),
\[
 v=(2b^2)^\ell(1+O(b^4)),\qquad
 \mathbb E|X_i|^h\le C_{\ell,h}v^{h/2},\qquad
 \max |X_i|=o(1)
 \tag{6}
\]
as \(b\to0\), for every fixed \(h\ge2\).
This follows from \(R(x)=2b\cos(2\pi x)+O(b^5)\), uniformly.
The variables are symmetric. A change by \(1/2\) in any one
underlying coordinate negates just its \(X_i\), leaving all
even-mode factors \(g\) invariant. This parity symmetry is also
used for the joint limits.

## 4. A recursion for arbitrary small symmetric coordinate variables

Let \(1\le j\le N\), and \(B\) be the smallest power of two
at least \(j\). Reduce the polynomial modulo \(1+Y^B=(1+Y)^B\);
equivalently form \(B\) group parities in residue classes mod \(B\).
Its kernel is \(C_{N,B}\), the product of even parity codes on
the groups of size \(H=N/B\), and the image of \(C_{N,j}\)
is exactly \(C_{B,j}\). Divisibility by \((1+Y)^j\) is equivalent
to divisibility of this remainder. For a group \(g\), let
\[
 P_g^\pm=\prod_{i\in g}(1\pm X_i),\qquad
 E_g=(P_g^++P_g^-)/2,\qquad
 R_g=(P_g^+-P_g^-)/(P_g^++P_g^-).
\]
The code polynomial factors into
\[
      P_{C_{N,j}}(X)=(\prod_g E_g)P_{C_{B,j}}((R_g)_g).
      \tag{7}
\]
Alternatively by (5), if \(j=j_0\) is fixed, the dual signs are
constant on the \(B=D_{j_0}\) groups, indexed by \(C_{B,j_0}^\perp\).
When \(Nv\to T<\infty\) the group sums of \(X_i\) converge to
independent \(N(0,T/B)\), and each group sum of \(X_i^2\) converges
in probability to \(T/B\), by (6).
The third-order terms in the expansions of
\(\sum_i\log(1\pm X_i)\) are \(o_{\mathbb P}(1)\) because
\(\max|X_i|\to0\). This proves the limit (1) for the code part.

Now suppose \(j\to\infty\), \(1\le j\le N/2\),
and \(\sqrt B H v\to c<\infty\). Then \(B\to\infty\).
For \(\Delta_g=E_g-1\), symmetry gives mean zero and
\[
 \mathbb E\Delta_g^2=\binom H2 v^2+O((Hv)^4),\qquad
 \mathbb E\Delta_g^4=O((Hv)^4).
 \tag{8}
\]
For the second moment, expand the nonempty even subsets at a
group; their products are orthogonal under the symmetric
coordinate law. For the fourth moment, take four such subsets.
Each contributing coordinate appears twice or four times, and
there are at least eight total occurrences. If \(k\) distinct
coordinates appear, the assignment of their memberships in
the four factors has at most \(7^k\) choices (six pairs or all
four), and the weight is bounded by \(C^k v^{\max(k,4)}\)
using (6). For \(k\ge4\) sum using \(\binom Hk\), which gives
\(O((Hv)^4)\) as \(Hv\to0\); \(k<4\) contributes the same bound
since \(H\ge1\). This proves (8) uniformly in \(H\).
Thus \(\sum_g\Delta_g\) converges to \(N(0,V_0)\), where
\(V_0=(1-h^{-1})c^2/2\), and \(\sum_g\Delta_g^2\to V_0\)
in probability. Indeed \(B\mathbb E\Delta_g^4=O(1/B)\),
and \(B\mathbb E|\Delta_g|^3=O(1/\sqrt B)\) by (8).
Maximal \(|\Delta_g|\) tends to zero and the log Taylor
remainder tends to zero, so the first factor in (7) converges to
\(\mathcal G(V_0)\).

By minimality of \(B\) we have \(j>B/2\). Set \(r=j-B/2\);
the repeated-halves rule reduces the second factor in (7)
to \(P_{C_{B/2,r}}((Y_g)_{g<B/2})\) with
\(Y_g=R_g R_{g+B/2}\). The random variables \(Y_g\) are
independent and symmetric. The identity
\(R_g=\tanh(\sum_{i\in g}\operatorname{arctanh}X_i)\) gives
\[
    \mathbb E R_g^2=Hv(1+o(1)),\qquad
    \mathbb E |R_g|^h\le C_h(Hv)^{h/2}\quad(h=4,6).
\]
To check this, the symmetric summands \(\operatorname{arctanh}X_i\)
have variance \(v+O(v^2)\) and fourth/sixth moments
\(O(v^2),O(v^3)\) by (6) and \(\max |X_i|\to0\).
Their sum has second, fourth, sixth moments bounded by the
respective powers of \(Hv\) by expansion and independence.
Use \(|\tanh z|\le |z|\) and \(|\tanh^2 z-z^2|\le C z^4\).
Therefore \((B/2)\mathbb EY_g^2\to c^2/2\)
and \((B/2)\mathbb E|Y_g|^4=O(1/B)\).
If \(r=r_0\) is fixed, group the \(Y_g\)'s into \(D_{r_0}\) groups,
use (5), and apply the same finite-group central limit and Taylor
proof as above. In this case the fourth bound also gives
\(\max|Y_g|\to0\) in probability and the third moment remainder
tends to zero by Cauchy–Schwarz, so the limit is
\(\mathcal M_{r_0}(c^2/2)\).

If \(r\to\infty\), the residual factor tends to 1 in \(L^2\).
In fact for symmetric independent variables of variance \(w\)
the \(L^2\) error of \(P_{C_{M,r}}\) from 1 is
\(W_{C_{M,r}}(1,w)-1\), where \(W(1,w)=\sum_{z\in C} w^{|z|}\).
Let \(D\le r\) be the largest dyadic power at most \(r\).
By \(C_{M,r}\subseteq C_{M,D}\) and the exact block even enumerator,
\[
 W_{C_{M,r}}(1,w)\le
 \left(\frac{(1+w)^{M/D}+(1-w)^{M/D}}2\right)^D
       \le \exp(M^2 w^2/(2D)).
 \tag{9}
\]
The second inequality uses termwise comparison of even binomial
coefficients to \(\cosh((M/D)w)\), then
\(\cosh x\le e^{x^2/2}\). With \(M=B/2\) and
\(w=\mathbb E Y_g^2=O(1/B)\), this proves the claim.

## 5. Combine the limits and the remaining regimes

Under cube Haar, \(g(x)=1+2b^4\cos(4\pi x)+O(b^{16})\).
When \(db^8\) has a finite limit, expansion of \(\log g\) gives
mean \(-b^8+O(b^{12})\), variance \(2b^8+O(b^{12})\),
and hence \(G_d\Rightarrow\mathcal G(V_e)\),
\(V_e=\lim 2db^8\). The same proof applied to \(f_b\) establishes
the \(a=0\) row directly.
In the first positive depth range (6) and the finite \(c_d\)
scale imply \(db^8=o(1)\); in the second
\(2db^8=c_d^2/(4H)\) by the definition of \(c_d\).
This supplies the even variance in §2.

The required code and even-mode limits are jointly independent,
not just marginal. For fixed \(j\), apply the multivariate central
limit theorem to the sums over independent effective coordinates:
the underlying \(\ell\) even log factors for one coordinate
are uncorrelated with its \(X_i\), by flipping one raw coordinate.
For \(j\to\infty\) group summands into independent pairs of
groups \((g,g+B/2)\) for the triangular array CLT, including the
sums of even logs, group \(\Delta_g\)'s, and the residual \(Y_g\)
sums when \(r\) is bounded. Every covariance involving \(Y_g\)
and another kind of summand is zero by flipping one whole group
of effective signs. The covariance between \(\Delta_g\)
and an even log sum is zero by expanding each nonempty monomial
in \(\Delta_g\) and flipping one raw sign in that monomial.
Even-log fluctuations over a paired block have fourth moment
\(O((d b^8/B)^2)=O(B^{-2})\) by the independence of its raw
coordinates and their second/fourth moment bounds.
The fourth bounds in §4 then prove the joint Lindeberg condition.
Limiting jointly Gaussian sums with zero cross covariances
give independence, and all the quadratic drifts were shown to
converge to constants.

For the last depth range use \(\ell=4,N=d/4\).
If \(db^8\to\beta<\infty\), (6) gives \(Nv\to4\beta\).
With \(j\) bounded the finite-group argument gives
\(\mathcal M_j(4\beta)\), jointly independent of \(G_d\) as above.
With \(j\to\infty\), (9) applies directly to \(P_{C_{N,j}}\),
with variance \(v=O(1/N)\), so the code factor tends to 1.
This proves the last row. For all finite windows (2) is valid
by weak convergence under Haar and the bounded continuous
overlap \(x\mapsto\min(x,1)\).

For divergent scales, use monotonicity of TV under increasing
Gaussian variance. For each fixed positive value of the
scale choose the larger width giving that value, then send
the chosen finite scale to infinity.
For bounded \(j\), each finite mixture in (1) tends to zero
almost surely on a common Gaussian space as \(T\to\infty\).
For unbounded \(j\) in the middle rows, \(h\ge2\) ensures
\(V_0\to\infty\) as \(c\to\infty\); the lognormal factor tends
to zero on such a coupling. The extra factor, when present,
also tends to zero. For the final row the same is true
of \(\mathcal G(2\beta)\). Thus their bounded overlap tends to zero,
which gives TV tending to one in the divergent case.
Taking the scale to zero in the finite formulas yields TV zero.

## 6. Strict first-shell separation

Weight-two words in \(C_{d,a}\) lie exactly within one residue group
modulo \(B\): the multiplicity of \(1+Y\) in \(1+Y^k\)
is \(2^{\nu_2(k)}\), found by writing \(k\) as a power of two
times an odd number. The number of signed shortest vectors is
then \(4B\binom H2\), independent of \(r=j-B/2\).
In the two examples of §2, \(\mathcal M_1(T)\) and
\(\mathcal M_2(T)\) have the displayed cosh formulas because
at \(j=D_j=1,2\) the finite code is zero.
Write \(Z=(Z_1+Z_2)/\sqrt2\).
By the cosh addition rule and independent symmetric signs,
\[
 \mathbb E\!\left[e^{-T/2}\cosh(\sqrt T Z)\,\middle|\,
          |Z_1|,|Z_2|\right]
      =e^{-T/2}\cosh(\sqrt{T/2}Z_1)\cosh(\sqrt{T/2}Z_2).
\]
Multiply both sides by the same independent primary lognormal
factor \(G=\mathcal G(V_0)\).
Conditional Jensen for \(|G M-1|\) proves the claimed TV order.
It is strict: for a.e. nonzero \(|Z_1|,|Z_2|\), the two
conditional values of \(M\) are different and positive; the
independent \(G\) has a positive density on \((0,\infty)\)
because \(V_0>0\). Hence 1 is strictly between the two possible
values of \(G M\) with positive probability. Both limiting
likelihoods have mean 1 (each constituent lognormal does),
so this absolute-value comparison is the strict inequality
also for (2).

**Replay.** Run `node verify-ramified-ideal-tv-windows.js`
for finite exact repeated-root/quotient/character identities and
synthetic checks of the even-group moment and variance formulas.
The infinite-dimensional TV limits use the analytic arguments above.
