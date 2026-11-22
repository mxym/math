# The full chamber with three genuine small tags on each arm

Use the same fixed even target \(N\), interval \(J\Subset(1/3,2/3)\),
\(L=\log N\), \(M=|J|N\mathfrak S(N)\), and actual score
\(S=G_b+W\), \(b=.003\), as in the
[two-by-three comparison](TwoByThreeTagCredit.md).
All pairings use the original \(x+y=N,\ x\in NJ,\ (x,N)=1\).

Let \(\mathcal C_3\) be the actual squarefree integers with exactly
three distinct prime factors in \((N^{.003},N^{.080}]\) and
with every other prime factor \(>N^{.080}\).
The quotient after those three tags is not required to be prime.
There is no other restriction on tag sums, quotient ranks,
residues, or signs.

**Proposition.** For every sufficiently large even target,
\[
 \sum_{x,y\in\mathcal C_3} S(x)S(y)>.037M+o(M).
\]
This entire chamber is disjoint from every chamber in the previous
comparison. In particular
\[
             R_J\ \ge\ 1.162M+\mathcal R_{\rm out,new}+o(M),
\]
where \(\mathcal R_{\rm out,new}\) is the original physical signed
exterior after also removing \(\mathcal C_3\times\mathcal C_3\).
No lower bound for this new exterior is asserted.

## 1. Physical support and the genuine paired measure

Both arms pass the .003 gate, and \(Q=0\) on both arms.
Even when their two least angles sum to at most .065, \(W=0\):
the quotient after those first two tags contains the third actual
prime \(\le N^{.080}\), whereas \(W\)'s required quotient floor
is at least \((.555-.065)/3>.163\). Thus on the whole chamber
\(S=H\), literally, and no prime atom or proper prime power is
present on either scored arm. The quotient rank is at least one
since the three tags have product at most \(N^{.240}\), which
cannot itself be central. The two \(N^{.1251}\)-rough arms and
both original mixed chambers cannot occur here. Neither can the
complete two-tag ambient, whose quotient after the two least
primes is \(N^{.110}\)-rough on each side. The one-by-two and
two-by-three orientations are excluded by the exact factor
counts at .080. The squarefree requirement discards only
zero-product rows when either physical score is \(H\).

On each arm partition target-log angles into half-open bins of
width .008 starting at .003, with the final bin shortened to end
at .080. Enumerate nondecreasing triples of bins, allowing bins
to coincide but requiring the actual primes to be distinct and
in increasing order. For a triple \(i\), let \(\tau_i\) be the
sum of its three upper endpoints and \(v_i\) its ordered
three-dimensional volume:
\[
 v_i=\frac{\prod_{\ell=1}^3 |I_{i_\ell}|}{\prod_\nu h_\nu!},
\]
where \(h_\nu\) counts how often a bin \(\nu\) occurs in the triple.
This ordering factor is exact: on a same-bin prime harmonic, the
ordered distinct allocations of the primes have precisely that
multiplicity, and coincident-prime harmonics are negligible
at the polynomial floor. All moment bounds below are uniform
over each full product of three bins before imposing the order.

For two chosen triples \(i,j\), use the **one common physical
measure** with the product of all six actual target-log tag angles
as the weight of each squarefree row. Normalize it by
\(v_i v_j M/L^2\), and call the resulting measure \(\nu\).
Put \(A=H(x)/(L u_1u_2u_3)\) and
\(B=H(y)/(L v_1'v_2'v_3')\), where the denominators use the
three target-log angles on their respective arms
(\(v_\ell'\) denotes a right-arm angle, not a cell volume).
Thus the contribution in units \(v_i v_jM\) is exactly
\(\int AB\,d\nu\).

For a nonnegative real source \(Z\) on one of these arms, with
bounded piecewise continuous weight on its true factor angles,
the ordinary unopposed moment \(m_i(Z)\) satisfies, on the
genuine paired measure,
\[
 k_j m_i(Z)-o(1)\ \le\ \int Z\,d\nu\ \le\
 U_j m_i(Z)+o(1) .                                               \tag{1}
\]
In the reflected orientation exchange \(i,j\).
This is the true product-BV transfer from §2 of the
[one-by-two comparison](OneByTwoTagCredit.md), applied at the
following literal variable levels. Write \(a=.080\) and take
\[
 D_j=\min(4a,\ .498-\tau_j),\qquad s_j=D_j/a,
 \qquad 3.225\le s_j\le4 .
\]
For the right-arm receiver open its genuine three-prime product
\(h\) and linear-sieve the quotient at \(N^a\) using support
\(d\le N^{D_j}\). The actual modulus is \(hd\le N^{.498}\), in
the below-root product-BV range of the fixed-rank true source.
Real angle-product boxes and then bounded step approximation
apply exactly as in the cited transfer. All tested residues are
the true reduced \(N\bmod hd\). Prime exclusions from the
source and named tag products in the local model are
\(1+o(1)\) after the actual positive polynomial floor, and the
target factors remain in \(\mathfrak S(N)\). After omitting
the receiver's named primes from the sieve, restore its actual
roughness and squarefreeness by discarding real \(p^2\) rows for
\(p>N^{.003}\): the positive integer bound
\(O(N^{1-.003}+\sqrt N)\), with fixed divisor-power and bounded
angular multiplicities, suffices. Both sides of (1) refer to
this same squarefree paired measure.

Here \(k_j\) and \(U_j\) are certified lower and upper bounds for
the linear coefficients \(e^{-\gamma_E}f(s_j)/a\) and
\(e^{-\gamma_E}F(s_j)/a\), respectively. For \(3\le s\le4\)
their exact formulas are
\[
 \frac{2\log(s-1)}{as},\qquad
 \frac{2}{as}
   \left(1+\int_0^{s-3}\frac{\log(1+t)}{2+t}\,dt\right).           \tag{2}
\]
At the cap \(s=4\) use the same explicit lower \(.549/a\) and
upper \(.575/a\) as in the previous proofs. Elsewhere the checker
uses a lower positive atanh truncation at \(\log(s-1)\) and an
outward right-endpoint rectangle sum for the increasing integrand
in (2). At the actual row both tag and unmarked primes are shifted
by \(O_J(1/L)\) only when computing the normalized **score** from
the limiting own-log formulas; all physical cutoffs use the
original target-log angles. The errors are uniform on these
positive-floor bounded ranks and are paid by (1).

## 2. Two shifts, and the positive-only high odd tail

For a cell \(i\), use \(m_i(A)\), \(m_i(1)\),
\(m_i((A+d_i)^2)\) for the ordinary unopposed moments and \(P_i\)
for an upper bound for \(m_i(A_+)\). Every quantity is for the
same hard tag and roughness cell, with all actual quotient
ranks counted. For any positive integer shifts \(d_i,d_j\),
write
\[
 AB=(A+d_i)(B+d_j)-d_j A-d_i B-d_i d_j .
\]
The relevant negative first-moment lower in (1) gives
\(-\int A\,d\nu\ge -k_j m_i(A)-(U_j-k_j)P_i-o(1)\); the
corresponding right bound has the labels reversed.
The genuine common mass satisfies
\(\int 1\,d\nu\le \min\{U_jm_i(1),U_i m_j(1)\}+o(1)\).
Cauchy--Schwarz on that **same** physical measure gives this
signed cell lower, up to \(o(1)\):
\[
\begin{split}
 &d_j[-k_jm_i(A)-(U_j-k_j)P_i]
 +d_i[-k_im_j(B)-(U_i-k_i)P_j]\\
 &\qquad-d_i d_j\min\{U_jm_i(1),U_i m_j(1)\}\\
 &\qquad-\sqrt{U_iU_j\,
                 m_i((A+d_i)^2)m_j((B+d_j)^2)} .                \tag{3}
\end{split}
\]
No independence of the true quotient factors is assumed. The
square moments retain the constant \(d_i^2\) or \(d_j^2\) on
the vanishing-score ranks too.

The first, mass, and shifted-square moments come from the
[one-integer four-class identity](OneByTwoTagCredit.md#3-the-unopposed-ordinary-moment-calculation),
using the exact
[third true divided difference](TwoByThreeTagCredit.md#2-the-third-real-finite-difference-and-interval-verification)
on each arm. In particular \(g_3\) is the average of
\(-F'''(s+\sum_\ell u_\ell V_\ell)\) for independent auxiliary
integration variables \(V_\ell\) uniform on \([0,1]\); these
variables describe the exact finite difference of a deterministic
function on the **one** physical integer. The score shift is
on the inclusive subset atom, as in that proof.

Only the following positive tail is needed for \(P_i\).
For rank four the single quotient prime has own-log angle
at least \(.760-O_J(1/L)\), so \(q=\sum s_\ell^2>11/35\) and
the exact rank-four formula is negative. Ranks five, six and
seven are nonpositive everywhere by the actual
[slice formulas](Proof.md#2-the-whole-rough-negative-arm-comparison).
Every even rank at least eight has score zero.
Thus the only possible positive ranks are \(r=9,11,13,15\).
Put \(k=r-3\) and \(T=1-u_1-u_2-u_3\).
The ordinary quotient rank-\(k\) density is
\[
 b_k(T)=\frac1{k!}(\kappa_a^{*k})(T),\qquad
          \kappa_a(dt)=1_{t\ge a}\frac{dt}{t}.
\]
The original high odd rank envelope after division by the
actual three least angles is at most
\[
  1056\,2^{k-2}(T/k)+80640\,2^{k-4}(T/k)^3 .
\]
Indeed, the products of the four or six smallest factors in
the original envelope contain the three true tags. The
arithmetic means of the remaining one or three smallest
quotient angles are bounded by \(T/k\).
All true quotient ranks above 12 are impossible since
\(13\cdot .080>1-.009\).
Multiplying the displayed caps by the respective ordinary
quotient densities and summing gives the required positive
upper. There is no sign claim on the higher odd ranks themselves.

## 3. Whole-chamber replay

In this directory run:

    python3 -OB check_three_by_three_tag_credit.py

The verifier checks the exact prior checker hash and reuses its
audited third-difference setup, four-class integrals, ordinary
density, and outward interval operations, using 100
ordered-separator bins. The new nonnegative rank-density
recursion for the four terms in the positive upper is
\[
 b_1(t)=1_{t\ge a}/t,\qquad
 t b_k(t)=\int_{(k-1)a}^{t-a} b_{k-1}(z)\,dz
 \quad(t\ge ka).
\]
It is evaluated with the outward \(10^{-4}\) density and
predecessor-prefix bins, with zeros below the actual endpoints;
the factorials are already intrinsic to this recursion.
Shifts \(d_i\) are fixed positive integers chosen from the
computed one-arm enclosures in their cells; any such choice
is valid in (3), independent of the reflections and of the
actual rows.

The verifier uses all 220 ordered-bin triples and all 24,310
unordered pairs with repetition of grid triples.
Since the signed bound (3) is symmetric in the two labels,
a different-cell pair is evaluated once with its volume doubled
to count the **two separate physical orientations** on \(NJ\).
An equal-cell pair is evaluated once at its full ordered
six-tag volume, with **no** doubling. This is true also for
asymmetric \(J\): the reflected intervals have equal length,
and every physical row on \(NJ\) has just one ordered pair
of cells. The outward lower in every pair exceeds 770,000 in
the normalized cell units, and the verified sum is
\[
          \sum_{i,j}v_i v_j\,\mathrm{LB}_{ij}
             > .037104 .
\]
All cells, sieve levels and amplitude shifts are fixed before
\(N\to\infty\). This accounts for the entire physical
three-by-three chamber without a favorable-cell selection,
post hoc rank exclusions, or an overlap with prior credits.
