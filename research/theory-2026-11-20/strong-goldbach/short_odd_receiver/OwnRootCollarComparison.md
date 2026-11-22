# Literal odd-rank comparison for true near-half prime-factor sources

Use the same fixed even target \(N\), central interval \(J\), actual target
units, actual prime weight \(\Pi(n)=1_{n\ {\rm prime}}\log n\), and
\(M=|J|N\mathfrak S(N)\) as in the
[short odd receiver](Proof.md). Pair \(x+y=N\) with \(x\in NJ\).
Keep its exact profiles and actual score \(H=P_F-B-C_\psi\),
including all real cutoffs. Put \(L=\log N\), \(k=(1-.0001)^{-1}\),
\(v=.498\), \(\kappa_n=\log(N/n)/L\), and
\[
 \Pi_F(n)=(1+k\kappa_n)\Pi(n),\qquad
 \alpha=1-.001k,\qquad
 g_n(d)=\log n+k\kappa_n\log(n/d).
\]
The symbol \(C\) below is the cutoff in \(F(t)=(1+kt)C(t)\), distinct
from the compensator \(C_\psi\). Define
\[
 \begin{split}
 U(n)&=\sum_{d\mid n}\mu(d)C(\log(dN/n)/L)g_n(d),\\
 W(n)&=U(n)-\Pi_F(n)-H(n),\\
 O(n)&=\mu^2(n)\log n\sum_{\substack{d\mid n\\d<\sqrt n}}\mu(d)-\Pi(n),\\
 \mathcal C(n)&=\mu^2(n)\left\{
       \sum_{\substack{d\mid n\\d<\sqrt n}}\mu(d)g_n(d)-U(n)+W(n)
                                      \right\}.
 \end{split}                                                     \tag{1}
\]
The inequality \(d<\sqrt n\) is literal. In particular the right arm of
\(O\) is not cut at any fixed monotone cap below the square root.

**Theorem.** At each large even target, all these scores have the following
same-profile properties.

1. On squarefree central \(n\), \(W\) is exactly a sum over actual divisors
   \(N^{.498}<q\le N^{.4997}\). The score \(\mathcal C\) is exactly supported
   on genuine divisor labels \(N^{.498}<q<\sqrt n\), with no condition on
   the least prime factor. The following are true bilateral comparisons:
   \[
    \langle W,W\rangle=\alpha^2 M+o(M),\qquad
    \langle W,H\rangle=\langle H,W\rangle=\alpha(1-\alpha)M+o(M),\qquad
    \langle W,\Pi\rangle=\langle\Pi,W\rangle=-\alpha M+o(M).
                                                               \tag{2}
   \]
   The nonsquarefree physical arms can be discarded in (2) at \(o(M)\)
   absolute cost.

2. There are two actual, disjoint first-arm sources. The first,
   \(\mathcal X_3\), consists of the central genuine triprimes
   \(x=q a b\), with \(q,a,b\) prime and their target-log exponents
   in respectively
   \[
          [.4922,.4976],\qquad [.23,.248],\qquad [.254,.28].
                                                               \tag{3}
   \]
   The second, \(\mathcal X_{\rm odd}\), uses six nonoverlapping prime
   \(q\)-cells \([a_i,b_i)\) of width \(.0009\), with
   \[
          a_i=.4922+.0009i,\qquad b_i=a_i+.0009,\qquad
          \eta_i=.50225-a_i,\qquad 0\le i\le5.
   \]
   On cell \(i\) keep the exact factorization \(x=q m\), with \(m\)
   squarefree, \(P^-(m)>N^{\eta_i}\), and \(\omega(m)\) even and
   at least four. This is a whole odd rank-at-least-five source:
   no cutoff further reduces the genuine ranks permitted by these
   factor sizes. In both sources \(q\) is uniquely determined.
   Let \(Z\) be the indicator of either source times
   \((2+k\kappa_x)\log x\), and put
   \(M_Z=\mathfrak S(N)\sum_{x\in NJ,(x,N)=1} Z(x)\).
   Fixed subwindows and bounded nonnegative smooth weights in the
   three angles of (3), or in the \(q\)-angle of the second source,
   and in \(x/N\), are also permitted. Then
   \[
       \langle Z,O\rangle=-\langle Z,\Pi\rangle+o(M),
       \qquad
       \langle Z,\mathcal C\rangle=-\alpha M_Z+o(M).
                                                               \tag{4}
   \]
   For the unweighted sources \(M_{Z_3}\asymp_J M\) and
   \(M_{Z_{\rm odd}}>.579M\) for all large \(N\); these are ordinary
   source masses, not signed joint bounds for the uncorrected \(H\).
   On each source the exact value of \(H(x)\) is
   \(-(2+k\kappa_x)\log x\). Thus the actual pairing of its negative
   score with the entire \(O\)-arm, including all higher ranks, is
   \[
          \sum_{x\ {\rm in\ the\ source},\ (x,N)=1}H(x)O(N-x)
                 =\langle Z,\Pi\rangle+o(M)\ \ge -o(M)           \tag{5}
   \]
   for the unweighted choice (insert the same weight on the left
   if using weighted sources). The \(O\)-arm is identically zero
   except at squarefree odd ranks at least three with all prime
   factors below own half. In particular (5) pays every adverse
   opposite odd rank in the complete signed own-root comparison.
   The genuine \(H\) on the opposite arm still differs by its
   actual calibrated collar term in (4). No absolute bound for
   that collar, sign for \(H\times H\), or estimate for all
   stable odd perspectives is asserted.

## 1. Exact physical collar and short-variable moments

Write \(Z_H=A_F-B-C_\psi\) as in the short odd receiver. Except on the
physical divisibility by a proper prime power \(>N^{.0001}\),
\(H=Z_H-\Pi_F\). As there, such rows have \(o(M)\) effect after the fixed
divisor-power envelopes. On squarefree \(n\) the equation holds exactly.
Aggregate \(U-A_F+B+C_\psi\) on a squarefree row by its actual divisor
\(q\mid n\). Put \(s=\log q/L\), \(u=\log n/L=1-\kappa_n\) and
\(u_r=\log r/L\) for each prime \(r\mid q\). After the factor
\(L\mu(q)\), the coefficient is
\[
 \begin{split}
 &C(s+\kappa_n)[u+k\kappa_n(u-s)]-(u-s)F(s+\kappa_n)\\[-2pt]
 &\ -\sum_{r\mid q}u_r F(s+\kappa_n-u_r)
       \{1_{r\le N^{.0001}}+\chi(s)1_{N^{.0001}<r\le N^v}\}\\
 &\ +k\psi(s)\sum_{r\mid q}(u_r-u_r^2).
 \end{split}                                                     \tag{6}
\]
Here the short \(j\)-mark of \(A_F\) is an actual prime on this
squarefree row. In the signed grouping of \(B\) the sign changes because
its actual divisor is \(q/r\). If \(s\le v\) all three profiles are on
their plateau or affine interval, and the brace is one at every \(r\).
The polynomial in (6) is zero, using \(\sum_{r\mid q}u_r=s\).
Indeed omitting the \(k\kappa_n(u-s)\) term in its first line would have
left \(-k\kappa_n(u-s)\). If \(s>.4997\), there is no nonzero term:
\(C,F\) are supported at most through \(.4996\), \(\psi\) and \(\chi\)
through \(.4992\) and \(.499\), while a genuine short \(j\) can add at
most \(.0001\) to the divisor angle. This proves the assertion about
physical \(W\). In the \(d\)-sum difference in (1), \(C=1\) and
\(d<\sqrt n\) for \(d\le N^v\), while the supported \(U\)-divisors and
all labels of \(W\) are \(<\sqrt n\) for large \(N\).
This proves the exact support of \(\mathcal C\). Its squarefree factor is
part of its definition, not a deletion after a sharp estimate.

For the signed moments, \(U\) has actual modulus \(d\le N^{.4996}\).
All its mixed compositions with \(A_F,B,C_\psi\) have the same strict
short-modulus CRT margins as in the short odd receiver, with
\([q,e^2]\) and the actual squarefree expansion on a \(C_\psi\)-leg.
These are physical moduli with fixed divisor-power multiplicities.
One can therefore use precisely the local simultaneous first moments
and signed completions in §§1–2 of that calculation. At fixed \(n\),
the \(U\)-profile is affine for \(d\le S=\exp((\log L)^4)\); its zeroth
moment vanishes, and its coefficient of \(\log d\) is
\(-k\kappa_n=O_J(1/L)\). Completing that variable first with the
polynomial mask of the actual opposite modulus gives the same
arbitrary-log tail. The opposite leg has after its signed completion a
bounded first coefficient (including its positive marked reciprocal
harmonic); thus this \(1/L\) is not lost. The same pointwise harmonic on
an actual genuine prime cross applies with ordinary weighted BV.
Consequently
\[
 \langle U,U\rangle,\ \langle U,Z_H\rangle,\ \langle Z_H,U\rangle,\
 \langle U,\Pi_F\rangle,\ \langle\Pi_F,U\rangle=o(M).
\]
The short odd receiver gives
\(\langle H,\Pi_F\rangle=\langle\Pi_F,H\rangle
=\alpha M-R_J+o(M)\) and
\(\langle H,H\rangle=R_J+(\alpha^2-2\alpha)M+o(M)\).
The genuine binary atom is \(O_J(M)\) by the upper sieve, so
\(\langle\Pi_F,\Pi_F\rangle=R_J+o(M)\).
Substitution of \(W=U-\Pi_F-H\) gives all the signs in (2).

For the nonsquarefree absolute qualification, \(U\) has the same
Fourier envelope as the
[wide finite-angle bound](../nearfull_high_vaughan/WideJointGiantFiniteAngles.md):
the unmarked summands give \(\prod_{p\mid n}|1-e^{i\xi u_p}|\);
a \(\log d\) term is the sum with one selected \(p\mid d\) and obtains
the upper
\[
 L\prod_{p\mid n}(|1-e^{i\xi u_p}|+u_p)
\]
after allocating its true \(u_p\) to the corresponding degree-one term.
The physical phase \(e^{i\xi\kappa_n}\) has modulus one, and the outside
coefficients of \(\log n\) and \(\log d\) are bounded. The fixed
smooth profiles and the actual bound for \(H\) therefore give the
true two-leg Henriot envelope and the true \(O(\eta M)\) bound
with one actual prime \(\le N^\eta\) extracted at any valuation.
Outside that set, nonsquarefree rows are \(O(N^{1-\eta})\) and are
power-small with the actual divisor weights. Let \(\eta\) decrease
after fixing the profiles and taking \(N\) large. The same argument
for a prime arm permits replacement of \(\Pi_F\) by \(\Pi\) at
\(o(M)\) in (2).

## 2. Over-root distribution of the real prime-product long factor

Write \(x=q m\), with \(m=ab\) on \(\mathcal X_3\).
For \(\mathcal X_{\rm odd}\), on the \(i\)-th cell the
cofactor \(\omega(m)\) ranges through a fixed finite set,
since each actual prime factor exceeds \(N^{\eta_i}\) with
\(\eta_i\ge .00555\). We can write the \(m\)-coefficient by
summing over its sorted distinct true prime factors at each
allowed even rank. No replacement of its parity by an
independent sign is used. The largest prime factor of \(m\)
is at most \(N^{.5078-3\cdot.00555}=N^{.49115}<q\) on this
second source, so \(q\) is unique and the disjoint half-open
cells count every physical row once. It is also unique
on \(\mathcal X_3\), by the three disjoint intervals.
The **long** slot is \(m\) in both cases: on the central
physical window its exponent is in \([.5023,.5079]\) for
large \(N\). After independent dyadic subdivision we may
impose that slightly enlarged \(m\)-range without changing
an actual row.

This \(m\)-coefficient has Siegel--Walfisz, including arbitrary
auxiliary unit masks, at its own dyadic scale \(Y\). For each
allowed rank write \(m=h b\), with \(b\) the last genuine
prime and \(h\) the product of the other fixed genuine prime
labels. On \(\mathcal X_3\), \(h=a\). For a reduced class
modulo \(j\) the actual \(h\) must be a unit and the class
of \(b\) is determined via its inverse. The \(b\)-interval,
including the last-prime ordering and the actual real
\(m\)-window, has prefixes of upper scale \(O(Y/h)\);
on a nonempty interval \(Y/h\gg N^{c_0}\) for one fixed
\(c_0>0\), since all source factors exceed \(N^{.00555}\).
For \(j\le L^B\), prime Siegel--Walfisz in those true prefixes
gives \(O_A((Y/h)L^{-A})\) at arbitrary accuracy. Removing
a forbidden true \(b\) dividing an auxiliary mask costs
at most its number of distinct prime factors times fixed
log powers; the auxiliary unit restrictions on \(h\)
stay exact. The same applies to the actual target mask.
The harmonic sum over the possible \(h\)'s, even
allowing ordered prime labels, is bounded by a fixed
power of \(\sum_{N^{.00555}<p\le N}1/p=O(1)\).
Thus the first error sums to \(O_A(YL^{-A})\), and
the auxiliary exclusion error sums to \(O(Y N^{-c_0})\)
times the allowed auxiliary divisor factor and log powers
(using \(h\ll Y N^{-c_0}\)). The number of ranks
and the number of cells are fixed. For larger \(j\) the
trivial \(O(Y/(hj)+1)\) bound per actual \(h\), along with
the same harmonic estimate and \(h\ll YN^{-c_0}\), proves
the required large-\(j\) form. The corresponding reduced
means have the same bounds with \(1/\varphi(j)\). This
proves the auxiliary-mask form of SW from the primary
Fouvry--Radziwiłł definition, not just equidistribution
with no coprimality constraints. Separated smooth and
normalized log weights have the same property by partial
summation. Fixed joint smooth weights on the three prime
angles of \(\mathcal X_3\) are separated to arbitrary log
accuracy by log-fine meshes or smooth Fourier expansion.

Below \(N^{.4996}\) use the genuine ordinary product distribution of
[the full one-mark transfer, §1](../nearfull_high_vaughan/WholeMarkPrimeTransfer.md),
in which \(q\) is a genuine prime and \(m\) has a divisor-bounded
coefficient. From \(N^{.4996}\) to \(N^{.5010}\) use
[Fouvry--Radziwiłł, Theorem 1.1](https://arxiv.org/abs/1812.00562v2)
with the longer Siegel--Walfisz slot \(m\), the other divisor-bounded
slot \(q\), and the actual reduced residue \(N\). Its fixed-aspect
size allowance for this residue is exactly that used in
[the signed asymmetric block, §1](../nearfull_high_vaughan/AsymmetricGiantMarkDispersion.md);
it depends on scales and divisors, not on the special form of the long
coefficient beyond Siegel--Walfisz. The strict exponent inequalities are
\[
           (56\cdot .5079-17)/23<.4996,\qquad .5010<.5023.
\]
These are absolute summed discrepancies over the displayed true
moduli, not a separate error for each factorization of a modulus.
They allow fixed divisor powers by the standard interpolation
with the crossed divisor moments: an actual modulus divides
\(N-x\) and all its possible decompositions have fixed divisor-power
multiplicity. Reduced errors have only the extra positive totient
harmonic. Fixed central spatial arguments and product endpoints can
be reconstructed with polynomially many log-fine cells as in that
proof; the physical sum on each discarded thin boundary is bounded
by Cauchy and the same divisor moments. The actual reduced model
throughout retains \((x,Q)=1\) at a true modulus \(Q\).

## 3. The sharp own-root term and its real signed consequence

Open the genuine squarefree factor in \(O+\Pi\) by
\(\mu^2(y)=\sum_{e^2\mid y}\mu(e)\) and initially retain
\(e\le N^{.0004}\). The physical \(e\)-tail is supported on
\(O(N^{1-.0004})\) integers and has power-small effect with the
divisor weights. The actual modulus is \([d,e^2]\), whose maximum
is \(N^{.5008}\). It is coprime to \(N\) on any true row. Its total
multiplicity is at most a fixed divisor power at every modulus.
The spatial prefix after opening \(d\) is the actual
\(x<N-d^2\). To retain this endpoint, use a common mesh of width
\(\Delta N\), \(\Delta=L^{-A_1}\), in \(x\). A misclassified
physical \(d\) has \(|y-d^2|\ll\Delta N\) and \(d\asymp_J\sqrt N\).
Writing \(y=d a_0\) counts \(O_J(\Delta N+\sqrt N)\) actual pairs
\(d,a_0\). Cauchy, ordinary crossed divisor moments, and the fact that the
simultaneous \(e^2\mid y\) labels have fixed divisor multiplicity
pay this edge with arbitrary log saving after \(A_1\) is chosen.
Even in the reduced model the endpoint toll is small: for any
squarefree \(d\) the positive sum over squarefree \(e\) of
\(1/\varphi([d,e^2])\) is at most \(L^{O(1)}/d\), by the factors
\(1+1/p\) at \(p\mid d\) and \(1+1/(p(p-1))\) elsewhere, after the
outside \(1/\varphi(d)\). Summing \(d\) in the geometric edge
interval costs \(L^{O(1)}(\Delta+N^{-1/2})\).
This permits a literal moving own-root cutoff, not only a fixed
power in its place. Apply the discrepancies of §2 within the
common cells, then restore this cutoff and real log weights.

For each fixed actual \(x,y,e\) in the reduced model, keep its full
mask \(H_e=Nxe\). We only need \((e,Nx)=1\).
For \(d=d_1d_2\) with \(d_1\mid e\), \((d_2,e)=1\) the factor is
exactly \(1/\{\varphi(e^2)\varphi(d_2)\}\), not independent
local densities at shared primes. Thus the inner signed sum is
\[
 \frac{1}{\varphi(e^2)}
     \sum_{d_1\mid e}\mu(d_1)
          \sum_{\substack{d_2<\sqrt y/d_1\\(d_2,H_e)=1}}
                                  \frac{\mu(d_2)}{\varphi(d_2)} .
                                                               \tag{7}
\]
The innermost sum is arbitrary-log small by the uniform signed
harmonic of the full one-mark transfer, because each cutoff
is \(\gg_J N^{.4996}\) and \(H_e\le N^{2.001}\).
No source factor is removed from this mask.
The positive \(\sum_e\tau(e)/\varphi(e^2)\) converges, and
\(\sum_{x\in NJ}Z(x)=O_J(N)\) by elementary prime counting
and bounded reciprocals in the three fixed power ranges.
The factor \(\log y\) costs one fixed log power. This proves
the first equation of (4).

The same proof applies to the normalization term
\[
   Q(n)=\mu^2(n)k\kappa_n
          \sum_{\substack{d\mid n\\d<\sqrt n}}\mu(d)\log(n/d)
                         -(\Pi_F(n)-\Pi(n)).
\]
In (7) the additional \(\log d_1\) is accompanied by the negligible
zeroth moment; the first log moment for \(d_2\) is
\(-\mathfrak S(H_e)\), times \(O_J(1/L)\). Uniform
\(\mathfrak S(H_e)\ll(\log L)^{O(1)}\) and the same absolutely
convergent \(e\)-majorant give \(o(M)\). The genuine prime change
is \(O(1/L)\langle Z,\Pi\rangle=o(M)\). Here
\(\langle Z,\Pi\rangle\ll_J M\) follows, for example, by the
positive two-form sieve with \(x\) polynomially rough on this
actual source and \(y\) prime. Thus \(\langle Z,Q\rangle=o(M)\);
no absolute estimate on the normalization at each sharp row is used.

The actual \(H\)-calibration also works with \(Z\) as the genuine
source, at its original strictly short moduli:
\[
                 \langle Z,H\rangle
                     =\alpha M_Z-\langle Z,\Pi\rangle+o(M).
                                                               \tag{8}
\]
Indeed apply §2's product distribution to the literal \(Z_H\)
expansion in the short odd receiver. At each fixed observed \(x\)
the completed one-variable model has mask \(Nx\), with the same
squarefree local corrections and distinguished-mark moments
computed there. Its leading coefficient is
\(\alpha\mathfrak S(Nx)\); all actual factors of the source exceed
\(N^{.00555}\), so this is
\((\alpha+o(1))\mathfrak S(N)\) uniformly. The prime term is
literally \(\Pi_F\), replaced as above only after applying the
actual sieve bound. The nonsquarefree \(y\) part of (8) costs
\(o(M)\) in absolute value, using the fixed smooth \(H\)-envelope
and \(Z(x)\ll L\,1_{P^-(x)\ge N^{.00555}}\) in the actual
two-form bound as in §1. The rough multiplicative upper on
the source leg has bounded Euler cost; in particular it does
not require an unproved two-prime estimate for the source at
a fixed complementary divisor.

By (1), on every squarefree \(n\),
\(\mathcal C(n)=O(n)-H(n)+Q(n)\). On nonsquarefree \(n\),
\(O,Q,\mathcal C\) all vanish, and the residual \(H\)-part
paired with \(Z\) has just been paid. Combining (7)--(8)
therefore proves the second equation of (4).

Finally, among the actual proper divisors of a squarefree even-rank
integer, complementary subsets have the same sign, so the short
Möbius sum is half the full zero sum. There is no square-root equality.
If a composite squarefree integer has a genuine prime above own half,
the short divisors are all divisors of its nontrivial complementary
factor, and again their signed sum is zero. The central prime is
removed exactly by \(\Pi\). On the source in (3), all true proper subset sums are outside
the transition band of the short odd receiver: the only short
nonempty subsets are the three singletons. Their signed angle
sum is \(-u\), \(u=\log x/L\), and their signed count together
with the empty subset is \(-2\).

On \(\mathcal X_{\rm odd}\) write \(\theta=\log q/L\) and
\(t_m=u-\theta\). Every proper cofactor divisor has angle at
most
\[
 t_m-\eta_i \le .49775-\kappa_x-(\theta-a_i).
\]
Its own-log angle is thus at most \(.49775\); a smaller
number than \(.4978\) remains after dividing by \(u=1-\kappa_x\).
The full \(m\)-angle divided by \(u\) is at least
\(.5024-o(1)>.5022\). The mark \(q\) itself is short with
own-log angle at most \(.4976+o(1)<.4978\); every product
of \(q\) times a nontrivial divisor of \(m\) has angle
at least \(\theta+\eta_i\ge.50225\).
Consequently the genuine short subset family is all
proper divisors of \(m\), together with \(q\) alone.
They are stable, all factors exceed \(N^{.0001}\),
and neither score has a high-mark exception. Since
\(\mu(m)=+1\), and the full \(\mu(d)\) and
\(\mu(d)\log d\) divisor sums of the squarefree composite
\(m\) are both zero, this same subset family has
signed count \(-2\) and signed angle sum
\(-t_m-\theta=-u\). Applying the exact stable
coefficient \(u(1+k\kappa_x)+k(u-1)t_A\) per subset
from the short odd receiver therefore gives
\[
                       H(x)=-(2+k\kappa_x)\log x
\]
on both sources, with no approximation to a sharp score.
This proves (5). At no point do we use a bound on
the actual joint occurrence of different factor ranks.

## 4. The ordinary mass of the whole odd source

The triprime lower \(M_{Z_3}\gg_J M\) follows from PNT on any
interior angular box in (3) where the three true factors can
range over the central products. The matching upper follows
from the bounded prime reciprocal sums in the prescribed
ranges. For the second source we give a fixed reproducible
constant. Put \(s=1-\theta\). For \(u\ge 1\), use the genuine
fixed-rank harmonic functions
\[
 J_1(u)=1,\qquad
 J_j(u)=\frac{u}{j!}
   \int_{\substack{t_\ell\ge1\ (1\le\ell\le j)\\
                   t_1+\cdots+t_j=u}}
        \frac{dt_1\cdots dt_{j-1}}{t_1\cdots t_j}
   \quad(j\ge2),
\]
with value zero below the respective support.
Ordinary PNT in the last true prime and harmonic PNT in the
others give the \(j\)-factor density \(J_j(s/\eta_i)/(s L)\)
for the cofactor in its actual interval of length
\(|J|N/q\), at each real \(\theta\) in the \(i\)-th cell.
For clarity the angular integral appears by fixing \(j-1\)
genuine factors (and using PNT in a last prime on a fixed
relative interval), then dividing the ordered count by \(j!\).
On each fixed positive floor all slots have polynomial
sizes; the ordinary harmonic Riemann sums converge uniformly
in the compact \(s\)-range by subdivision and a boundary
layer of arbitrarily small angular width. Any repeated
large prime or target prime in the cofactor can be
removed at power-small cost: relative to its scale \(N/q\)
the respective absolute counts are bounded by
\(\sum_{p>N^{\eta_i}}1/p^2\) and
\(\sum_{p\mid N,\ p>N^{\eta_i}}1/p\).
The omitted outer primes dividing \(N\) likewise have
power-small reciprocal harmonic. All ranks are bounded
at each of the six fixed floors, so the errors may be combined
before integrating the actual outer \(q\) and its real endpoints.
This is an ordinary source count; an asymptotic for any
opposite factorization is not being used.

The identity
\(J_j'(u)=J_{j-1}(u-1)/(u-1)\) for \(j\ge2\) follows by
writing \(u=\sum t_\ell\) in the integrand and taking one
boundary derivative of the resulting symmetric cumulative
\((j-1)\)-variable integral. In particular \(J_2(u)=\log(u-1)\)
for \(u\ge2\), and these delay equations with their initial
conditions give
\[
 \sum_{j\ge1}J_j(u)=u\omega_{\rm B}(u),\qquad
 \sum_{j\ge1}(-1)^{j+1}J_j(u)=\rho_{\rm D}(u-1).
\]
Here \(\omega_{\rm B}\) is Buchstab and \(\rho_{\rm D}\)
is Dickman; these are finite identities in the displayed
range, and \(0\le \rho_{\rm D}\le1\).
For an elementary uniform floor, \(\omega_{\rm B}(u)\ge.55\)
for \(u\ge3\): on \([2,3]\),
\(u\omega_{\rm B}(u)=1+\log(u-1)\), which by concavity gives
\(\omega_{\rm B}\ge.50\) on \([2,2.5]\) and
\(\omega_{\rm B}\ge.55\) on \([2.5,3]\).
On \([3,3.5]\), the delay equation gives
\(u\omega_{\rm B}(u)\ge1+\log2+.50(u-3)>.55u\).
On \([3.5,4]\) the delayed floor is already \(.55\);
induct in intervals of length one from there. The
elementary bounds \(\log(3/2)>.4\) and \(\log2>.69\)
suffice at the endpoints (e.g. use the positive
odd-power series for \(\log((1+t)/(1-t))\)).

It follows that
\[
 \begin{split}
 \lim_{N\to\infty}\frac{M_{Z_{\rm odd}}}{M}
 &=\sum_{i=0}^5\int_{a_i}^{b_i}\frac{2}{\theta s}
    \left\{\frac{(s/\eta_i)\omega_{\rm B}(s/\eta_i)
                          -\rho_{\rm D}(s/\eta_i-1)}2
                              -\log(s/\eta_i-1)\right\}d\theta\\
 &\ge 8\cdot .0009 \sum_{i=0}^5
        \left\{.275(1-b_i)/\eta_i-5.11\right\}\\
 &=\frac{23075750579607}{39827304125000}>.57939 .
 \end{split}
\]
In the inequality \(s/\eta_i<100\), \(\log100<4.61\),
\(2/(\theta s)\ge8\), and each resulting bracket is positive.
The log upper can be checked with the positive exponential
partial sum \(\sum_{j=0}^{11}4.61^j/j!>100\).
The factor \(2\) in the integral is the actual
\((2+k\kappa_x)\log x=(2+o(1))L\) on this central
source. The spatial normalization is the same \(M\)
throughout.
