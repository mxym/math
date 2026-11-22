# A literal signed tag union in a cap variant of the wide no-high score

Let \(N\) be an individual large even target, \(J\Subset(0,1)\)
a fixed interval of positive length, \(L=\log N\), \(x\in NJ\),
and \(y=N-x\). Write \(M=|J|N\mathfrak S(N)\) and let
\(\langle V,W\rangle=\sum_{x\in NJ,\,(x,N)=1}V(x)W(y)\).
All physical scores below retain the actual target units.
Use the wide profile of
[the signed semiprime sector](../same_T_semiprime_sector/Proof.md):
\[
      \lambda=.0001,\quad \rho=.999,\quad b=.4996,\quad
      v=.498,\quad k=(1-\lambda)^{-1},\quad F(t)=(1+kt)C(t).
\]
Here \(C\) is any fixed smooth cutoff in \([0,1]\), one
through \(.4992\) and zero from \(b\) onward. Keep the true
prime marks, the full \(P_F\) score, and \(E\) as in that note.
**Change the product cap** in \(B\) as follows. Choose a fixed
smooth \(\vartheta\in[0,1]\), one through \(1.02\) and zero from
\(1.08\) onward. For an integer \(K\ge3\) put
\[
               \sigma=.0002/K,\qquad
               \chi_K(t)=\vartheta((t-v)/\sigma)\quad(t\ge0).
\]
The new \(B_K\) retains the real marks \(N^\lambda<r\le N^v\)
and multiplies each true divisor summand by \(\chi_K(\log(rd)/L)\).
Then \(T=T_K=P_F+E-B_K\). This is not the original cap that
was one through \(.4985\). It is still one on the entire
short divisor box at every \(r\le N^v\). The proof of
[the no-high decomposition](../nearfull_high_vaughan/WideLowNoHighRemainder.md)
works with this cap as well: \(T\) has no support on a prime or on
an integer with any prime factor \(>N^\rho\). On the latter
integers, every surviving low product \(rd\) divides the high
prime's cofactor and hence is \(<N^{1-\rho}\); all other low
terms have profile zero.

Take \(\mathcal R=9/5\) or \(13/10\), set \(\eta=\sigma/\mathcal R\),
and use the true prime bank
\[
          \mathcal P=\{p\text{ prime}:\eta<\log p/L\le\sigma\},
  \qquad \nu(n)=\#\{p\mid n:p\in\mathcal P\},\qquad I(n)=1_{\nu(n)\ge2}.
\]
The union considered here is literal: at least one of the two
integers has two distinct primes in this bank. In particular,
a second prime on the same arm means a different actual prime,
not another valuation of the first one.

**Theorem 1.** Fix \(\mathcal R=9/5\). Choose \(K\) sufficiently
large and fixed, then let \(N\) be any sufficiently large even
target. For the actual, unweighted union,
\[
 \sum_{\substack{x\in NJ,\,(x,N)=1\\I(x)=1\ \text{or}\ I(y)=1}}
                  T(x)T(y)>.068 M.                              \tag{1}
\]
All opponent signs on this union are included. Thus in this
cap variant only the signed comparison with at most one bank
prime on **both** arms remains after the paid union. There is
no bound on the net \(T\times T\) sum.

**Theorem 2 (smaller bank, actual disjoint allocation).**
Take instead \(\mathcal R=13/10\) with the same cap construction,
\(J\subset[1/2,2/3]\), and \(R_J\le.01M\).
Use the actual squarefree semiprime weight \(S\) and allocation
\(hT=-.162 S\) from the cited signed semiprime-sector note,
now with this cap. The sum of the signed tag union and the
disjoint fractional contribution
\[
        \sum_{\substack{x\in NJ,\,(x,N)=1\\I(x)=I(y)=0}}
                        h(x)T(x)T(y)
\]
is \(>.0239M\). The second contribution is itself positive.
No part of the semiprime allocation lying in the tag union
is counted twice. Neither theorem uses the older \(\rho=.518\)
profile.

## 1. Actual factorial tags and modulus ceilings

Put \(W_j(n)=\binom{\nu(n)}{j}\) for \(2\le j\le K\).
Open \(W_j\) by an actual squarefree product \(h_0\mid n\)
of \(j\) bank primes. It is a target unit and
\(h_0\le N^{j\sigma}\le N^{.0002}\).
The positive lower bound \(\eta\) is fixed for each \(K\).
Pay actual selected-prime squares at power saving:
their physical support has \(O(N^{1-\eta})\) integers,
and all original and expanded terms have fixed divisor-power
and log weights. Selected prime products \(h_0\) have
fixed divisor multiplicity per physical integer. For an
integer with two such primes, the true \(\Pi\) and \(E\)
are both zero: a high prime is different from the tags and
its cofactor cannot be a prime power. When \(A_F\) is the
[short log-minus-mark score](../nearfull_high_vaughan/JointGiantEndpointDerivative.md),
we consequently use \(T=A_F-B_K\) on tagged integers,
apart from the true proper-power exceptional support
at \(p^\ell>N^\lambda,\ell\ge2\), again power-small.

Write \(n=h_0 m\) and \(d=a d'\) with \(a\mid h_0\)
and \((d',h_0)=1\). On the paid squarefree-tag complement,
each selected prime is below \(N^\lambda\) and appears
once. Its free log in \(A_F\)'s quotient is exactly canceled
by its literal short prime mark if it has not already
been removed by \(a\). Hence the short profile becomes
\[
         \sum_{a\mid h_0}\mu(a)F(t+\log a/L)
\]
on \(d'\mid m\), with the ordinary log-minus-short-mark
braces on \(m/d'\); the short prime-power label \(j_0\)
excludes \((j_0,h_0)>1\). In \(B_K\) the same shift \(u=\log a/L\)
appears in \(F(t_{d'}(n)+u)\) and
\(\chi_K(\log(rd')/L+u)\). The actual mark \(r>N^\lambda\)
is never a tag. As in
[the two-tag calculation](../nearfull_high_vaughan/WideNoHighTaggedPositive.md),
restore the artificial rows with \((m,h_0)>1\) after opening,
keeping the displayed divisor and short-mark masks on the
free variables. They have the already paid true tag-square
support and fixed divisor bounds.

For \(A_F\) the actual product moduli are \(h_0 d'\) or
\(h_0 d' j_0\), at most \(N^{.4999}\). For \(B_K\) they
are \(h_0 r d'\), at most \(N^{.0002+.499}=N^{.4992}\).
The subset factor \(a\mid h_0\) is not an additional factor
of a modulus. Each exact modulus, including the tag, has
at most a fixed divisor power of allocations for fixed \(K\).
Thus integer CRT for two such opened weights has product
ceiling \(N^{.9998}\); opening target units in the floors
costs \(\tau(N)=N^{o(1)}\). For the actual prime and actual
high-\(E\) opponent use ordinary BV and the
[true product BV](../nearfull_high_vaughan/WholeMarkPrimeTransfer.md)
respectively, at the same strict sub-root ceiling and with
all modulus weights summed globally. Bounded fixed spatial
variations are kept in both the CRT and genuine-prime
models. In particular no assertion about arbitrary over-root
tagged moduli is needed.

## 2. The tag coefficient and both true crosses

In the arithmetic models, complete \(d'\) at
\(S_0=\exp((\log L)^4)\) by the actual unit-masked signed
harmonic, as in
[the short joint calibration](../nearfull_high_vaughan/WideLowNoHighRemainder.md).
For the CRT model this is the \(\mu(d')/d'\) expansion
with the full opposite polynomial modulus and own tag mask.
In the reduced prime models it is the \(\mu(d')/\varphi(d')\)
expansion with all the true units; its zeroth moment is zero
and its first log moment is \(-\mathfrak S(H)\) at even mask \(H\).
For the \(A_F\) prime-power mark \(j_0=p^e\), the actual
\(1/\varphi(d'j_0)\) has the additional multiplier
\(1-1_{p\mid d'}/p\) relative to coprime separation.
Split the shared term \(d'=p d''\): if \(p\le\sqrt{S_0}\)
the signed tail in \(d''\) begins at least at
\(\sqrt{S_0}\); for larger \(p\) use its additional
reciprocal \(p\) for absolute saving. In \(B_K\) the
\(r\mid d'\) term similarly costs a reciprocal prime power
in the model since \(r>N^\lambda\); no physical row
has been discarded on this account. Fixed \(K\) and
smooth profiles permit all the same variations and higher
log moments in these completions. The short \(A_F\)-profile
is identically zero on \(d'\le S_0\) by its affine finite
difference of order at least two. Its signed model is negligible.

For a \(B_K\) shift \(u=\log a/L\), the integrated first-log
coefficient in the completed model, using the actual
\(r\)-log reciprocal harmonic over \((\lambda,v]\), is
\[
 H(u)=k\int_\lambda^v\chi_K(s+u)\,ds+
          (1+ku)(\chi_K(v+u)-\chi_K(\lambda+u)).
\]
Indeed before the \(r\)-harmonic the first coefficient comes
from differentiating both \(F\) and the actual product cap
in \(d'\); the bounded \(n/N\) shift supplies only
\(O_{K,J}(1/L)\) after integration. Put
\(H_0=k(v-\lambda)\), \(H_\chi=\int_0^\infty\chi_K(s)\,ds\)
and \(\beta_K=1-k(H_\chi-v)\).
For the empty shift and every one-tag shift, \(H(u)=H_0\):
\(u\le\sigma\) and \(v+\sigma\) is below the cap transition.
For every shift with two or more tags,
\(u>2\eta\ge(10/9)\sigma>1.08\sigma\), and
\(\lambda+u\) is still in the plateau. Thus
\[
                   H(u)=k(H_\chi-\lambda)-1-2ku .
\]
The complete finite difference of this affine function is
zero. Correcting it at the empty and the \(j\) one-tag
shifts, then taking the minus sign for \(A_F-B_K\), gives
the first-log coefficient on the tagged \(T\)-leg
\[
               D_j(h_0)=(j-1)\beta_K+
                                   2k\,\frac{\log h_0}{L}.       \tag{2}
\]
In particular its sign is positive; crossing on *pairs* of
shifts, not on all nonempty shifts, is essential.

All tag-prime reciprocal corrections at the main term
are \(1+o_K(1)\) uniformly: a tag is removed from both
unit harmonics in the two-leg CRT, and contributes the
factor \(p/(p-2)\) relative to \(1/p\); on an actual prime
opponent the reduced local factor is \(1/(p-2)\).
Every tag is \(\ge N^\eta\). The omitted repeated or
cross-arm tag labels cost a convergent square-reciprocal
tail, and the actual target-prime exclusions are likewise
power-small. On the high \(E\) principal retain the exact
mask \(Nx\) on its source integer \(x=rm\), including
coprimality to \(h_0\). If a tag \(p\mid x\), its
prime-power cofactor has underlying prime \(p\), since
\(r>N^\rho\) is distinct. PNT or Chebyshev at fixed
cofactor gives
\(\sum E(x)c(x)1_{p\mid x}\ll_J N(\log p)/(pL)\),
with \(c(x)=\mathfrak S(Nx)/\mathfrak S(N)\) on units.
The \(j\) such exclusions at fixed \(h_0\) cost
\(O_K(N^{1-\eta})\). Thus the true mean in this model
remains \(k(1-\rho)|J|N+o_K(N)\), using the exact high
affine harmonic and the summable prime-power correction
for \(c(x)-1\). Neither high \(E\) nor \(\Pi\) is
assumed absent on the untagged opponent.

Write \(V=\log\mathcal R\). Summing (2) over the actual
tag harmonics gives
\[
 a_j=\frac{(j-1)\beta_K V^j+
                      2 k j(\sigma-\eta)V^{j-1}}{j!}.
\]
Use PNT for \(\sum_{p\in\mathcal P}1/p=V+o(1)\) and
\(\sum_{p\in\mathcal P}\log p/(pL)=\sigma-\eta+o(1)\);
distinctness is paid by the same square-reciprocal bound.
The CRT first/first term against the untagged
\(A_F-B_K\) has coefficient \(-a_j k(v-\lambda)\),
since the untagged \(A_F\)-coefficient is
\(k-1-k\lambda=0\). The actual \(\Pi\)-cross is
\(-a_j M+o(M)\), by the negative signed log moment in
the prime BV principal. If a spatial \(\Pi_F\)
multiplier is present, remove its \(1+O_J(1/L)\) only
after evaluating that genuine BV principal. The actual
\(E\)-cross is \(-a_j k(1-\rho)M+o(M)\) by the preceding
true product BV model. As \(T=A_F-B_K-\Pi_F+E\) up to
its physical proper-power errors, we obtain
\[
 \begin{split}
       \langle W_jT,T\rangle
           &= a_j k(\rho-v) M+o_K(M),\\
       \langle W_jT,W_\ell T\rangle
           &= a_j a_\ell M+o_K(M)\qquad (2\le j,\ell\le K).
                                                                    \tag{3}
 \end{split}
\]
Reflection gives the first identity in the other
orientation, with the same spatial length.

## 3. Full unweighted tag union with a uniform factorial tail

For a nonnegative integer \(n_0\) the polynomial
\[
          Q_K(n_0)=\sum_{j=2}^K(-1)^j(j-1)\binom{n_0}{j}
\]
equals \(1_{n_0\ge2}\) whenever \(n_0\le K\).
For \(n_0>K\) its difference from the indicator
has absolute value \(O(3^{n_0})\), by the elementary
binomial sum with \(j-1\le n_0\).
Both \(|Q_K(n_0)|\) and the indicator are bounded by
a fixed constant times \(3^{n_0}\). Thus replacing
one or both \(Q_K(\nu)\)'s by the literal \(I\) in
pairings against \(T(x)T(y)\) costs at most a fixed
constant times
\[
    2^{-K}\sum_{x\in NJ,\,(x,N)=1}
          6^{\nu(x)+\nu(y)}|T(x)T(y)|.
                                                                    \tag{4}
\]
This estimate does not assume statistical independence of
bank occurrences. It is important to bound it uniformly as
the cap width changes.

Use the absolute Fourier envelopes for \(\mathcal L\)
and the actual smooth \(B_K\) of
[the true rank pressure, §3](../nearfull_high_vaughan/WideNoHighPrimeRankPressure.md)
and the
[corrected two-leg Henriot bound](../nearfull_high_vaughan/WideJointGiantFiniteAngles.md).
On each arm the envelope has \(L\) times a multiplicative
weight with \(p\)-factor
\(|1-e^{it\log p/L}|+\log p/L\), integrated against the
fixed \(F\) transform and, for \(B_K\), the cap transform;
the cap frequency is added to \(t\). Use the larger
\(6^{\omega(x)+\omega(y)}\) in (4). The corrected
Henriot estimate for the primitive \(x,N-x\) forms and
actual unit weights has factor \(\mathfrak S(N)/L^2\)
times fixed polynomial frequency moments at this fixed
tilt 6. Crucially their degrees and constants depend
on \(J\) and the fixed tilt but not on \(K\).
Extend \(\chi_K\) smoothly with fixed compact negative-side
cutoff. Its fixed-order derivative \(L^1\) norms, and
every fixed weighted transform \(L^1\) norm, grow at
most as fixed powers of \(K\), since the only shrinking
transition is of length \(\asymp K^{-1}\).
The \(F\) norms are fixed. It follows that (4) is
\(O(K^A2^{-K}M)\) with fixed \(A\) and constant.
Each \(K\) is fixed before the large-\(N\) threshold is
taken. This proves a true physical tail, not a tail
only in the factorial main terms.

Define \(D_K=\sum_{j=2}^K(-1)^j(j-1)a_j\).
Equations (3)--(4) price the exact literal union by
inclusion-exclusion, with coefficient
\[
 2k(\rho-v)D_K-D_K^2+O(K^A2^{-K})+o_K(1).
\]
As \(K\to\infty\), \(\sigma-\eta\to0,\ \beta_K\to1\), and
\[
 D_K\longrightarrow D(V)
    =\sum_{j\ge2}\frac{(-1)^j(j-1)^2 V^j}{j!}
    =(1+V+V^2)e^{-V}-1 .
\]
For \(V=\log(9/5)\) the limiting union coefficient is
\(>.0687\), so choose \(K\) sufficiently large, then \(N\).
This proves (1) for the literal union in this cap.

## 4. Exact overlap with the semiprime allocation

The earlier semiprime calculation used only that
\(\chi=1\) on the completed short divisor box at
\(r\le N^v\), that the true \(B\) modulus remains below
the root, and that the mark \(m\le N^{.4979}<N^v\)
is fully capped at \(d=1\) on the selected squarefree
semiprime. All hold with \(\chi_K\).
Thus the same \(\langle S,T\rangle<-.036 M\) and actual
\(hT=-.162 S\), \(0\le h\le1\), apply under \(R_J\le .01M\).
The bank primes cannot divide any true source \(S\)-row.

For the other arm apply the same genuine product BV
calculation of §2 to this actual \(S\)-source, at the
same \(N^{.4999}\) ceiling. Its two factors are the
true \(m,r\) primes, with their exact real sharp
endpoints and the smooth \(\log(x)/\log r\) weight.
Every tag is smaller than both prime factors of \(S\),
so none is lost to the reduced source unit mask.
The calibrated one-variable log moment has minus sign
and retains \(c(x)\). Its actual source mean is
\((J_0+o(1))|J|N\), with
\(J_0=\log(.4979(1-.204)/(.204(1-.4979)))\), as in the
semiprime calculation. This gives
\(\langle S,W_jT\rangle=-J_0 a_j M+o_K(M)\).
The fixed-\(m\) true affine envelope from that note,
now with the same polynomial cap Fourier norms, pays
the factorial tail with \(S|T|\) in place of \(|T T|\)
and the fixed tilt 6. Hence the **actual signed overlap**
is
\[
           \langle hT,IT\rangle
             =.162 J_0 D_K M+O(K^A2^{-K}M)+o_K(M).
\]
This is the entire overlap between the semiprime allocation
and the tag union, since the source arm has no tags.
For \(V=\log(13/10)\), the limiting lower bound for the
remaining allocation is
\(.162(.036-J_0 D(V))M>.00057M\), and the tagged
union itself tends to \(>.02347M\).
Their sum exceeds \(.0239M\) for fixed sufficiently
large \(K\) and sufficiently large \(N\).
For the larger bank in Theorem 1 this calculation does not
justify adding any positive semiprime allocation outside
the union. Neither statement estimates the full complement.

The [exact rational certificate](check.py) checks the
limiting numerical inequalities and the uniform exponent
ceilings used before taking \(K\) large.
