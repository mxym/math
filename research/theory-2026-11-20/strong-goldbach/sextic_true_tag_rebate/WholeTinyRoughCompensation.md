# The whole tiny-factor union of the original rough-compensated sextic

Use the genuine fixed-target \(N,L,J,M,\Pi,R_J\), own-log sextic
\(F,H\), and \(Q_{\rm rough}=[-H]_+1_{P^->N^{.1251}}\) of
[the degree-six proof](Proof.md). In this note use the
**rough-only** score \(G=H+Q_{\rm rough}\). There is no
\(B_0\)-mark subtraction on either arm. Put
\[
 I_b(n)=1_{P^-(n)\le N^b},\qquad
 m(b)=-78b+864b^2-\tfrac{12784}{3}b^3+10640b^4-\tfrac{54432}{5}b^5 .
\]
All pairings have the actual unit condition \((x,N)=1\).
Write \(M_Q^x\) and \(M_Q^y\) for \(\mathfrak S(N)\) times
the true ordinary signed \(Q_{\rm rough}\) masses on
the two central intervals \(NJ,N(1-J)\), with target units.

**Theorem.** For every sufficiently small fixed \(b>0\), through
individual even targets,
\[
\begin{split}
 \langle I_b G,G\rangle&=m(b)M_Q^y+O_J(b^{5/2}M)+o_{J,b}(M),\\
 \langle G,I_b G\rangle&=m(b)M_Q^x+O_J(b^{5/2}M)+o_{J,b}(M),\\
 \langle I_b G,I_b G\rangle&=m(b)^2M+O_J(b^{5/2}M)+o_{J,b}(M).
\end{split}                                                     \tag{1}
\]
The \(O_J\) constants are uniform as the fixed cut \(b\)
decreases. Thus the **entire literal** union where either
arm has some prime factor \(\le N^b\) has signed contribution
at least \(-4.22b M+o_{J,b}(M)\), including every no-hit
source row. Combining this with the rough-only comparison
in [Theorem B of the ordered-mark proof](OrderedMarkCovariance.md)
gives
\[
        R_J\ge (.929-4.22b)M+
                \langle (1-I_b)G,(1-I_b)G\rangle+o_{J,b}(M).    \tag{2}
\]
The surviving arms are the original sharp sextic with
the same actual rough correction, and their true ranks
are now bounded by \(\lfloor1/b\rfloor\).
There is no claim about the sign of that remaining correlation,
no value of the sufficiently small cutoff asserted explicitly, and
no addition of any separately compensated \(B_0\)-mark sectors.

## 1. A true taper narrow enough for both whole small-tag opens

On \(I_b\), \(G=H\) since \(b<.1251\). As throughout,
\(|G|\le |H|\). Use the standard smooth sub-half taper
\(F_\delta\) equal to \(F\) below \(1/2-2\delta\) and zero
from \(1/2-\delta\) onward, with \(\delta=6b\).
Let \(H_\delta\) denote its actual squarefree own-log score,
with the same prime subtraction. A fixed common smooth
left extension is harmless. Because the physical sextic has
a fourth-order half zero, its tapered difference is \(\delta^4\)
times a uniformly compact rescaled \(C^3\) function with
bounded variation of the fourth derivative. Thus
\[
 \int_{\mathbb R}|\widehat F_\delta-\widehat F|(\xi)
                       (2+|\xi|)^{3/2}\,d\xi\ll \delta^{5/2},
 \qquad
 |\widehat F_\delta(\xi)|\ll(2+|\xi|)^{-5}.
\]
The latter has uniform constants: the fourth derivative
jump or total fifth variation of the rescaled difference is
bounded uniformly after rescaling, and the profiles have a common
bounded support. The same bounds apply by bounded spatial Fourier
dilation for literal own-log angles.
Use the **actual** two-form positive envelope in
[the degree-six base, §1](Proof.md) with exponent \(3/2\)
on each arm (strictly above \(4/\pi\)).
For the prime part there is no change between the two profiles;
a prime opponent, if used, is bounded by its true rough indicator
times \(L\). Consequently the actual absolute pairing error
when replacing one sharp factor by its taper is \(O(b^{5/2}M)\)
against the sharp score, the tapered score, or \(G\), even after
multiplying either side by an actual indicator. This compares the
sharp and smooth **scores on both physical integers**, not their
independent angular masses. We do this before expanding any
hit indicator.

Take a true small bank \(B=(N^a,N^b]\) of primes with
\(a=b^C\), where \(C\) is fixed large enough that
\(a^\gamma=O(b^3)\) for the actual small-factor envelope exponent
\(\gamma>0\). Replace \(I_b\) by the real \(B\)-hit at
\(O(a^\gamma M)\) by that envelope.
Expand the hit through its first five inclusion--exclusion
terms. The absolute remainder is at most
\(\binom{\omega_B(n)}6\) exactly. The bounds needed for
the one- and two-remainder terms, uniformly as \(a\) shrinks
with \(b\), are detailed next.

For each product \(h\) of six actual marked primes,
impose its literal divisibility and extract the six genuine
phase factors \(|1-e^{i\xi\log p/L}|\) on this arm.
The corrected two-form envelope on the free quotient lattice
has reciprocal factor \(1/h\); if both remainders are used, impose
the two actual coprime products \(h,h'\), with effective length
\(\asymp_J N/(hh')\). The roots at primes of \(N\) coincide
and the target mask is retained; at primes of either leading
coefficient just one root remains, as in
[the real ordered-mark fiber proof, §1](OrderedMarkCovariance.md).
Since each \(h,h'\le N^{6b}\), all coefficients and lengths
have fixed power slack uniformly for small \(b\).
The lower cutoff \(a\) is not used to estimate the harmonic:
the whole small-prime phase sum satisfies
\[
 \sum_{p\le N^b}\frac{|1-e^{i\xi\log p/L}|}{p}
 \ll \begin{cases}bT,& bT\le1,\\1+\log(bT),&bT>1,\end{cases}
       \qquad T=|\xi|.
\]
Use the prime log harmonic in the first case; in the second
split at \(N^{1/T}\) and use Mertens above it. When the split
is below 2, the full reciprocal sum is \(O(1+\log(bT))\)
since \(T>L/\log 2\).
The positive six-tag Fourier integral is therefore
\[
 \ll\int_0^\infty(1+T)^{-7/2}
       (bT\,1_{bT\le1}+(1+\log(bT))1_{bT>1})^6 dT
       \ll b^{5/2}.
\]
The uniform sharp/tapered Fourier bound of this section gives
the exponent \(-7/2=3/2-5\). Factorial normalization of six
unordered actual labels is available, although not needed for
the power. If both remainders occur, the corresponding true
two-arm absolute integrals factor with bound \(O(b^5M)\);
a single remainder costs \(O(b^{5/2}M)\).
In the product expansion the total propagated error is at most a
constant times \(|E_6(x)|+|E_6(y)|+|E_6(x)E_6(y)|\), because
each actual hit indicator is at most 1. This shows explicitly why
neither the artificial floor nor the other side's huge number
of possible true factors affects the uniform bound.

## 2. Sub-root product-BV for the actual arbitrary score opponent

For the single tiny arm the other score can be a fixed
signed source \(Z\) satisfying \(|Z|\ll |H|\) and, on each
fixed compact positively rough finite-rank region, given
by a bounded piecewise continuous true angular weight
times \(\log n\). This covers \(G\) and its reflection.
Restrict that one physical source to fixed finite rank
and positive polynomial floor, as in
[the actual product transfer in the degree-six base, §1](Proof.md).
For such a cutoff, label its true primes, choose any one
actual prime slot, and group the others into an independent
divisor-bounded coefficient on log-fine product cells.
Use standard true product Bombieri–Vinogradov at every fixed
strict sub-root level; the reduced model retains \((d h,Ny)=1\)
for each genuine source \(y\). It is not applied to an
abstract remainder coefficient without this product structure.
Actual boundary and square errors and weight approximations
are those of the cited compact product transfer.
For the complete \(Z\) remove the cutoff only after
the fixed-\(b\) calculation: the genuine paired and ordinary
rank/floor tails are controlled by its hypothesized sextic
envelope, and any fixed-\(b\) truncation error can be made
arbitrarily small. The uniform \(b\) error of §1 used that
envelope on the *untruncated* source and remains valid.

For a product \(h\) of \(s\) distinct true \(B\)-marks,
\(1\le s\le5\), write \(x=hv\) and open the actual divisor
profile on the quotient. It is
\[
     g_h(t)=\sum_{e\mid h}\mu(e) F_\delta(t+\log e/L).
\]
The real modulus is \(h d\) with \((d,h)=1\);
the receiving arm cannot be prime. Because \(\delta=6b\),
\[
              h d \le N^{5b+.5-\delta}=N^{.5-b}.
\]
Thus there is genuine strict sub-root room at fixed \(b\)
for the full true compact source, with no carrier selection.
Repeated actual labels and the true unit masks are
handled as in the product transfer; the signed reduced model
has \(1/\varphi(h)\) times the \(d\)-harmonic with mask \(Nhy\),
zeroth moment zero and first-log moment
\(-\mathfrak S(Nhy)=-(1+o(1))\mathfrak S(N)\).
At each physical retained source \(y\), omitting any mark
sharing its true factors has power-small reciprocal mass
at the fixed positive floors. The model at a fixed test is
therefore \(-g_h'(0)/\varphi(h)\) times ordinary source mass
\(M_Z=\mathfrak S(N)\sum_y Z(y)\).
All included \(\log e/L\le5b\) lie below the taper.
The true harmonic of a set of \(s\) polynomial-sized
primes gives \(1/s!\) times independent angle
integrals for this **unopposed reciprocal label harmonic**.
Their repeated labels have power-small reciprocal mass,
and were never repeated on a physical subset.

After the actual first-five hit expansion the coefficient is
\[
 -\sum_{s=1}^5 \frac{(-1)^{s+1}}{s!}
 \int_{(a,b]^s}\Delta_{\boldsymbol t}F'(0)\prod_i\frac{dt_i}{t_i},
 \qquad
 \Delta_{\boldsymbol t}=\prod_{i=1}^s(1-\mathcal T_{t_i}),
\]
where \(\mathcal T_t f(v)=f(v+t)\).
Because the fixed derivative is a degree-five polynomial at
these arguments, its \(s\)-fold difference is \(O(\prod t_i)\)
and every order above five is zero.
Extending the lower endpoint from \(a\) to 0 therefore gives
\(O(a)\) error, uniformly for small \(b\).
Evaluate the finite difference integral by formal
compound-Poisson moments with cumulants \(b^j/j\),
equivalently expanding the finite exponential
\(\exp\bigl(\int_0^b(\mathcal T_t-1)dt/t\bigr)\)
on polynomials. The first five moments are
\(b,\tfrac32 b^2,\tfrac{17}{6}b^3,\tfrac{19}{3}b^4,\tfrac{81}{5}b^5\).
Applied to
\(F'(v)=-1-78v+576v^2-1504v^3+1680v^4-672v^5\),
this gives exactly \(m(b)\).
Hence the real sharp single tiny transfer is
\(m(b)M_Z+O(b^{5/2}M)+o_b(M)\).
There is no restriction on the true prime factors of \(Z\)
except the temporary analytic compact truncation already removed.

For \(Z=G\), the whole ordinary signed mass of \(H\) tends
to zero in its normalization. The ordinary \(V_F\) moment
is \(-F'(0)=1\) by actual integer CRT and its first-log
\(\mu(d)/d\) moment, or by the identical unopposed angular
calculation in [the degree-six proof, §4](Proof.md)
with no marks. The true PNT for the subtracted prime part
gives 1 as well. Thus \(M_G=M_Q^y+o(M)\) on that arm.
The same proof on the reflected interval gives the second
formula in (1).

## 3. Both genuine tiny arms at once

After the sharp-to-taper transfer and the actual hit expansions
of §1, both sides have nonempty genuine marked products
\(h,h'\le N^{5b}\) and true short moduli
\(hd,h'd'\le N^{.5-b}\).
These joined moduli are coprime on the target-unit rows,
and each is a unit at \(N\).
The direct CRT floor is power-small:
\((hd)(h'd')\le N^{1-2b}\), with fixed divisor multiplicity
and target opening cost \(N^{o(1)}\). There is no
over-root dispersion argument in this case.
The remaining signed two-variable harmonic uses
\((dd',Nhh')=1\) and \((d,d')=1\).
The actual CRT density is \(\varphi(N)/(Nhh'dd')\)
on compatible tests. Use the two first-log moments
from the genuine joint short calculation
[of the half-zero proof, §3](../halfzero_detector/Proof.md)
with local mask \(Nhh'\).
They give \(\mathfrak S(Nhh')\) in the normalization
with \(\varphi(Nhh')/(Nhh')\), with zero constant moments.
Relative to that normalization the outside factor is
\[
   \frac{\varphi(N)/N}{\varphi(Nhh')/(Nhh')}\frac1{hh'}
                   =\frac1{\varphi(h)\varphi(h')}
\]
because the actual marked groups are coprime and target units.
Here \(\mathfrak S(Nhh')=(1+o(1))\mathfrak S(N)\).
Dropping a cross-shared mark in this *reciprocal model*
has power-small cost (it contributes a square reciprocal);
it was never restored in the physical rows.
The two genuine signed derivative factors are thus the
two ordinary \(m(b)\)'s. Both absolute propagated
remainders, including their product, and the sharp profile
returns have already been bounded in §1.
This proves the last line of (1).

The two ordinary nonnegative \(Q_{\rm rough}\) masses
are both \(<.02688M+o(M)\) by the explicit rank masses
in the degree-six base. The signed contribution on the
whole union is the first two lines of (1) minus the last,
by exact indicator algebra.
Since \(m(b)=-78b+O(b^2)\), it is at least
\[
  -156(.02688)bM-O_J(b^2M)+o_{J,b}(M).
\]
Here \(156(.02688)=4.19328<4.22\). The strict difference
absorbs the quadratic term and uniform Fourier errors for all
sufficiently small fixed \(b\). Combining the union lower with
the genuine rough-only debit \(<.071M\) on \(G\) proves (2),
without appealing to any carrier or any separate narrow-mark
correction.
