# A favorable actual small-factor cross in the compensated quartic detector

Keep the same squarefree own-root [quartic half-zero detector](../halfzero_detector/Proof.md)
\(H\) and [compensated score](../halfzero_detector/CompensatedDebit.md)
\(\widetilde H=H+R+W_1+W_2\), with the same actual supports and
weights. In particular the correction \(R\) is on prime factors
all exceeding \(N^{.145}\), and \(W_1,W_2\) have least factor
\(>N^{.005}\) and second factor \(<N^{.187}\).
As usual \(N\) is an individual large even target,
\(L=\log N\), \(J\Subset(1/3,2/3)\) a fixed interval,
\(x\in NJ,\ y=N-x\), \((x,N)=1\), and \(M=|J|N\mathfrak S(N)\).

For a fixed angular band \(I\) and lower actual factor floor \(c\),
write \(\mathcal Z(I,c)\) for the actual squarefree central \(y\) with
\[
     \widetilde H(y)<0,\qquad P^-(y)>N^c,\qquad
        \log p/L\in I\ \text{for at least one genuine prime }p\mid y .
\]
Write \(Z(I,c;y)=[-\widetilde H(y)]_+1_{\mathcal Z(I,c)}(y)\).
The source keeps its exact compensated magnitude on a tag bank.
The other arm below has no compensation at all. No rank within
the physical range (at most \(1/c\)) is discarded.

**Theorem.** For every sufficiently large fixed integer \(k\), set
\[
 b_0=.004/k,\qquad b_1=.018/k,\qquad I_0=(.012,.076],
                       \qquad I_1=(.019,.058].
\]
On the following **two disjoint actual pair regions**,
\[
\begin{array}{lll}
 \mathcal C_0:\ & P^-(x)\le N^{b_0},&
                         y\in\mathcal Z(I_0,b_0),\\[1mm]
 \mathcal C_1:\ & N^{b_0}<P^-(x)\le N^{b_1},&
                         y\in\mathcal Z(I_1,b_1),
\end{array}
\]
the signed contributions to \(\widetilde H(x)\widetilde H(y)\)
are strictly bigger than \(6b_0M\) and \(4.8(b_1-b_0)M\),
respectively, for all sufficiently large even \(N\).
Together they give \(>.091M/k\) on this orientation.
The reflected regions satisfy the same conclusion and
all four regions are disjoint on the same actual interval.
These are full signed contributions, with arbitrary true
rank and either sign on the small-factor arm. In particular
the larger cut is not added twice on the inner cut.
We do not lower bound the remaining compensated correlation.

There is also a compensation-free subregion of \(\mathcal C_0\):
take its actual source ranks \(3,4,5\), least prime factor in
\((N^{.012},N^{.076}]\), and genuine second least factor
\(>N^{.188}\). There \(H=\widetilde H\) on both arms, and
its signed contribution exceeds \(2b_0M\) per orientation.
This is nested within \(\mathcal C_0\), not an extra term.

## 1. Two real over-root rails for the actual sources

For each source \(Z=Z(I_i,b_i;\cdot)\), use \(Z/L\) as a bounded weight; occurrences of \(L\) in the unnormalized source may
therefore be restored at the end. For every \(A>0\), this source
has arbitrarily high log-power savings for its discrepancy at
the literal reduced residue \(N\) in the respective class below.
For \(I_0\) it covers \(q\le N^{.504}\) with any fixed
divisor-bounded multiplier. For \(I_1\) the tested modulus
is a product \(q=d h\) of two independent divisor-bounded
dyadic coefficients, \(d\le N^{.5}\), \(h\le N^{.018}\).
The reduced model at \(q\) is the genuine source on \((n,q)=1\)
divided by \(\varphi(q)\), with the same real spatial interval.

To prove this, select a true prime in the displayed angular
band as the short slot, and group the other true primes.
If more than one prime factor belongs to this band, assign
each selected label the reciprocal of the actual number in
the band. This is an exact partition with total weight one
for each physical source integer, not a uniqueness assumption
on the marked prime. All prime tuples of a fixed rank can be
labelled symmetrically and, after selecting the true short
prime, divided by the factorial of the remaining rank.
The rank range is fixed after \(b\), all prime lengths
are at least \(N^b\), and actual repeated or target-dividing
source primes may be excluded from the weights or paid by
their power-small counts and fixed divisor weights.
The positive part and the actual compensation are kept
throughout, rather than replacing this source by a negative
score on every prime product in the band.

We invoke [Fouvry, *Autour du théorème de Bombieri–Vinogradov II*,
the main theorem (1.4), Condition (C.1), and Corollaire 1, p. 619](https://www.numdam.org/article/ASENS_1987_4_20_4_617_0.pdf).
Its large scale is \(X=4UV\) when \(U,V\) are the long and
short support parameters; the actual-residue uniformity in
(C.1) and in Corollaire 1 is \(1\le |a|\le X\).
The short input is Siegel–Walfisz in the sense of (1.3).
For \(I_0\) Corollaire 1 has the two modulus rails
\(X^{1/2}V^{1/2}\) and \(X^{4/7}V^{-6/7}\), both with
fixed power slack. If \(V=N^{\beta+o(1)}\) and
\(.012\le\beta\le.076\), both exceed \(N^{.506-o(1)}\).
This proves the required strict room for \(N^{.504}\).

For \(I_1\) use the factorized discrepancy of (1.4) directly.
In its notation \(R\) is the \(d\)-dyad, \(S\) the \(h\)-dyad.
The genuine (C.1) rails are
\[
                    V^{-1}R^{2}S,\qquad V^{3/2}R^{7/4}S^2 .
\]
They are \(<X^{1-\epsilon}\) with strict fixed \(\epsilon>0\):
their upper exponents are
\[
       -.019+2(.5)+.018=.999,\qquad
       \tfrac32(.058)+\tfrac74(.5)+2(.018)=.998 .
\]
There is no assertion that arbitrary modulus weights are
admissible in this wider region. The separation needed for
the actual \(d,h\) coefficients is checked in §2. In either
case the required fixed positive short-slot size is present.

Here are the actual weight and residue details. Partition the
\(p_1\)-slot and the other genuine prime slots into multiplicative
cells of ratio \(1+\Delta\), with \(\Delta=L^{-C}\) to arbitrarily
large fixed \(C\). In each cell put the true short prime into its
own coefficient on \([V,2V]\); group the other true labels and
their product as a single divisor-bounded coefficient on
\([U,2U]\). Freeze continuous angle or central spatial factors
to \(O(\Delta)\) accuracy on that cell. The finite angular partitions are aligned with all the thresholds
of the two real compensating banks (including the quotient floors).
On a given box, each selected short prime's reciprocal multiplicity
is constant. The \(R\) correction vanishes, since a genuine prime
factor is at most \(N^{.076}\). If a \(W_i\)-cell survives, its two
least tags are in their prescribed different cells and its quotient
floor exceeds both cell endpoints. Consequently the tagged labels
are fixed on these boxes: a competing prime in either tag cell
would already violate the actual quotient floor or the required
two distinct cells. The finite rational cell weights are fixed;
taking a minimum with the actual negative magnitude preserves a
Lipschitz angular profile on each such box. The quartic half-zero
pieces and the positive parts are themselves Lipschitz at subset-half
equalities. Thus these are genuine signed or positive angular
coefficients on ordinary product supports. Factors outside a truncated
box but lying exactly on a fixed threshold can be assigned according
to the original half-open conventions on all prime intervals.
For the real product interval keep all
cells lying inside it and discard boundary cells at either
endpoint. For the surviving fine cells, \(UV=(1+O(\Delta))n\)
for products \(n\) in that cell, with \(n>N/3\). Therefore
\[
                     N<4UV=X
\]
literally for all large \(N\). No change of residue to a bounded
integer, and no extension of the stated range of the cited theorem,
is used. There are only a fixed power of \(L\) many cells.
Any discarded boundary is an actual integer strip of length
\(O_J(\Delta N+1)\). For floors and model errors, count its
actual multiplicities by divisor powers of \(n\) and \(N-n\).
Cauchy and the ordinary divisor moments bound its actual
weighted error by \(O_J(N\Delta^{1/2}L^{C_0})\) plus a power-small
error; the reduced contributions satisfy the same upper with
only an extra logarithmic totient harmonic. Increasing \(C\)
and then the requested log saving therefore removes the boundaries.
Names \(C,C_0\) here concern the mesh and divisor bounds, not
new fixed source ranges.

For condition (1.3), the short coefficient is a genuine prime
in a true prefix or interval, with a fixed reduced-class marker
only from genuine target-unit exclusions. For any fixed logarithmic
modulus range, ordinary maximal prime Siegel–Walfisz gives
arbitrary-power log saving in this short variable. Omitting
primes dividing an auxiliary \(d\) (including any actual target
mask) costs at most \(\omega(d)\), which is within the allowed
\(\tau(d)\) factor in (1.3); the target mask separately has
\(O(L)\) prime factors. Uniformity in the finely cut short interval
follows by taking two genuine prefixes. For larger test modulus
\(m\), the trivial \(O(V/m+1)\) bound for its class and
\(O(V/\varphi(m))\) for its reduced model suffice, choosing the
log-power threshold arbitrarily high. The literal source unit
restriction and the short factor's nondivisibility by the target
introduce no extra residue. The large coefficient has only a
divisor-bound requirement, so it is allowed to be a product of
the other true primes. The theorem accepts signed divisor-bounded coefficients
in the precise modulus classes above. Multipliers with fixed
log powers can be absorbed in the arbitrary saving in the
stated applications (the wider class uses separated
coefficients). This proves the claimed discrepancy
estimates after summing the fine cells.

## 2. Exact arithmetic with a fixed set of genuine marked primes

Write \(f_*(t)=P(t)1_{t<1/2}\), with the half-zero polynomial
\[
              P(t)=1-t-11t^2+24t^3-12t^4 .
\]
Use the fixed smooth taper \(f_\delta\) from the half-zero proof.
On rows divisible by any of the nonunit-size genuine marked
products below, the original \(\Pi(x)\) term is exactly zero in
the central interval. The tested arithmetic therefore has no
unknown reflected prime leg.

Let \(B\) be a set of actual prime labels in \((N^a,N^b]\),
where \(0<a<b<.005\) are fixed, and let \(h\) be a product of
\(s\) distinct labels of \(B\). For the source \(I_i\) assume \(s b\le k b_i\).
On the squarefree marked rows \(x=h m\) the exact detector opening
has the function
\[
 g_{\delta,h}(t)=\sum_{e\mid h}\mu(e)
                  f_\delta(t+\log e/L).
\]
A term with genuine \(d\mid m\) tests the actual modulus \(hd\)
at the literal residue \(N\) on \(y=N-x\). Its \(d\) is coprime
to \(h\). The actual modulation \(g_{\delta,h}\) does not make
\(e\) another factor of the tested modulus: it is already in
\(h\). On \(I_0\) all moduli are at most \(N^{.504}\).
On \(I_1\) they are the genuine joined products of §1.
Squareful rows where a selected mark divides \(m\) are
supported on a square \(p^2\) with \(p>N^a\) and have
\(O(N^{1-a+o(1)})\) total weight, also after summing
over the possible actual label subsets of fixed size.
For removal of other nonsquarefree rows and target-log versus
own-log replacement, use the true paired estimates of the
half-zero proof with \(0\le Z(n)\le|H(n)|\).
At fixed \(a,s\), the actual marking multiplicity on any
one row is bounded in terms of \(a,s\) alone, because
\(\omega_B(x)\le1/a\). Those absolute comparisons are
therefore legitimate for each total marked sum. In particular
one can first use the analytic \(L\)-normalized target-log
version of \(f_\delta\), and then return to the exact real
own-root score \(H\) by taking \(\delta\downarrow0\).
No nonunit-size mark lies on a central true prime row.

For \(I_0\), group all opened terms at the actual moduli
\(hd\); the multiplicities are divisor-bounded, so §1 applies.
For \(I_1\) first take a fixed smooth compact real extension of
\(f_\delta\), then use exact Fourier inversion
\[
 g_{\delta,h}(\log d/L)
    =\int_{\mathbb R}\widehat f_\delta(\xi)
          d^{i\xi/L}\prod_{p\mid h}(1-p^{i\xi/L})\,d\xi
\]
with a single consistent Fourier normalization. Keep the
independent \(d\)-cap \(d\le N^{1/2-\delta}\) throughout; outside
it \(g_{\delta,h}\) is identically zero by its nonnegative
shifts. In each true dyad of \(d,h\), after multiplying by
\(\mu(d)\), the \(d\) and \(h\) coefficients are thus
independent and divisor-bounded, the latter by \(2^s\).
No Fourier multiplier enters the short source coefficient.
The \(L^1\) Fourier norm is finite at fixed \(\delta\);
the arbitrary log saving handles all dyads.

To separate these true coefficients, the compatibility
\((d,h)=1\) may first be relaxed in the expanded expression.
The new term tests the **product** \(hd\) (not an lcm)
and therefore has a divisor \(p^2\mid (N-y)\) for some
actual \(p\mid h,\ p>N^a\). Its total physical error is
\(O(N^{1-a+o(1)})\) by fixed divisor multiplicities.
The corresponding positive principal harmonic is at most
\[
 \sum_{\substack{q\le N^{.518}\\ p^2\mid q\text{ for some }p>N^a}}
                          \frac{\tau(q)^{O(1)}}{\varphi(q)}
                                      \ll N^{-a+o(1)} .
\]
This follows by summing \(q=p^2m\) and the prime-square
reciprocals. Thus restore the exact condition after the
application of (C.1), also in the principal. The target-unit
condition \((hd,N)=1\) is kept literally in the dispersion
sum; no independence of the two target-unit masks is needed.
For each actual source value \(y\),
a term's reduced reciprocal is \(1/\varphi(hd)\) with
\((hd,Ny)=1\); all primes of \(h\) are smaller than those
of \(y\). Its \(d\)-harmonic uses the true polynomial-sized
mask \(Nhy\). The zero moment of the signed
\(\mu(d)/\varphi(d)\) harmonic vanishes and its first log
moment is \(-\mathfrak S(Nhy)\), by the same uniform
signed completion as in [the rough union, equation (10)](../halfzero_detector/OneArmRoughDebit.md).
The first derivative of \(g_{\delta,h}\) is bounded
uniformly for fixed \(s,\delta\) (and \(N\)), and the
first-order error after multiplication by \(L\) is
\(O_\delta((\log L)^{C_1}/L)\). The total reciprocal
\(h\)-harmonic is bounded for fixed \(s,a,b\).
All actual primes of \(hy\) are above a fixed positive
power, so uniformly
\(\mathfrak S(Nhy)=(1+o(1))\mathfrak S(N)\).
Omitting the allowed bank primes dividing the actual
target changes their harmonic by \(O(LN^{-a})\).
As a result, putting \(M_Z=\mathfrak S(N)\sum_{y\in N(1-J),(y,N)=1}Z(y)\),
\[
 \sum_{\substack{x\in NJ\\(x,N)=1}}\binom{\omega_B(x)}s
                             H(x)Z(y)
  = -(M_Z+o(M))
          \sum_{\substack{h\ {\rm formed\ from}\ s\
                         {\rm distinct\ primes\ of}\ B\\(h,N)=1}}
                        \frac{g'_{\delta,h}(0)}{\varphi(h)}
       +o(M).                                                 \tag{2}
\]
One can equivalently keep the exact \(M_Z\) and use just one
\(o(M)\) here. The prime arguments \(\log e/L\le .018\)
are below the taper, so this derivative is independent of
\(\delta\) after choosing any \(0<\delta<.1\).
The arbitrarily accurate fixed-\(\delta\) result and the
absolute half-seam transfer, at fixed \(a,s,b\), justify
(2) for the original \(H\), not only for a taper.

## 3. Literal bank occupancy with a uniform score remainder

Take \(b=b_i,\ a=b\exp(-k/100)\), and \(B=(N^a,N^b]\)
on the genuine primes. The identity for the actual indicator is
\[
 1_{\omega_B(x)\ge1}
   =\sum_{s=1}^{k-1}(-1)^{s+1}\binom{\omega_B(x)}s+E_k(x),
 \qquad |E_k(x)|\le\binom{\omega_B(x)}k .
\]
Every actual \(h\) in the truncated sum satisfies \(h\le N^{.018}\).
For \(s\ge4\), the derivative in (2) is zero: it is an
\(s\)-th difference of the cubic \(P'\), evaluated entirely
below the taper. Let \(w=b-a\). By the genuine reciprocal
prime harmonic and literal distinctness of the labels,
the limits of the first three normalized terms (without
the alternating prefactor) are respectively
\[
 \begin{split}
 c_1&=-22w+36(b^2-a^2)-16(b^3-a^3),\\
 c_2&=-72w^2(1-a-b),\\
 c_3&=-48w^3 .
 \end{split}
\]
Indeed the marked derivative with one, two, three angles
\(u,v,t\) is respectively
\(P'(u)-P'(0)\), \(-144uv(1-u-v)\), \(-288uvt\),
including the minus sign from the harmonic.
Use \(du/u\) for each actual prime log-angle, divide by
\(s!\) for the unordered set, and note that repeated
actual labels in the limiting ordered harmonic cost
\(O_{a,s}(N^{-a}L)\). Thus \(c_1-c_2+c_3<-21w\).

For clarity the bound on the remainder is genuinely uniform
as the fixed depth \(k\) is selected. For each actual product
\(h\) of \(k\) labels, put \(x=h m\) so its true
parameter interval has length \(\asymp_J N/h\ge c_JN^{.982}\).
In the positive Fourier envelope from the half-zero proof
extract each selected prime factor \(p\mid h\) once, costing
at most \(2^k\). Reset the weight on powers of these primes
in \(m\) to 1; the remaining multiplicative function has
the same growth constants. Apply the same corrected
two-affine envelope to \(m,N-hm\), keeping the genuine
target units and the bound \(0\le Z(y)\le |H(y)|\).
The uniform coefficient-size and interval conditions have
fixed power slack; the moduli dividing \(h\) supply a single
root instead of two, with a local ratio bounded by
\(\prod_{p\mid h}(1+O(1/p))\le2\) for all sufficiently
large \(N\) after the fixed \(k\). Thus all constants
outside \(2^k\) are independent of \(k,a,b\) for these
choices. In the positive enlargement, the source can be
bounded by the second Fourier envelope of the same fixed
\(H\), rather than by a rank-dependent pointwise constant.
Both Fourier exponents \(c<2\) are available. The negative
source is composite, so the true \(\Pi\) term is zero on it;
enlarge by the positive bound for the product of the two
divisor profiles. This keeps the constants independent of \(k\). The integrated contribution for
one \(h\) is at most \(C_J 2^k M/h\); this holds for the
actual own-log profile by the bounded real Fourier dilation
as in the half-zero proof. Consequently
\[
 \sum |E_k(x)H(x)| Z(y)
   \ \le\ \frac{C_J\,2^k}{k!}
                      \left(\sum_{p\in B}\frac1p\right)^k M
   \ \le\ C_J(3e/100)^k M
\]
for every large \(N\) with \(k\) fixed, using
\(\log(b/a)=k/100\). This is an actual positive remainder,
not an approximate independence assertion.
Replacing \(1_{\omega_B(x)\ge1}\) by
\(1_{P^-(x)\le N^b}\) costs at most \(C_J a^\gamma M\)
for one fixed \(\gamma>0\), by the actual small-factor
bound in the half-zero proof against the same second Fourier envelope. The constant is independent of \(k\).
Both errors are \(o_{k\to\infty}(b M)\) after the large-target
limit.

It follows that the exact oriented contribution with source \(Z\)
is
\[
 \sum_{P^-(x)\le N^b} \widetilde H(x)(-Z(y))
   = \left(22b+o_{k\to\infty}(b)\right)M_Z
                           +o_{k\to\infty}(bM)+o_N(M).       \tag{3}
\]
More precisely the main coefficient is \(-c_1+c_2-c_3\),
with error \(O_J((3e/100)^k+a^\gamma)M+o_N(M)\). Both
\(o_{k\to\infty}\) assertions are after the large-target limit.
For the \(I_1\) source kept fixed at its floor \(b_1\)
this holds both at \(b=b_1\) and at the smaller \(b=b_0\).
In the latter case the same \(I_1\) rails apply with still
more room, and source and weight are not reselected.
The equality uses no correction on the small-factor arm:
its actual least factor is below \(N^{.005}\).
## 4. Actual mass and disjoint signed consequences

For \(I_i\) we may lower the source mass just by using
genuine rank-four rows whose *least* factor is in \(I_i\).
They all meet its geometric masks; on these rows \(R=0\).
Before correction, the ordinary mass of \([-H]_+\)
with all four own angles above \(c_0\) is \((1-4c_0)^3\).
Indeed \(144\prod u_i\) cancels the four factor angles
in the labelled simplex harmonic, leaving the volume of
the shifted simplex. For target-log boundaries use the
harmless \(O_J(1/L)\) shift, with its actual polynomial
factor floors and zero-boundary angular measure.
The actual PNT and reciprocal prime harmonics give
these ordinary counts, removing repeats and target primes.

On the \(I_0\) least-factor slice the uncompensated mass
is \(.525647872M+o(M)\). Subtract the two full ordinary
bank upper masses \(<.146748616M\), \(<.077025550M\) in
[the compensated debit](../halfzero_detector/CompensatedDebit.md).
These upper their literal overlap with these rank-four
rows; they cannot flip the sign after compensation.
This gives \(M_{Z(I_0,b_0)}/M\ge.301873706+o(1)\).

For the \(I_1\) least-factor slice pay only the actual
overlap with the first-least cells whose half-open
index belongs to \(19,\ldots,57\). The uncompensated
mass is
\((1-4\cdot.019)^3-(1-4\cdot.058)^3=.335904192\).
The [exact rational checker](check.py) retains the same
quotient-\(1,2,3\) harmonic mass upper from each old
bank cell in the compensated debit and restricts only
this first-least index. The two resulting ordinary
upper masses are respectively \(<.068376990M\) and
\(<.032632445M\). Therefore in this same actual source
\(M_{Z(I_1,b_1)}/M\ge.234894757+o(1)\).

Apply (3) to the \(I_0\) source to get \(>6b_0M\).
For \(\mathcal C_1\) apply (3) to exactly the same
\(I_1\) source, first with cut \(b_1\) and then
subtracting its evaluation with cut \(b_0\).
This is the literal annulus in the theorem, so the
main coefficient is
\(22(b_1-b_0)+o_{k\to\infty}(b_1)\), not \(22b_1\).
As \(b_1-b_0\) is a fixed positive fraction of \(b_1\),
the errors are absorbed for \(k\) large, and the
rank-four lower gives \(>4.8(b_1-b_0)M\).
The two lower bounds sum to \(>.091M/k\).

For the explicitly uncorrected subregion use the same proof
with \(Z\) restricted to those negative ranks \(3,4,5\)
and the stated true first and second least factors.
There \(W_1,W_2\) vanish by the second least floor, and \(R\)
vanishes by the first least bound. Its rank-four mass alone is
\[
       12\int_{.012}^{.076}(1-u-3\cdot .188)^2\,du
                         =.118276096 .
\]
The unique small factor gives four choices in the labelled
simplex and the three other angles have cross-section area
\((1-u-3\cdot .188)^2/2\).
The other two negative ranks of this subregion also have
positive ordinary mass independently. One may use an open
giant rank-three angle box with second angle in \((.19,.24)\),
or a rank-five box with four other distinct angles above
\(.188\), where the known scores are strictly negative.
These actual rank sources can each be used separately in
(3), taking \(k\) large enough to absorb its error.
The two base orientations are disjoint by the cut \(b_0\),
and the two annular orientations by the cut \(b_1\).
Neither annular orientation can overlap either base
orientation: both annular arms have least factor \(>N^{b_0}\).
All signs are kept inside each of these actual regions.
