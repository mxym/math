# A disjoint second-least-prime rebate for the same half-zero score

Use the squarefree own-root quartic detector \(H\) of
[the half-zero proof](../halfzero_detector/Proof.md), with
\[
 A_j(n)=\sum_{d\mid n}\mu(d)(1-2\log d/\log n)_+^j,\qquad
 H(n)=\log n\bigl(\tfrac74 A_2(n)-\tfrac34 A_4(n)\bigr)-\Pi(n),
 \qquad \Pi(n)=1_{\{n\ {\rm prime}\}}\log n.
\]
Set \(H=0\) off the squarefree integers, and
\(S_j=1_{\omega(n)=j}[-H]_+\). For an individual large even \(N\),
let \(J\Subset(1/3,2/3)\) be a fixed nondegenerate interval,
\(x+y=N\), \(x\in NJ\), \((x,N)=1\). Use ordered pairings on these
actual rows, \(L=\log N\), \(M=|J|N\mathfrak S(N)\), and
\(R_J=\langle\Pi,\Pi\rangle\).

**Theorem.** On an explicit physical squarefree rank-\(3,4,5\)
source with \(N^{.005}<p_1\le N^{.132}<p_2\), where \(p_1,p_2\)
are the literal least two primes, the genuine \([-H]_+\)-weighted
prime crossing is \(>.0288M\). Its lower holds even after the
positive deweighting in §3. It is disjoint from the
[previous two-least bank](../halfzero_detector/TwoLeastPrimeRebate.md),
whose certified lower \(>.1057691M\) is on \(p_2\le N^{.132}\).
The combined prime crossing on the two banks is \(>.134M\).
Moreover
\[
                       \langle\Pi,S_3+S_4+S_5\rangle>.137M.    \tag{1}
\]
The same results hold in the reflected orientation. The deweighted
new bank also has an explicit ordinary mass upper \( .077025550M\)
and an actual weighted opposite receiver bound with multiplier
\(.141638208\), as defined in §3. These are estimates for the same
\(H\); in particular the prime crossing by itself does not pay the
ordinary mass and overlap of a signed union.

## 1. True tags and subtraction of all unwanted quotient ranks

For \(5\le i\le131\) and \(132\le j\le186\), take actual distinct
primes \(p_1,p_2\) with target logarithmic angles in
\((i/1000,(i+1)/1000]\) and \((j/1000,(j+1)/1000]\). Write
\[
 a=(i+1)/1000,\quad b=(j+1)/1000,\quad h=p_1p_2,\quad
 c=1-a-b,\quad C=c+.002,\quad D=.555-a-b,\quad
 z=\max(.1325,D/3,b+.0005).
\]
Keep only the cells with \(2<D/z\le3,\ C/z<8,\ b<z<.187\).
The marked row event is exactly \(h\mid n,\ P^-(n/h)>N^z\).
Thus the two labels are the unique actual first two primes on
every squarefree retained row. Different cells or different
actual tag pairs give disjoint rows. Write \(t_\nu=\log p_\nu/L\).

With tag weights \(t_1t_2\), the lower linear sieve for the
actual prime opponent has normalized lower, per cell,
\(10^{-6}(2/D)\log(D/z-1)\). Use the marked calculation of
[the two-least-prime proof, §§1–2](../halfzero_detector/TwoLeastPrimeRebate.md),
with the following checks for the altered cells. Each residual
large-bank Rosser label has all square prefix angles at most
\(D\); the first lower square test follows from \(2z<D\).
Inserting both genuine labels in decreasing order spends
at most \(a+b\) at a residual prime. At a forced prime of
angle \(t\), the preceding residual prime of angle \(u\ge t\),
if present, bounds the sum of earlier residual angles by
\(D-u\); the earlier forced angles sum to at most \(a+b-t\).
The new square prefix is at most \(D-u+a+b-t+2t\le.555\).
If there is no preceding residual prime, it is at most
\(a+b+t\le.555\) since \(t\le b<z<D\).
All actual joined primes are below \(N^{.187}\), including
the largest possible forced label, since \(b<z<.187\).
Thus the original [.555 packing](../angular_prime_level_555/Proof.md)
covers the joined supports with the same notional \(.55525\)
and a small bank below both tags. Use the genuine two-bank
lower inequality, rounded-tree mesh, and strict power reserve
before attaching that independent bank. This is not an
over-root theorem for arbitrary weighted moduli.

Repeated large-bank prime collisions cost a power by the
same genuine square-divisibility estimate; in particular the
tag primes can be omitted from the residual sieve with
\(1+o(1)\) local change and the actual squares removed.
The physical modulus is \(hd\) and the unit residue is the
actual \(N\). The target-dividing tag weights are power-small.
The principal retains \(1/\varphi(h)\), the quotient
dimension-one Mertens factor is
\((1+o(1))e^{-\gamma_E}\mathfrak S(N)/(zL)\), and the two
genuine tag log-harmonics have \(\sum t_\nu/(p_\nu-1)=.001+o(1)\).
The spatial interval remains genuine, with proper prime
powers in any von Mangoldt expansion negligible.

Keep only quotient ranks one through three. A rank-\(k\)
quotient has ordinary angular density \(J_k(c_{\rm true}/z)/c_{\rm true}\),
where \(c_{\rm true}=\log(n/h)/L\in[c,C]+O_J(1/L)\),
\(J_1=1\) on \([1,\infty)\), \(J_k=0\) below \(k\), and
\(J_k'(u)=J_{k-1}(u-1)/(u-1)\).
These are genuine unopposed prime products: apply reciprocal
prime harmonics on all but the final slot, the ordinary PNT
in the actual final prime interval, and divide by \(k!\).
Apply the [actual \(3.446\) product-prime upper](../angular_prime_first_composite/Proof.md)
to the tags times every genuine quotient of rank \(k\ge4\),
with the same \(t_1t_2\) and \(J\).
All such ranks are finite on these cells. The retained count
with \(\Pi L t_1t_2\) is at least
\(10^{-6}\ell_{ij}M+o(M)\), where
\[
 \ell_{ij}=\left[
    \frac{2}{D}\log(D/z-1)-
    \frac{3.446}{c}\sum_{k\ge4}J_k(C/z)\right]_+ .              \tag{2}
\]
This subtracts an unconditional upper on the actual unwanted
ranks, not an unopposed model from an opposed lower.

The resulting actual ranks \(3,4,5\) have negative score.
The lower bounds for its magnitude divided by \(\log n\,t_1t_2\)
are, up to \(o(1)\),
\[
 v_3=36c^2+12[(i/1000)^2+(j/1000)^2]-14,\quad
 v_4=144z(c-z),\quad v_5=288B_{ij}z^2(c-2z),
\qquad
 B_{ij}\le \frac1{\sqrt{a^2+b^2+2z^2+(C-2z)^2}} .
\]
The rank-three residual prime is a genuine giant. The rank-four
weight on the physical row is \(144\prod u_i\) in own angles.
For rank five, by [the rough union, §1](../halfzero_detector/OneArmRoughDebit.md),
\(-H_5/\log n\ge288\,b_5(0)\prod u_i\), where \(b_5\)
is the density of the sum of five centered uniforms of
lengths \(u_i=\log p_i/\log n\). Its height is at least
\(1/\sqrt{\sum u_i^2}\), since among densities bounded by a
fixed height the uniform density on the centered interval
of that height minimizes the variance. With the three
remaining \(u_i\ge z+o(1)\), their product is at least
\(z^2(c-2z)+o(1)\) and their square sum is at most
\(2z^2+(C-2z)^2+o(1)\).
All these comparisons use the \(O_J(1/L)\) change between
target and own logarithms on the fixed compact cells.

The [rational checker](check.py) builds upper delay values
for \(J_k\) using right endpoint numerators and left endpoint
denominators on a grid of width .001. A positive series for
the logarithm lowers (2). Take \(B_{ij}\) to be the greatest
multiple of .001 satisfying its displayed bound, using an
integer square root. Write \(v_{ij}=\min(v_3,v_4,v_5)>0\);
this is distinct from the rational lower computed for the
product \(v_{ij}\ell_{ij}\). The checker gives per-cell
downward-rounded lower masses \(p_{ij}\) for
\(10^{-6}v_{ij}\ell_{ij}\), with sum
\( .028817505038252 \).
The earlier bank certifies \( .105769197972637 \) on its
literal tag event \(P^-(n/h)>N^z\), the two smallest real
prime labels, and ranks \(3,4,5\). Its second least label
is disjoint from the new one, proving the combined \(>.134M\)
strictly after taking the large-target limit at fixed cells.

## 2. The unpartitioned lower without double use of any cell

Use the exact calibration and unused positive upper from
[the negative-rank rebate, §§1–3](../halfzero_negative_rebate/Proof.md),
with comparison \(Q=A_4-(31/20)A_2\).
For cells in either bank write
\[
 r_{ij}=6c^2+((i+j)/1000)^2,\qquad
 K_{ij}=\frac{r_{ij}-31/20}{(3/4)r_{ij}-7/4}.
\]
On a true rank-three cell row the giant formula has
\(A_4/A_2\ge r_{ij}+o(1)>7/3\), since
\(2(u_1^2+u_2^2)\ge(u_1+u_2)^2\).
The ratio \(Q/(-H/\log n)\) decreases with \(A_4/A_2\);
therefore it is at most \(K_{ij}+o(1)\).
On ranks four and five \(Q\le(4/3)[-H/\log n]_+\),
so \(K_{ij}>4/3\) also suffices there. Off the cells use
the original pointwise coefficients and the entire original
unused positive upper; nothing is assumed about untagged ranks.
Accordingly the original weighted inequality keeps its right
side \(.263M+(11/20)R_J\), but its coefficients are lowered to
\(K_{ij}\) on these disjoint different physical sources.
Raising every other coefficient to \(21/5\) and rearranging gives
\[
 \frac{21}{5}\langle\Pi,S_3+S_4+S_5\rangle
 \ \ge\ \left(.263+\sum_{i,j}(21/5-K_{ij})p_{ij}\right)M
               +\frac{11}{20}R_J+o(M).
\]
The per-cell coefficients are nonnegative, so their certified
lower crosses can be inserted in this direction.
The exact rounded extra sum is \( .315706369439743 \), proving
(1) since \(R_J\ge0\). This is not a sum of overlapping
unpartitioned rebates.

## 3. A deweighted bank and its two different actual normalizers

In each new cell with positive certified product \(v_{ij}\ell_{ij}\),
define
\[
 W_{ij}(n)=
 1_{\{n\ {\rm squarefree},\ \omega(n)\in\{3,4,5\},\
          p_1,p_2\ {\rm as\ in\ the\ cell},\ P^-(n/h)>N^z\}}
       \min\{[-H(n)]_+,v_{ij} L t_1t_2\}.
\]
Set \(W_2=\sum W_{ij}\) over those cells. Each \(W_2\) is a
physical deweighting of exactly the same \(H\), not an
independent detector. Its true prime lower retains all the
\(p_{ij}\) of §1 by the preceding lower
\(W_{ij}\ge(v_{ij}-o(1))Lt_1t_2\) on that event.
No error relative to an empty tiny slice is needed; all
cells and their angular floors are fixed.

The ordinary upper for \(\mathfrak S(N)\sum W_2/M\) is
\[
 m_2=\sum_{\rm new\ cells}
       \frac{10^{-6}v_{ij}}c\sum_{k=1}^3 J_k(C/z)
             \ < .077025550 .
\]
Use genuine ordinary product integration as in §1, since
the density excludes the true squareful rows and the
target-unit mask can only decrease its positive upper.
This bound holds in both central intervals.

For any of the genuine compact angle sources \(B\ge0\) used
here (in particular \(W_2\), the deweighted old bank, or
\([-H]_+1_{P^->N^{.145}}\)), there is also the bound
\[
 \langle B,W_2\rangle
     \le U_2\,\mathfrak S(N)\sum_{x\in NJ,(x,N)=1} B(x)+o(M),
 \qquad
 U_2=\sum_{\rm new\ cells}\frac{10^{-6}\,2v_{ij}}{.499-a-b}
                                  < .141638208.              \tag{3}
\]
It holds in either orientation, taking the source interval
accordingly. Indeed drop the opposite rank condition after
uppering the weight by \(v_{ij}Lt_1t_2\) and keep the two
literal tag divisibilities with actual rough quotient.
The upper linear sieve has level \(N^{D'}\),
\(D'=.499-a-b\). Each actual modulus is
\(hd\le N^{.499}\) with divisor-bounded forced-tag multiplicity.
Thus the true product BV in [the rough union, §3](../halfzero_detector/OneArmRoughDebit.md)
pays the actual discrepancy, summing the weights at the
joined moduli rather than applying BV separately for
individual fixed tags. This also covers the actual reflected
residue and unchanged macroscopic intervals. The source weights
are fixed finite prime-product profiles of positive
polynomial floor; rounding continuous weights and compact
Jordan masks uses the same strict power reserve and true
two-rough error upper.

For the exact model, on a true source value \(x\) the reduced
density of \(hd\mid N-x\) is \(1/\varphi(hd)\) if \((hd,Nx)=1\)
and zero otherwise. Any tag prime dividing \(Nx\) is excluded,
not counted as another bad root. We may omit the two tag primes
from the rough upper sieve; this majorizes the event and changes
the local factors by \(1+o(1)\). The principal quotient product
is \((1+o(1))e^{-\gamma_E}\mathfrak S(Nx)/(zL)\), while
\(\mathfrak S(Nx)/\mathfrak S(N)=1+o(1)\) uniformly for these
sources, whose real primes all are polynomially large.
The tag sum with real unit exclusions is bounded above by
the unrestricted positive tag log-harmonics.
The checker verifies \(1<D'/z<3\) for every selected cell,
so the upper coefficient becomes \(2/D'\). This proves (3).
The two bounds \(m_2,U_2\) price actual but different
pieces of any subsequent fractional union ledger.
They do not evaluate the untreated contribution.
