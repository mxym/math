# Refined rough overlap and a compensated debit for two real tag banks

Use the **same** squarefree own-log quartic half-zero detector \(H\)
from [the half-zero theorem](Proof.md) and
[the negative-arm comparison](OneArmRoughDebit.md).
Let \(N\) be an individual large even target, \(L=\log N\),
\(J\Subset(1/3,2/3)\) a fixed nondegenerate interval,
\(x\in NJ,\ y=N-x\), and \(M=|J|N\mathfrak S(N)\).
All pairings retain the actual target units \((x,N)=1\).
In particular
\[
       \langle H,H\rangle=R_J-M+o(M),\qquad
       R_J=\langle\Pi,\Pi\rangle .
\]
No profile change or unit-jump receiver is involved.

Put \(a=.145\) and \(R_j(n)=[-H(n)]_+
1_{\{\omega(n)=j,\ P^-(n)>N^a\}}\) for \(j=3,4,5\).
Then \(R=R_3+R_4+R_5\) is the full negative score on all
actual \(N^a\)-rough arms, by the previously proved signs through
rank six. Define two further genuine nonnegative weights:

* \(W_1(n)\) is supported on the actual surviving squarefree
  rank-three-to-five cells of [the two least prime rebate](TwoLeastPrimeRebate.md).
  Thus the two smallest distinct primes have target angles
  \(t_1,t_2\) in its specified fixed disjoint cells below \(.132\),
  and the actual quotient is \(N^z\)-rough with the same
  cell-dependent \(z\). On that support put
  \(W_1(n)=\min([-H(n)]_+,B L t_1t_2)\), with its same
  positive cell weight \(B\).
* \(W_2(n)\) is the real deweighted bank of
  [the separate second least prime rebate, §3](../halfzero_tag_union/Proof.md).
  Its first genuine least angle is at most \(.132\), its
  second is above \(.132\), and the remaining factors pass
  its fixed cell-dependent quotient floor. It uses every
  positive certified cell in that proof, not the full
  negative weight in those cells.

These three banks have disjoint actual supports **on one arm**.
Set \(Q=R+W_1+W_2\) and
\(\widetilde H=H+Q\). On their support \(0\le Q\le[-H]_+\).
In each old tagged cell \(W_1\) removes at least \(7.3\%\)
of the true negative weight for all large \(N\); the new
bank \(W_2\) removes at least \(9.3\%\) on its cells.
These fractions concern the selected actual cells, not all
of the small-factor negative arm.

**Theorem.** Uniformly through the even targets, there is a strict
actual comparison
\[
              \langle H,H\rangle
               \ge \langle\widetilde H,\widetilde H\rangle
                          -.693\,M+o(M),                      \tag{1}
\]
and hence
\[
          R_J\ge .307\,M+\langle\widetilde H,\widetilde H\rangle+o(M).
                                                                    \tag{2}
\]
The full rough negative weight disappears from
\(\widetilde H\); its negative parts on the two actual tag banks
are only reduced, not set to zero. Any remaining adverse row
has a negative arm with least actual factor \(\le N^{.145}\).
The sign of the remaining true correlation in (2) is not proved.
The separate unpartitioned prime rebate is **not** added.

## 1. Uniform positive receivers for the three exact rough ranks

For a nonnegative genuine compact finite-rank prime-product
source \(Z\) on the first arm, of fixed positive least-factor
floor, abbreviate
\[
                 M_Z=\mathfrak S(N)
                     \sum_{\substack{x\in NJ\\(x,N)=1}} Z(x).
\]
Here \(Z/L\) is a bounded angle and spatial profile
(or a finite collection of such profiles), as in
[the rough-arm proof, §3](OneArmRoughDebit.md).
All actual sources in the calculation below have this description.
Let \(\theta=.499\). We use literal positive receivers
\(U_j\) such that
\[
       \langle Z,R_j\rangle
                   \le U_j M_Z+o(M)\qquad(j=3,4,5).            \tag{3}
\]
Each estimate also holds on the reflected interval.
The genuine product distribution and the finite angle
approximations are exactly those in the preceding rough-arm
proof. Every opened modulus in the following sieves is at
most \(N^\theta\), including the fixed true tag or tags.
All the tag choices are grouped at these actual moduli
with divisor-bounded multiplicity. No error bound is claimed
after fixing an individual progression and every tag.

Here is the common local calculation for the positive receivers.
When the opponent has true tag product \(h\), its actual
quotient is sifted at level approximately \(N^\theta/h\).
The actual modulus is \(hd\), with \(d\) a sieve label.
We may omit the prime factors of \(h\) from the upper sieve;
this preserves a true upper and changes its model by \(1+o(1)\),
as every tag prime is polynomially large. Retain \(Nx\) in the
reduced model for each actual \(x\). Thus the conditional
density at each other tested prime is \(1/(p-1)\) off \(Nx\)
and zero on \(Nx\); the outside factor is \(1/\varphi(h)\)
when \((h,Nx)=1\). All actual source factors are polynomially
large and at fixed rank, so \(\mathfrak S(Nx)=
(1+o(1))\mathfrak S(N)\), uniformly. Dropping the remaining
unit exclusions is allowed only for uppering the positive
tag harmonic in this model. With an actual quotient floor
chosen so the linear-sieve parameter belongs to \([1,3]\),
its combined factor is
\[
         \frac{2\mathfrak S(N)}
                     {h(\theta-\log h/L)L}(1+o(1)).
\]
Here the usual \(sF(s)=2e^{\gamma_{\!E}}\) on \([1,3]\)
and the genuine Mertens local product are used.
Varying the sieve levels between tag labels changes only the
bounded coefficients at the joined moduli. Fine fixed angle
boxes with margins, then refinement, retain all the stated
integrals and the physical spatial intervals.

**Rank three.** On the negative receiver the third factor
is an actual giant, and the other two angles \(u_1,u_2\)
are the two real tag angles with sum \(s\le .428\).
Because the genuine residual prime is above this sieve floor,
use \(z_{\rm up}=(\theta-s)/2\) as the residual sifting
exponent, so the parameter is 2. The pointwise majorant
for \(R_3/L\) at fixed tags is
\[
    u_1u_2 G(s),\qquad
    G(s)=\{36(1-s)^2+12(a^2+(s-a)^2)-14\}_+ .
\]
This is the exact rank-three formula majorized over
the actual ordered \(u_1\in[a,s/2]\). The true reciprocal
harmonics of the two distinguished primes cancel \(u_1u_2\).
The resulting receiver is
\[
             U_3=2\int_{2a}^{.428}
                       \frac{s/2-a}{\theta-s}G(s)\,ds .        \tag{4}
\]
The divisor bound is strict since \(\theta-.428>0\).
Using target-log rather than own-log angles for tags and
sieve levels changes only vanishing boundary layers.

**Rank four.** Open its actual **least** prime of angle
\(u\in[a,1/4]\). The exact score implies
\[
       R_4/L\le144u\{(1-u)/3\}^3+o(1).
\]
Every remaining factor exceeds the least prime. Set the
sifting exponent to \(\min(u,(\theta-u)/2)\), with
negligibly smaller fixed bin floors if necessary.
The parameter is between 2 and 3 uniformly on this range:
it is 2 in the second case, and in the first it is
\((\theta-u)/u\le (\theta-a)/a<3\).
Hence the true single-tag receiver is
\[
             U_4=\frac{288}{27}\int_a^{1/4}
                                 \frac{(1-u)^3}{\theta-u}\,du. \tag{5}
\]
We may enlarge the sum to all genuine labels in this range
after majorizing the actual least-labelled row.

**Rank five.** Use the bound \(b_*=16903/16000\) for
\(R_5/L\) from the preceding rough-arm proof.
For any actual rank-five receiver the sum of its ten actual
unordered pair angles \(\log(pq)/L\) is \(4\log n/L\le4\).
With \(b=.450\) it follows that \(R_5/L\) is bounded above
by
\[
      \frac{b_*}{10b-4}
      \sum_{\{p,q\}\subset\{p:p\mid n\}}
                            (b-\log(pq)/L)_+ .
\]
This is the same actual pair-label principle as in
[the rough positive-arm overlap](../short_odd_receiver/PositiveRoughUnion.md),
now applied to this quartic negative score.
The remaining factors are genuinely above \(N^a\),
so the sifting exponent \((\theta-s)/2\) is usable for
every pair with \(s=\log(pq)/L\in[2a,b]\):
\((\theta-2a)/2<a\) and \(\theta-b>0\).
The ordinary **unordered** reciprocal harmonic of the
two tags at fixed total \(s\) is
\(\log((s-a)/a)/s\). Thus the actual upper is
\[
        U_5=\frac{2 b_*}{10b-4}\int_{2a}^{b}
            \frac{\log((s-a)/a)}s\frac{b-s}{\theta-s}\,ds .     \tag{6}
\]
The ten slots are used only to prove the pointwise receiver
majorant; no independent factor assumption occurs in a
physical paired count.

The proof of (3) for all these profiles is therefore
one actual source product-BV estimate with positive linear-sieve
weights on the marked opponent. It does not estimate
the simultaneous prime statuses of two large free factors.

## 2. Exact masses, overlaps and true rebates for the small banks

Let \(m_j\) be the ordinary upper for \(M_{R_j}/M\) in
[the rough-arm proof, §2](OneArmRoughDebit.md).
The numerical bounds below keep the distinction between
that **source mass** and the **receiver** \(U_j\).
We have, in either physical orientation,
\[
 \begin{gathered}
  M_{R_j}\le(m_j+o(1))M,\\
  \langle R_i,R_j\rangle\le
               \{\min(m_iU_j,m_jU_i)+o(1)\}M,
                    \qquad i,j\in\{3,4,5\}.
 \end{gathered}                                                \tag{7}
\]
The second inequality uses (3) with genuine source \(R_i\)
and then its reflection with source \(R_j\). It prices the
actual positive overlap once, not a product model.

For \(W_1\), write \(c_-,c_+,z,B\) as in each old tag cell and
put \(D'=.499-\kappa_+\).
Analogous to its rank subtraction, ordinary integration
over the actual quotient ranks 1,2,3 gives the positive upper
on \(M_{W_1}/M\)
\[
       m_{W_1}=\sum_{\rm old\ cells}
                    \frac{10^{-6}B}{c_-}
                              \sum_{j=1}^3 J_j(c_+/z).
\]
The literal two-tag conditional rough upper in §1 of this
note is available at level \(D'\) and threshold \(z\):
\(1<D'/z<3\) on every selected cell.
We may drop the opponent's rank condition for an upper,
but keep its true quotient roughness and both literal tags.
Their actual harmonic weight is \(t_1t_2\).
Consequently, for any of the genuine sources \(Z\) in (3),
\[
       \langle Z,W_1\rangle
                   \le U_{W_1} M_Z+o(M),\qquad
       U_{W_1}=\sum_{\rm old\ cells}10^{-6}\frac{2B}{D'}.
\]
For \(W_2\) use the actual mass and receiver from
[its proof, §3](../halfzero_tag_union/Proof.md).
These bounds apply also with source \(W_1\) or \(W_2\)
and to all \(R_j\): the physical least-factor floors
are fixed, the actual rank is bounded, and use of a
minimum with \([-H]_+\) is a bounded continuous angle
test inside each fixed cell. Thus (7) holds also for
indices labelling \(W_1,W_2\) with their own \(m,U\).

The real prime-opponent rebates of the earlier tag proofs
apply to the exact deweighted banks:
\[
  \langle W_1,\Pi\rangle\ge (p_1+o(1))M,\quad
  \langle W_2,\Pi\rangle\ge (p_2+o(1))M,\quad
  p_1=.105769197972637,\quad p_2=.028817505038252 .
\]
Indeed within the selected physical rows the previously
proved lower was \( (B-o(1))L t_1t_2\), or its new
cell analogue, and \(W_i\) retains precisely that certified
weight up to \(o(1)\) in the normalized row.
Their true fixed positive rank/floor prime-opponent upper
makes the total of this \(o(1)\) error negligible.
Both prime rebates hold separately in either orientation.
For a rough source \(R_j\) the lower \(p=0\) is sufficient.

To check the retained fractions, within any tested cell
the literal negative score divided by \(Lt_1t_2\) is at
most \(V+o(1)\), where
\[
           V=\max\{36C^2+12(\bar t_1^2+\bar t_2^2)-14,\
                                36C^2,\ 28+32C^2\}.
\]
Here \(\bar t_1,\bar t_2\) are the upper tag endpoints,
and \(C\) is the upper cofactor sum in the corresponding
old or new proof. The first two entries follow from the
exact rank-three/four formulas. For the last, let
\(v_1\le v_2\le v_3\) be the three remaining genuine
factor angles. The exact box-spline formula gives
\(-b_5''(0)\le2/(v_1v_2v_3)\),
\(b_5(0)\le1/v_3\), so the upper after multiplication
by the three residual angles is at most
\(28+288v_1v_2\le28+32C^2+o(1)\).
The exact checker takes the minimum of \(B/V\) or
its new-cell analogue, over the whole actual banks.
These ratios are respectively \(>.07347\) and \(>.09315\).
This explains the qualitative limit on what is removed:
the rest of those actual negative rows is not discarded.

## 3. Joint signed accounting, with no missing overlap

For each of the five actual sources
\(Z\in\{R_3,R_4,R_5,W_1,W_2\}\), the same
[true transfer against the full detector](OneArmRoughDebit.md)
gives
\[
            \langle Z,H\rangle
                         = M_Z-\langle Z,\Pi\rangle+o(M),
\]
also in its reflection. This uses strictly short product-BV
with the actual \(Nx\) mask followed by the uniform
own-log/half-zero transfer on the **entire** opposite arm.
There is no assumed roughness of that opposite arm,
and the genuine prime cross has not been replaced by a model.

Expanding the compensated score gives the exact algebra
\[
 \langle H,H\rangle
  =\langle\widetilde H,\widetilde H\rangle
      -\langle Q,H\rangle-\langle H,Q\rangle-\langle Q,Q\rangle .
\]
For the lower, bound each of the two signed mixed terms by
its genuine ordinary source mass minus its true prime rebate,
and use (7) for every ordered component of the positive
overlap. Thus the debit is at most
\[
       2\bigl(\sum_i m_i-p_1-p_2\bigr)
                          +\sum_{i,j}\min(m_iU_j,m_jU_i).        \tag{8}
\]
All five sources are used on each arm, with explicitly
paid actual cross-overlaps. None of the real same-sign
terms has been added a second time.

The [exact rational checker](check_compensated_debit.py)
uses fixed endpoint Riemann sums for (4)--(6),
the verified old/new tag cells and their same delay-integrals,
and exact positive rounding of all ordinary/receiver bounds.
For orientation, its outputs rounded upward are
\[
\begin{array}{c|cc}
  \text{source}&m&U\\ \hline
  R_3&.006712177&.058317542\\
  R_4&.074088000&1.925719739\\
  R_5&.009809915&.353457543\\
  W_1&.146748616&.212221385\\
  W_2&.077025550&.141638208
\end{array}
\]
It gives (8) \(<.692566782<.693\). The three rough
sources alone in the same exact accounting cost
\(<.375319467\); using only them and \(W_1\) costs
\(<.526880294\). These are nested alternatives, not
additional credits. Equations (1)--(2) follow.
No lower on \(\langle\widetilde H,\widetilde H\rangle\)
and no strong Goldbach conclusion is obtained.
