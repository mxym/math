# The complementary positive nonsemiprime one-by-three chamber

Keep the actual even target \(N\), the fixed central interval \(J\),
\(L=\log N\), \(M=|J|N\mathfrak S(N)\), \(x+y=N\), \(x\in NJ\),
\((x,N)=1\), and the original sextic score \(S=G_b+W\), \(b=.003\).
Use both orientations of the exact \((1,3)\) physical tag counts
of the [negative one-by-three proof](NegativeOneByThreeCredit.md):
all prime factors exceed \(N^{.003}\), exactly one is at most \(N^{.080}\)
on the first arm and exactly three on the other. Both arms are
squarefree. In this note the one-tag arm is **not a semiprime** and
has literal \(H(x)>0\). All right ranks and both right signs are
retained. As in that proof \(S=H\) on both physical arms.

**Proposition.** The original signed sum on this chamber and its
reflection exceeds \(-.195M+o(M)\). It is disjoint from the true
semiprime [one-by-three debit](SmallSemiprimeThreeTagAdverse.md)
and the [negative one-by-three credit](NegativeOneByThreeCredit.md).
The remaining \(H=0\) one-tag arm contributes zero. Together the three
bounds therefore price the **entire original** exact one-by-three
tag-count chamber and its reflection at the .003 floor. They do
not bound any other remaining exterior.

## 1. Genuine three-way comparison

Write \(X=[H]_+\) on the one-tag nonsemiprime support, and
\(Y=[-H]_+\) on the entire three-tag support. Write \(X=X_{34}+X_h\)
where \(X_{34}\) has ranks 3 and 4. All other possible positive
\(X\) is at odd ranks \(\ge9\): rank one is excluded by the physical
small tag, ranks 5–7 are nonpositive and higher even ranks
are identically zero. Likewise \(Y=Y_{\le7}+Y_h\) with nonzero
\(Y_{\le7}\) at ranks 4–7. The desired lower follows by bounding
\(\langle X,Y\rangle\), since the unused three-tag positive part
gives a nonnegative contribution.

As in the preceding one-by-three proof let \(m(Z)\) be the ordinary
unopposed mass for a true nonnegative score, and let \(U_Z\) be a
genuine opposed receiver upper: \(\langle Z,A\rangle/M\le U_Zm(A)+o(1)\)
for any fixed compact positive-floor genuine product source \(A\).
No rank independence is used. Split once as
\[
 \langle X,Y\rangle/M
 \ \le\ m(X_{34})\,U_{Y_{\le7}}
           + U_{X_{34}}\,m(Y_h)
           +m(X_h)\,U_Y+o(1).                                      \tag{1}
\]
Use genuine product Bombieri--Vinogradov in each orientation
as in [the true three-tag transfer](ThreeByThreeTagCredit.md#1-physical-support-and-the-genuine-paired-measure).
All sources in (1) have fixed finite rank (at most 15) and positive
polynomial factor floor. We use only a genuine one-sided **positive**
sieve in each receiver. The compact weighted source is obtained by
positive angular box approximation on these same actual integers.
Its auxiliary unit restrictions are exactly those of the centered
product progression estimate. Fixed source and receiver cuts use
only the actual target-log angles; replacing own-log coordinates
in continuous score profiles gives \(o(M)\), with the true rough
paired upper as in the negative comparison. Neither sign in (1)
is approximated by a signed model.

For \(X_{34}\) use the exact \(g_t(s)=(F(s)-F(s+t))/t\)
of the native profile, with \(T=1-t\) and the true one-tag angle
\(t\). On rank three the ordinary amplitude divided by \(Lt\)
is \([g_t(0)-g_t(z)-g_t(T-z)]_+\), and is at most \(g_t(0)\).
On rank four it is \([528-1680 q]_+\prod_{i=1}^3 z_i\),
where \(q=t^2+\sum z_i^2\), and is at most
\([528-1680(t^2+T^2/3)]_+(T/3)^3\). These are actual normalized
slice formulas; the formal full-quotient terms in the rank-three
formula vanish because \(T>.92\) is beyond \(g_t\)'s support.
Open the **one true tag**, using the ordinary upper ratio 4 with
sieve level \(N^{.320}\) and floor \(a=.080\), so every tested
modulus \(pe\le N^{.400}\). The real factor \(t\) in the score
cancels the prime reciprocal harmonic. This yields
\(U_{X_{34}}\) by integrating the sum of the two displayed caps
against \((.575/a)dt\). Ordinary rank-three and rank-four masses
are integrated against the actual reciprocal quotient simplex
with standing factors \(1/2!\), \(1/3!\), respectively.

The high odd ordinary bounds for \(X_h,Y_h\) are the half-envelope
bounds in the [negative one-by-three proof](NegativeOneByThreeCredit.md#2-actual-pointwise-estimates-and-the-ordinary-inputs),
now used as absolute envelopes. For \(Y_h\) this counts both
possible signs at those ranks, so it bounds the negative part
as needed. The remaining issue in (1) is to keep the **actual**
low-rank three-tag receiver small.

## 2. A weighted two-floor receiver on the same actual rows

On each actual right \(.004\) three-tag cell (last bin shortened)
write \(\tau_+\) for the upper sum of its tag angles, \(T\) for the
quotient angle sum, and \(q_0\) for the sum of squares of the three
tag angles, in the limiting normalized expressions. The true
right score is divided by \(L\) times its three tag angles. For
ranks 4, 5, 6, 7 use the respective upper caps
\[
\begin{split}
 C_4&=T[1680(q_0+T^2)-528]_+,\\
 C_5&=\max_{a\le z\le T/2}
 \left[10080\sqrt{q_0+z^2+(T-z)^2}
 -1056/\sqrt{q_0+z^2+(T-z)^2}\right]_+z(T-z),\\
 C_6&=40320(T/3)^3,\\
 C_7&=1056T/2+80640(2\sqrt 2/T)(T/4)^4 .
\end{split}                                                       \tag{2}
\]
The first and third follow from the literal even formulas. The
second is the genuine rank-five bound via the height and mean
absolute deviation of its centered box density, with its two
actual quotient factors \(z\) and \(T-z\). For the fourth,
order the four quotient angles \(z_1\le z_2\le z_3\le z_4\).
The three tags are smaller than all of them. Differentiating
the largest two boxes gives \(|b_7''(0)|\le 2/(z_2z_3z_4)\);
multiplication by the quotient product leaves \(2z_1\le T/2\).
The cube-slicing bound gives \(b_7(0)\le2\sqrt 2/T\) since
\(\sum z_i^2\ge T^2/4\). These bounds use the true quotient factors,
not nominal prime numbers on the tested progression.

Put \(D=.498-\tau_+\) and \(c=D/3\). In every cell
\(a<c<.164\) and \(T\ge .760\). Define \(C\) as a cell-wide
upper for the maximum of (2). If the **actual** least quotient
angle is at most \(c\), rank four is absent because its single
quotient prime has angle \(T>c\). In the rank-five cap restrict
the maximum to \(z\le c\); the rank-six cap becomes
\(40320c(T-c)^2/4\), since \(z(T-z)^2\) increases for
\(z\le T/3\). The rank-seven cap becomes
\[
       2112c+80640(2\sqrt 2/T)c((T-c)/3)^3
\]
since \(z(T-z)^3\) increases for \(z\le T/4\). Let \(B\le C\)
be a safe cell-wide bound for this restricted maximum, replacing
it by \(C\) if necessary. On the actual quotient \(m=y/h\)
the normalized \(Y_{\le7}\) is then at most
\[
         B\,1_{P^-(m)>N^a}+(C-B)\,1_{P^-(m)>N^c}.                \tag{3}
\]
This is a pointwise positive inequality with two **nested**
roughness tests, not a subtraction of independent \emph{upper}
sieve estimates.

Use the same true level \(N^D\) on each test; all \(he\le N^{.498}\).
Their ordinary linear upper model coefficients with the same
target-unit mask are \(e^{-\gamma}F_{\rm lin}(D/a)/a\) and
\(2/D\). They use the genuine tags and the actual reduced
residue \(N\) after opening their product. As in the original
three-tag transfer, omitting the actual three tag primes from
the positive sieve changes the local model by \(1+o(1)\); the
true left factors are bounded-rank with fixed polynomial floor.
The real three logarithmic weights cancel each actual harmonic,
leaving the ordered cell volume (factorial for repeated bins).
In particular (3) gives the receiver coefficient on a cell
\[
       \operatorname{vol}\,\left[C\,\frac2D
                    + B\left(e^{-\gamma}F_{\rm lin}(D/a)/a
                                             -\frac2D\right)\right].       \tag{4}
\]
For every cell we may alternatively choose the earlier true
ratio-at-most-four receiver and pointwise cap \(C\); use the
better of two upper bounds on the same entire cell. For the
all-rank \(U_Y\), use that earlier receiver and replace \(C\)
by its maximum with the applicable high odd half-envelopes.
No same cell is added twice, no conditional independence
is assumed, and no above-root input is used.

## 3. Outward replay and reflection

Run:

    python3 -OB check_positive_one_by_three_debit.py

The replay verifies the exact negative one-by-three wrapper
and its existing dependencies by hash. The genuine rank-three
one-tag ordinary integrals use .0002 tag cells, 720 separator
cells, and an improved bound for \(g_t\). When the full window
\([s,s+t]\) lies below half, integrate the cubic and quintic
of \(-F'\) exactly as centered uniform moments:
if \(h=1/2-s-t/2\), \(v=t^2/12\), \(w=t^4/80\), then
\[
 g_t(s)=h\{176(h^2+3v)-672(h^4+10h^2v+5w)\}.
\]
If it crosses half, integrate the enclosing values of
\(176z^3-672z^5\) at \(z=(1/2-s-tv)_+\), over 50 equal
intervals in the true averaging variable \(v\in[0,1]\).
Its possible interior maximum occurs at \(z=\sqrt{11/70}\);
the stationary location and value are bounded outward.
Rows wholly beyond half have zero. The ordinary rank-four
integral uses the exact quotient product cancellation and
60 separator bins. Rank-tail densities use the same
\(10^{-4}\) positive recurrence as the previous checker.

Right rank-five caps are outward maxima over the complete
\(10^{-3}\) grid for the ratio \((T-z)/T\in[1/2,1]\);
in the restricted cap omit a bin only if it cannot have
\(z\le c\). For \(s\le5\) the linear upper coefficient
in (4), normalized at \(a\), is
\[
     \frac{2}{D}\left(1+\int_0^{s-3}
                                \frac{\log(1+u)}{2+u}\,du\right)
       \quad (3\le s\le5)
\]
and \(2/D\) for \(s\le3\). Use a positive upper rectangle
sum for its increasing integrand, and monotonicity of
\(F_{\rm lin}\) beyond the safely smaller argument
\(.3999/.080=4.99875\) (the implemented cutoff in \(D\)
is .3999 at \(a=.080\)). All are upper bounds, with the
common positive coefficient in (3) kept exact before
computing a numerical enclosure of (4).

The outward constants are
\(m(X_{34})<.16881\), \(U_{X_{34}}<1.493\),
\(U_{Y_{\le7}}<.55006\), \(m(Y_h)<.002527\),
\(m(X_h)<.000081\), and \(U_Y<7.736\).
The outward cost from (1), summed over the two orientations,
is \(<.1945M+o(M)\), hence \(<.195M+o(M)\).
The reflected \(1-J\) interval gives the same normalized
constants, not because it is the same interval but because
all moment and receiver proofs apply to that fixed central
interval with its actual equal length. The literal counts
\((1,3)\) and \((3,1)\) are disjoint.
