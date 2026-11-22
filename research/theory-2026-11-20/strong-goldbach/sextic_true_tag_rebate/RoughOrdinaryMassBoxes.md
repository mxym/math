# Ordered boxes for the ordinary sextic rough masses

Keep the *same* degree-six score and physical rough-negative correction
\(G=H+Q\), where \(Q=[-H]_+1_{P^->N^{.1251}}\). Notation, fixed target
and unit conditions are those of [the original proof](Proof.md). These
estimates change two ordinary mass bounds only. They use neither new
receiver distribution nor the distinct narrow-mark compensation.

**Proposition.** In the normalization of the ordinary mass \(M_{R_i}\)
of \(R_i=Q1_{\omega=i}\), one has
\[
 M_{R_4}\le (.005455365940837+o(1))M,\qquad
 M_{R_5}\le (.011092191776369+o(1))M .
\]
Consequently the full rough-only debit in
[the ordered-mark proof, §4](OrderedMarkCovariance.md) is strictly below
\(.046M\), and the [whole true tiny union](WholeTinyRoughCompensation.md)
for this same sharp \(G\) costs at most \(2.68bM\) for every sufficiently
small fixed \(b>0\). Thus, for \(I_b=1_{P^-\le N^b}\),
\[
 R_J\ge (.954-2.68b)M+
              \langle(1-I_b)G,(1-I_b)G\rangle+o_{J,b}(M).
\]
The same original signed covariance on the right is still unpriced.
No explicit value of the sufficiently small cutoff \(b\) is needed
or asserted.

## Ordinary integration with exact ceilings

The true ordinary angular integral of rank \(r\) has density
\(du_1\cdots du_{r-1}/\prod_i u_i\) on the ordered simplex. Sorting
cancels \(1/r!\) in the ordinary density from the original proof.
Write \(a=.1251\), \(h=(1-ra)/256\), \(u_r=1-\sum_{i<r}u_i\).
Use sorted box labels \(j_1\le\cdots\le j_{r-1}\) and lower endpoints
\(A_i=a+j_i h\). Necessarily \(\sum_{i<r-1}j_i+2j_{r-1}\le256\).
For an upper use the full volume \(h^{r-1}/\prod m!\), where the
\(m\)'s are the multiplicities of equal labels among the first
\(r-1\) coordinates. Dividing by each factorial keeps exactly the
subregion ordered within that group; the last-coordinate constraint
can only shrink the volume. Bound the score on the box by its
outward upper and round each volume-weight product up to \(10^{-15}\).

At rank four the angle product cancels against the density, leaving
\((1680\sum_i u_i^2-528)_+\). The sum of squares, including the
determined last coordinate, is convex, so the maximum of the eight
box vertices is an upper even if a vertex violates the actual order.
With \(D=2560000\), the floor numerator is \(320256\) and the step
numerator is \(4996\). If \(v\) is the maximum sum of squared
numerators, the box upper is
\((1680v-528D^2)_+4996^3/(D^5\prod m!)\).

At rank five, every singleton is at most \(1-4a=.4996\), and
every four-element sum is greater than half. Put \(z=1-2t\);
\(F(t)=z^4(11-7z^2)/4\) on \([0,1/2]\). Put
\(\psi(t)=F(t)\) up to half and \(-F(1-t)\) thereafter.
Pair and complementary triple terms give the exact score
\[
             H_5=1-\sum_i F(u_i)+\sum_{i<j}\psi(u_i+u_j).
\]
Both \(F\) on its domain and \(\psi\) are decreasing. Use
\(A_5=\max(A_4,1-\sum_{i=1}^4 A_i-4h)\) for the last lower
endpoint. For pairs among the first four use upper angles
\(A_i+A_j+2h\); for a pair with the last use
\(1-\sum_{k\le4,k\ne i}A_k\). Thus bounding \(-H_5\) uses
lower singleton angles and upper pair angles; take the positive
part after the sum. For the density, \(\prod_i u_i\ge\prod_i A_i\).
The same denominator \(D\) applies, with step numerator \(3745\)
and exact value denominator \(4D^6\) for \(F\) and \(\psi\).
The rational check
[check_rough_ordinary_boxes.py](check_rough_ordinary_boxes.py)
sums 123,464 rank-four and 1,673,243 rank-five boxes using only
integer ceilings.

## Applying the same physical receiver bounds

Let \(m_i\) be the ordinary mass uppers just proved at ranks four
and five, and keep the existing \(.000451\) and \(.000001671\)
at ranks six and seven. The unchanged rank receiver constants
\(U_i\) come from the actual single-target product estimates in
[the ordered-mark proof](OrderedMarkCovariance.md). Use the same
debit \(2\sum_i m_i+\sum_{i,j}\min(m_iU_j,m_jU_i)\); the attached
check gives the strict bound \(.046\). For the true tiny union the
same exact formula keeps \(m(b)=-78b+O(b^2)\) on both arms, so its
leading loss coefficient is at most \(156\sum_i m_i<2.653\). The
strict reserve to \(2.68\) absorbs the uniform \(O_J(b^2)\) term
of the already proved union estimate at sufficiently small fixed
\(b\). Nothing about the remaining intermediate-factor covariance
has been inferred from these ordinary one-arm bounds.
