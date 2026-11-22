# The complete two-tag self-pair on the same sharp sextic score

Keep the fixed even target \(N\), \(L=\log N\), the central interval
\(J\), \(M=|J|N\mathfrak S(N)\), the genuine rows \(x+y=N\),
\(x\in NJ,\ (x,N)=1\), and the original score \(S=G_b+W,\ b=.003\),
of the [full medium comparison](FullMediumCohort.md).
Let \(\mathcal C_{22}\) be the whole physical chamber where each arm
has exactly two distinct actual prime factors of target-log angle
in \((.003,.080]\), and all its other factors exceed \(N^{.080}\).
Retain the true squarefree gate. There is no additional sign,
angle sum, or quotient-rank restriction.

**Proposition.** The original signed sum over this full chamber is
\[
                    \sum_{\mathcal C_{22}} S(x)S(y)>.187M+o(M).
\]
On this chamber the original \(W\) is retained, including intervals
where its positive clipping changes the score. No contribution
outside the chamber is asserted. In particular this lower **must
replace**, not be added to, the old
[\(\mathcal F_{\rm all}\)](CompleteTaggedCredit.md) contribution
on their actual intersection. To compose them, remove precisely
the old cells with both original tags at most \(N^{.080}\) on both
arms (the old quotient floor is \(N^{.110}\)), as well as any other
separately replaced old supports, in the old cell-by-cell certificate.
An independently proved lower on the remaining old cells can
then be kept. There is no assumed sign on that old complement.

## 1. Actual signs and genuinely opposed moments

This is the same exact tag convention as in the
[whole two-by-three comparison](FullTwoByThreeTagCredit.md).
The .003 gate passes, \(Q=0\), and \(S=H+W\) on both physical arms.
By the literal definition \(W\) only clips a negative value
of \(H\) to zero, so \(|S|\le |H|\) and \(S_+=H_+\).
In particular \(W=0\) at every completed rank greater than five.
The completed rank is at least 3 and at most 14: the two
actual small factors cannot multiply to the central argument,
and the quotient of angle at most \(.994+O_J(1/L)\) has
at most 12 factors above \(N^{.080}\). A nonsquarefree row
has both scores zero on that arm.

Put \(a=.080\). On each ordered pair of angle cells of width
.006 starting at .003 (final cell shortened to end at .080),
use actual tags \(p_1<p_2\) of angles \(u,v\), their true
product \(h\), the quotient \(n/h\), and the normalized score
\[
                   A(n)=H(n)/(Luv).
\]
Write \(T=1-u-v\) in the limiting target-log expressions. The
exact two-tag divided difference for its divisor profile is
\(g_{u,v}(s)=[F(s)-F(s+u)-F(s+v)+F(s+u+v)]/(uv)\).
Here \(F\) is the original degree-six half-zero profile.
The ordinary one-integer moments are those of the
[fixed two-tag source](TwoByThreeTagCredit.md), including
the atom of the unit divisor and every actual rank in the
quotient. They are normalized per unit tag-cell volume.
They are not a model for the coupled quotients.

The actual comparison uses the weighted ambient of each pair
of actual tag cells, with weight \(u v u'v'\) on a real unit
row. A one-arm positive weight \(Z\) has actual opposed upper
and lower \(\,U m_i(Z),\,k m_i(Z)\) per unit cell-pair volume
in the scale \(M/L^2\), where
\[
                       U=.575/a,\qquad k=.549/a .
\]
This is exactly the genuine ratio-four transfer of the
[one-by-two proof](OneByTwoTagCredit.md#2-why-the-marginal-inequalities-are-actual),
on finite angular boxes of positive prime-product lengths.
After opening the opposite actual two labels, the tested
moduli \(h e\) satisfy
\(h e\le N^{.160+.320}=N^{.480}\).
Ordinary product Bombieri--Vinogradov, the actual residue \(N\)
and reduced source mask all apply. Unit omissions at the
actual bounded number of tagged/source primes are \(1+o(1)\)
because they are polynomially large. Restoring real squares
in a lower costs \(O(N^{1-.003+o(1)}L^C)\) on the full physical
rows with bounded multiplicities. Mark weights cancel their
own true prime reciprocals and give each ordered cell its
volume, including \(1/2!\) when both tags are in the same bin.
As in the prior chamber proofs, fixed positive floors and
true upper counting justify the own-log normalization at
\(o(M)\) cost; no target-log membership changes.

## 2. A nonnegative part retained even in the clipping cells

The low completed ranks 3 through 7 have \(S\le0\).
At rank three the quotient prime is a giant, and the
only contribution is \(g_{u,v}(0)\) in the above normalization.
This is increasing in each of \(u,v\in[0,.080]\) since
it averages \(F''\) on two actual tag increments and
\(F'''\ge0\) up to .160. Its value at \((.080,.080)\)
is exactly \(-5723854/390625<0\).
At rank four the two quotient angles sum to \(T\ge.840\);
hence \(q=\sum u_i^2\ge T^2/2>11/35\), and the exact
score \((528-1680q)\prod u_i\) is negative.
Rank five has the already proved nonpositive slice,
rank six is negative, and rank seven is nonpositive
by the symmetric box-density formula
in [the original proof, §2](Proof.md#2-the-whole-rough-negative-arm-comparison).
The high even ranks vanish identically. Thus all possible
opposite-sign products have a true odd high rank 9, 11,
or 13 on at least one arm.

Call a pair of tag bins eligible if \(W\) vanishes
throughout it, as certified by their lower endpoint sum
being at least .065 or either upper endpoint being at most
.005. These are sufficient conditions, not an assertion
that the other cells have \(W\) everywhere. In two eligible
arm cells \(i,j\), set \(A_i^-=\min(A,0)\) and likewise
\(A_j^-\). Their product is nonnegative pointwise, and is
exactly the normalized product of the original negative
parts on those rows. With any positive \(d_i,d_j\),
\[
 A_i^-A_j^- =
 -d_j A_i^- -d_i A_j^- -d_i d_j
                +(A_i^-+d_i)(A_j^-+d_j).
\]
Since \(-m_i(A_i^-)\ge[-m_i(A)]_+\) and
\((A_i^-+d_i)^2\le(A+d_i)^2\) pointwise, the actual
same-ambient Cauchy inequality and the preceding true
marginal estimates give the cell contribution lower
\[
 \begin{split}
 \ell_{ij}={}&k\{d_j[-m_i(A)]_++d_i[-m_j(A)]_+\}\\
   &-d_i d_j\,U\min(m_i(1),m_j(1))
         -U\sqrt{m_i((A+d_i)^2)\,m_j((A+d_j)^2)} .
 \end{split}                                                       \tag{1}
\]
All displayed quantities are ordinary single-arm moments;
the Cauchy step itself is on the actual paired rows.
Use \(\max(0,\ell_{ij})\) there. In other cells we retain
the pointwise lower zero for the **negative-negative**
product of the original *clipped* score, not for its
full signed product. The full adverse part from every
cell, including the clipping cells, is paid below.
No score is physically altered and no matter of sign in
a skipped cell is assumed.

## 3. Every opposite sign, using literal ranks

For a low rank, an upper of the magnitude in the \(Luv\)
normalization is as follows. At rank 3 it is \(|g_{u,v}(0)|\).
For rank 4 use
\[
   [1680(q_0+z^2+(T-z)^2)-528]_+\,z(T-z),
   \qquad q_0=u^2+v^2 ,
\]
maximized over \(0\le z\le T\).
For rank 5 choose an actual quotient angle \(z\); the sum of
squares of the two other quotient angles is at most
\((T-z)^2\), and their product is at most \( (T-z)^2/4\).
The upper from the original rank-five slice therefore is
\[
       \left[10080\sqrt{q_*}-1056/\sqrt{q_*}\right]_+
                    z(T-z)^2/4,\qquad q_*=q_0+z^2+(T-z)^2 .
\]
Rank 6 has upper \(40320 (T/4)^4\). For rank 7 the derivative
bound \( |b_7''(0)|\le 2/(z_3 z_4 z_5)\) on the five ordered
quotient angles leaves \(2z_1z_2\le2(T/5)^2\).
Also \(b_7(0)\le\sqrt{10}/T\) by cube slicing and
\(\sum z_i^2\ge T^2/5\). Thus its magnitude has upper
\(2112(T/5)^2+80640(\sqrt{10}/T)(T/5)^5\).
Open the true two labels and use the same genuine \(U\) above
to upper-bound the low-score receiver \(U_{\rm low}\);
\(W\) only decreases its magnitude.

For \(j=7,9,11\), the high quotient rank \(j\) gives
completed rank \(j+2\). The true high
[half-envelope](../sextic_four_small_high/HalfEnvelope.md)
and AM--GM on its least quotient factors give the
normalized absolute upper
\[
             P_j(T)=1056\,2^{j-4}(T/j)^2
                        +80640\,2^{j-6}(T/j)^4 .
\]
The two mandatory tags are the actual least factors.
Multiplying by the ordinary exact quotient-rank density
\(b_{j,a}(T)\) and integrating over the same true tag cells
gives ordinary mass upper \(m_j\). Using \(U P_j(T)\)
on each feasible cell gives the true overlap receiver
\(U_j\) for that high rank. The remainders at fixed rank
and polynomial floors are still actual bounded
squarefree prime-product sources.

All products with any adverse sign and one low arm
cost at most \(2U_{\rm low}\sum_j m_j\,M+o(M)\) on the
two true orientations. The high/high adverse part costs
at most \(\sum_{j,\ell}\min(U_jm_\ell,U_\ell m_j)M+o(M)\).
This sum is over ordered rank pairs; it does not double
the same-rank diagonal. Each factor is obtained in the
cheaper genuine source orientation on the **same** block.
Both upper estimates are gross absolute bounds, so they
are valid on all excluded clipping or low-credit cells,
as well as the cells used in (1).

## 4. Outward replay on the full chamber

Run:

    python3 -OB check_full_two_tag_self.py

The checker locks the exact preceding two-by-three
wrapper by hash, including its already audited occupied
four-class square and one-integer mean, and uses those
routines with the actual two-tag differences. The
ordinary mean and shifted-square moments use 96 ordered
separator bins. Their interval enclosures apply over
each full true tag-angle cell before imposing order.
For each feasible eligible arm, the shift is chosen as
a positive integer from those moment enclosures;
inequality (1) holds for every choice, so no optimality
assumption is made. The low upper in §3 uses the full
ratio grid \(z/T\in[0,1]\) of spacing \(10^{-3}\),
and the high ordinary densities use the same positive
\(10^{-4}\) recurrence. The rank-three sign at .080
is checked exactly with rational arithmetic.

All 91 ordered two-tag cells are present, with total
one-arm tag area \(.077^2/2\). In the numerical double
sum an off-diagonal pair of cells represents the two
separate actual ordered pairs in \(NJ\), each with the
same proven lower from (1) and its real reversed source.
A diagonal pair is counted once. The 1891 strictly
positive lower entries for the negative-negative part
give \(>.196699M+o(M)\). Every adverse product is paid
by the separate stated gross bound \(<.009287M+o(M)\).
The exact outward difference is \(>.187412M+o(M)\),
implying the proposition on the entire literal chamber.
