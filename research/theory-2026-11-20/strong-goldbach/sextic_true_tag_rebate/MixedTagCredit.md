# A genuine signed mixed chamber in the same sharp sextic residual

Keep the fixed even \(N\), actual ordered unit pairing, \(L\),
central \(J\) and \(M=|J|N\mathfrak S(N)\) as before. Keep
**exactly** \(S=G_b+W\) of [the full medium cohort](FullMediumCohort.md),
with \(b=.003\), and the same genuine rough and medium corrections.
Write \(\mathcal E\) for [the priced positive block](RoughPositiveCredit.md)
and \(\mathcal F_{\rm all}\) for [the priced complete two-tag chamber](CompleteTaggedCredit.md).
Their comparison is \(R_J\ge .883M\) plus the literal sum of
\(S(x)S(y)\) outside those two sets, up to \(o(M)\).

Define the actual chamber \(\mathcal C\) by:
- In \(x\), all prime factors exceed \(N^{.150}\).
- In \(y=N-x\), there is one actual prime \(p\) of angle
  \(.080<(\log p)/L\le.125\), and every true factor of \(y/p\)
  exceeds \(N^{.170}\).

There is no completed-rank restriction in this chamber.
In particular \(p\) is its unique least prime and its only tag.
Let \(\mathcal C^{\rm op}\) impose the two conditions in the
opposite orientation. The four actual sets
\(\mathcal E,\mathcal F_{\rm all},\mathcal C,\mathcal C^{\rm op}\)
are pairwise disjoint.

**Theorem.** The full signed sum on \(\mathcal C\cup\mathcal C^{\rm op}\)
is \(>.113M+o(M)\). If \(\mathcal R_{\rm out}\) denotes the
literal original \(S(x)S(y)\) sum on all remaining ordered rows,
\[
                  R_J\ge .996M+\mathcal R_{\rm out}+o(M).
\]
This is a positive actual mixed-sign block, not a sign of
\(\mathcal R_{\rm out}\) and not a binary positivity conclusion.

## 1. Real supports and signs

Use \(a=.150,\ c=.170,\ \theta=.499\).
On the \(a\)-rough arm the exact \(S\) is the positive part
of the original \(H\), since \(Q\) clips every negative there
and \(W\) and the tiny gate do not change that arm. One has
\(0\le S(n)\le\log n\). For a prime or nonsquarefree row
the score is zero. On rank two the normalized \(H\) is
\(1-F(u)\le1\); on rank three the same upper follows from
monotonicity of \(F\) in the giant case and from positivity
of \(F\) in the no-giant case. The positive rank-four
formula has coefficient at most \(528-1680/4=108\),
times a product at most \(4^{-4}\).
Rank five and six are negative before clipping, and
higher ranks are not \(a\)-rough.

On the tagged arm, \(S=H\): the tag is below the \(Q\)
cut, the next prime exceeds \(N^{.170}\), so that the
two-tag \(W\) cannot occur, and the .003 gate is passed.
The actual tag is below every quotient prime, and the
completed rank is at most six because \(6c>1-.080\).
The value is zero on nonsquarefree rows. Rank two is
positive. Rank three is also strictly positive on this
whole actual support. In the giant case the target limit
with tag angle \(t\) and smaller quotient angle \(u\)
gives \(1-F(t)-F(u)+F(t+u)\). Since \(F\) is convex on
\([.170,.5]\), its minimum in \(u\) is at \(c=.170\).
The derivative in \(t\) at \(c\) is positive:
\(F'(t+c)\ge F'(.25)\), whereas by \(F'''>0\) on
\([.080,.125]\), \(F'(t)\le\max(F'(.080),F'(.125))<F'(.25)\).
The value at \(t=.080,u=c\) is strictly positive.
In the no-giant case both other angles are at least
\(.5-t\ge.375\), and \(1-F(.080)-2F(.375)>0\)
bounds the normalized score below. These margin
checks are rational and survive the actual own-log
changes. Thus any adverse negative products in
\(\mathcal C\) come from tagged ranks 4, 5, or 6;
they will all be charged below. Adverse rank is
not inferred from a random or model pair.

## 2. A weighted capacity inequality on the literal mixed chamber

Let the actual tagged cells be \((i/1000,(i+1)/1000]\),
\(80\le i\le124\), of width \(\Delta=.001\).
Give each row in the cell's common actual chamber
weight \(t=\log p/L\) (on the physically marked right arm).
Amplitudes are divided by \(\log n\) on the left and
by \(t\log n\) on the right. For a threshold \(u\ge0\)
on the left select a finite-box witness \(L_u\) from
the actual squarefree rank-two/three source with
all factors above \(N^a\) and amplitude \(>u\).
Write \(\underline m_L(u)\) for the certified ordinary
lower mass from those boxes. For a threshold \(v\ge0\)
on the right select finite-box witnesses \(R_{i,v}\)
from actual ranks two or three with the true tag in
cell \(i\), actual quotient floor \(c\), and amplitude
\(>v\). Write \(\underline m_{R,i}(v)\) for their
ordinary lower mass **per unit tag angle** with the
\(t\) weight included. Each source is a literal
finite-rank product of genuine primes, at a fixed
positive angular floor.

On this exact chamber we bound the weighted intersection
from below by the right selected weighted marginal
minus the left complementary weighted marginal.
The right source \(R_{i,v}\) paired to the left rough
receiver has lower coefficient \(k_L\underline m_{R,i}(v)\)
in units \(\Delta M/L^2\), where
\[
                     k_L=\frac{2}{\theta}
                                \log(\theta/a-1).
\]
This is the genuine below-root product-BV linear
lower at level \(N^\theta\) and cut \(N^a\),
as in [the positive block, §2](RoughPositiveCredit.md).
The right tag remains part of its actual source, not a
hypothetical independent integer.

For the opposite bound take as **source** every left
\(a\)-rough integer outside \(L_u\). Up to power-small
large squares this is a finite union of exact prime-product
shapes (including true primes), with a fixed finite-box
mask. Its ordinary mass is at most
\(3.8-\underline m_L(u)\). In fact the ordinary full
rough density in these units is
\(\omega(1/a)/a\le.57/a=3.8\).
To see the elementary \(.57\), on \([2,3]\) use
\((1+\log(t-1))/t\le.57\), since the maximum of the
difference in the numerator is
\(\log(1/.57)-.57<0\). Integrate the Buchstab
recurrence beyond 3 to propagate that bound.

For this complement as a genuine source, open the actual
right tag \(p\) in cell \(i\), and upper-sift its literal
quotient at exponent \(c\). Set \(\tau_i=(i+1)/1000\),
take level exponent \(\theta-\tau_i\), and apply true
product BV on the left source at actual moduli
\(pd\le N^\theta\) and residue \(N\).
Here \(2<(\theta-\tau_i)/c<3\), so its actual upper
coefficient in the same units \(\Delta M/L^2\) is
\[
                       U_i=\frac2{\theta-\tau_i}.
\]
It uses one external \(1/\varphi(p)\); in the true
tag harmonic the physical \(t\) cancels \(dt/t\).
Omitting \(p\) from the upper quotient sieve only
enlarges the set; thus no lower estimate is made from
artificial squared tags. Genuine tag primes dividing
\(N\) are removed; their reciprocal harmonic is
power-small. The actual reduced unit masks keep the
source and target; all source labels have fixed
polynomial size so their excluded Euler factors
alter \(\mathfrak S(N)\) only by \(1+o(1)\) in either
marginal. At primes of \(N\) the true excluded roots
are accounted for by that singular series. At fixed
finitely many amplitude boxes, ordinary below-root
product BV for the actual prime slots absorbs the
divisor multiplicity of the true joined moduli
and all spatial cutoffs. All source statements and
absolute bounds apply to the reflected \(1-J\) as
well, which has the identical spatial length.

In particular the capacity argument is the exact
inclusion inequality in one weighted physical ambient:
the positive right marginal pairs either with \(L_u\)
or with its complement. It gives lower for the true
intersection, in units \(\Delta M/L^2\),
\[
            [\,k_L\underline m_{R,i}(v)
                  -U_i(3.8-\underline m_L(u))\,]_+.              \tag{2}
\]
The complementary upper is a second true sieve estimate
on the same chamber. It neither assumes independence
of the two completed ranks nor requires a uniform
distribution statement for an individual fixed tag.

## 3. Price all actual signs with the same weights

Sum (2) by the two layer grids of widths \(1/100\)
and \(1/20\) in the left normalized amplitude and the
right amplitude divided by its actual tag. Each row
is counted with a product of step totals at most its
positive product divided by \(\log x\log y\) and
by the actual tag. Restoring the chamber's positive
weight \(t\) and the two logs gives a rigorous lower
for the positive contribution: \(\log x\log y/L^2=
1+O_J(1/L)\). All these are finitely many amplitude
events and fixed angle boxes.

The left boxes are the same sorted rank-two/three
geometry as in the positive-block proof. On the right
at rank two the per-unit-tag density is \(1/(1-t)\),
and the score for a cell \([t_-,t_+]\) is bounded
below by \((1-F(t_-))/t_+\).
At rank three order the two quotient angles
\(q_1\le q_2=1-t-q_1\). Use wholly ordered .001
intervals for \(q_1\), with quotient floor \(c\).
The identity \(H/\log n=1-\psi(t)-\psi(q_1)-\psi(q_2)\)
uses \(\psi(s)=F(s)-F(1-s)\), a decreasing function.
All lower endpoints in the subtracted terms give a
lower; divide by \(t_+\). For the ordinary density
\(1/(q_1q_2)\) enlarge each denominator angle to
its own upper endpoint. Only strict amplitude
inequalities are used, so true own-log changes
and the genuine fixed spatial interval do not cross
any counted amplitude endpoint. Small interior cell
fences may equivalently be taken before the limits
to restore every physical box. The attached rational
enumeration gives the true positive lower
\(>.115328M+o(M)\) for one orientation.

For the adverse part use \(0\le S(x)\le\log x\)
on the untagged rough arm and the actual nonnegative
tagged source \([-H(y)]_+\). Product BV and the genuine
upper linear sieve of the left roughness give multiplier
at most \(2/(3a)\) times its true ordinary mass \(M\):
indeed \(\theta/a>3\), and \(F_{\rm upper}\) decreases,
with \(e^{-\gamma_E}F_{\rm upper}(3)=2/3\).
The source is of exact bounded rank and positive
floor, with actual tags; all own-log or square losses
are handled on the same source as above.

After dividing the right weight by the actual tag
\(t\), the three adverse ordinary densities per unit
tag angle have the following explicit bounds. Put
\(t_+=t_-+\Delta\) and \(R_j=1-t_--jc\).
The factor \(t\) then cancels the tagged reciprocal
harmonic in this calculation.
- In rank 4 use the exact even formula:
  the other three angle factors in it cancel their
  ordinary reciprocal denominators. Integrate
  \([1680(t_+^2+3c^2+2cR_3+R_3^2\sum_i v_i^2)-528]_+\)
  on the three-variable ordinary \(\sum v_i=1\) simplex,
  with the factor \(R_3^2/3!\).
  The formula enlarges both the available total and all
  positive coefficient terms; it remains an upper for
  every true angle \(t\) of the tag cell.
- In rank 5 the analogous cancellation, the true slice
  upper \(C_5(q)=10080\sqrt q-1056/\sqrt q\), and its
  concavity give upper
  \[
      \frac{R_4^3}{4!\,3!}\,
        C_5(t_+^2+4c^2+2cR_4+2R_4^2/5).
  \]
  The mean \(\sum v_i^2=2/5\) is on the ordinary
  four-dimensional constrained simplex.
- In rank 6 the exact product formula gives
  \(40320R_5^4/(5!\,4!)\).

These upper bounds include the **entire** negative contribution
in the only possible tagged adverse ranks. The rank-4 integral
is upper-enclosed on \(1/256\) squares of the scaled simplex:
extend the determined last angle to the full squares at the
boundary and take the largest squared-angle sum of each square's
vertices, using convexity. The areas outside the actual simplex
only enlarge the upper. List the true reciprocal prime densities
once per sorted angle box and include the factorials above,
never an independent-prime assumption on both arms.
The [exact rational check](check_mixed_tag_credit.py) gives
the total adverse upper \(<.058450M+o(M)\) per orientation.
It verifies the score signs, ordinary box floors, polynomial
and root bounds, and strict net margin.
In particular it gives a signed lower \(>.113M+o(M)\)
on the two actual reflected chambers together (unrounded
enclosure \(>.11375717M\)).

Finally the chambers are disjoint from each other since
one least angle is \(>.150\) and the other is \(\le.125\).
They do not meet the existing \(\mathcal E\), which needs both
least angles \(>.150\), or the existing \(\mathcal F_{\rm all}\),
which needs two actual factors below \(.110\) on both arms.
Subtract only the two new whole chambers from the same outside
sum in the .883 inequality and add their proved lower. This
changes neither the score nor any prior prime/rough/medium debit.
