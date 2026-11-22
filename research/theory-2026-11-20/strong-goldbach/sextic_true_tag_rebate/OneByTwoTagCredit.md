# One genuine tag against two: a signed covariance credit

Keep the exact original sextic \(H\), score \(S=G_b+W\),
\(b=.003\), real interval \(J\Subset(1/3,2/3)\), fixed prescribed
even \(N\), and physical pairing \(x+y=N,\ x\in NJ,\ (x,N)=1\)
of [the last comparison](QBoundaryMixedChambers.md).
Write \(L=\log N\), \(M=|J|N\mathfrak S(N)\).
No profile, rough correction or medium compensation is changed.

All tag angles in the definition of the new chamber use denominator
\(L\). The left arm has one actual least prime \(p\) with angle
\(t\in(.003,.026]\); require every prime of \(x/p\) to exceed
\(N^{a_{\rm L}}\), where \(a_{\rm L}=.080\) for \(t\le .006\)
and \(a_{\rm L}=.108\) for \(t>.006\).
The right arm has two actual least primes \(q_1<q_2\), with angles
\(u,v\in(.006,.080]\) in different ordered cells of width .002
starting at .006 and wholly contained in that interval. Require \(P^-(y/(q_1q_2))>N^.080\).
Use only cells whose **lower** tag sum exceeds .065 and
whose upper tag sum is \(<.156\).
Cut the left \(t\) interval into width .001 cells. Let
\(\mathcal D\) be the union of the resulting cell products selected by
the finite outward lower-bound rule in §4, with squarefree coordinates.
There is no further rank, angular-sign or residue restriction on
either quotient.

**Proposition.** The signed sum of the original \(S(x)S(y)\) over
\(\mathcal D\) and its reflection exceeds \(.0355M+o(M)\).
Both orientations are disjoint from each other and from
\(\mathcal E_Q,\mathcal F_{\rm all},\mathcal C_Q,\mathcal C_Q^{\rm op}\)
in the last comparison. Thus, with the exact signed exterior now
omitting these two additional chambers,
\[
                 R_J\ge 1.0855M+\mathcal R_{\rm out}+o(M).
\]
No lower bound for \(\mathcal R_{\rm out}\), or percentage of a
Goldbach proof, follows.

## 1. A common physical measure and the signed dual

All tag products are target units. On both arms the .003 gate passes,
\(Q=0\), and \(W=0\): the sum of the two least angles on each arm
exceeds .065, while \(W\) requires that sum to be at most .065.
Thus \(S=H\) on both arms. Outside squarefree coordinates the
products in this chamber are already zero. The actual least tags
uniquely specify the side and cell. In particular, the left side has
exactly one prime at most \(N^{.080}\), while the right side has
two. Both arms have a prime below \(N^{.1251}\); this excludes
\(\mathcal E_Q\) and both mixed chambers.
For \(t\le .006\) the left first tag is too small for
\(\mathcal F_{\rm all}\). For \(t>.006\) its second prime
exceeds \(N^{.108}\). In the original .002 grid of
\(\mathcal F_{\rm all}\), the strict upper cell endpoint \(<.110\)
means the second tag itself is at most \(N^{.108}\). This proves
the remaining disjointness without imposing a model on the quotients.

Fix one interval product \(I_t\times I_u\times I_v\). Its actual
paired measure \(\lambda_N\) assigns weight \(tuv\) to each genuine
row in the specified ambient. Define there
\[
                  A=\frac{H(x)}{Lt},\qquad
                  B=\frac{H(y)}{Luv}.
\]
The signed contribution is exactly \(L^2\int AB\,d\lambda_N\).
For an arbitrary fixed \(d>0\), pointwise \(AB=A(B+d)-dA\).
Hence its lower uses the genuine same-ambient inequality
\[
 \int AB\,d\lambda_N
   \ge -d\int A\,d\lambda_N
       -\sqrt{\int A^2\,d\lambda_N\int(B+d)^2\,d\lambda_N}.        \tag{1}
\]
This is Cauchy–Schwarz on the real \(x+y=N\) rows; there is
no assertion that the two quotients are independent.

Write \(\mathsf m_{\rm L}(f),\mathsf m_{\rm R}(g)\) for ordinary
one-arm angular moments at fixed tag angles, for the corresponding
true rough floors. Their formula is in §3. If \(m_{\rm L}(f)\)
resp. \(m_{\rm R}(g)\) denote their uniform-measure averages over
the corresponding tag cells, the actual inequalities in §2 give
in units \(|I_t||I_u||I_v|M/L^2\)
\[
 \begin{split}
 \int A &\le k_{\rm R}m_{\rm L}(A)
                   +(U_{\rm R}-k_{\rm R})m_{\rm L}(A_+)+o(1),\\
 \int A^2 &\le U_{\rm R}m_{\rm L}(A^2)+o(1),\\
 \int (B+d)^2 &\le U_{\rm L}m_{\rm R}((B+d)^2)+o(1),
 \end{split}                                                     \tag{2}
\]
where \(k_i=.549/a_i\), \(U_i=.575/a_i\). The first line subtracts the
true lower for \(A_-\) from the true upper for \(A_+\). A uniform
pointwise bound on each **ordinary** moment therefore certifies its
cell average. The signed cell lower per unit three-angle volume is
\[
 d[-k_{\rm R}m_{\rm L}(A)-(U_{\rm R}-k_{\rm R})m_{\rm L}(A_+)]
   -\sqrt{U_{\rm R}U_{\rm L}\,m_{\rm L}(A^2)m_{\rm R}((B+d)^2)}.   \tag{3}
\]

## 2. Why the marginal inequalities are actual

Let \(Z\ge0\) be any one of the nonnegative real source weights
in (2), including \(A_-\) and the shifted square. All ranks in each
one-arm source are bounded, because its tag and quotient floors are
positive fixed constants. Its varying angular functions are bounded
and piecewise continuous on the finite factor simplices. Use genuine
product BV for these true angular products in the same way as in
[the positive block, §2](RoughPositiveCredit.md) and
[the two-tag proof, §2](TaggedNegativeCredit.md): first use compact
product angle boxes and then approximate the bounded weight.
The measures of the fixed angular box boundaries are zero for the
real limiting one-arm densities. One can obtain upper and lower
bounds with nonnegative step weights; the ordinary errors tend to
zero after using their genuine sieve upper on the same receivers.
The quotient-prime terms (quotient rank one) use the ordinary last
true prime slot, with no continuum assumption on its factorization.

Open the opposite actual tag product \(h\), and sieve the opposite
physical quotient at the actual cutoff \(N^a\) with linear-sieve
level \(N^{4a}\). The actual moduli are \(hd\) and
\[
       \frac{\log h}{L}+4a\le .160+.320<.499
             \quad\text{or}\quad .026+4(.108)<.499.
\]
This includes every retained cell and both reflected orientations.
The residue is the real \(N\), with reduced source and target units.
The exact outer model has \(1/\varphi(h)\); the inner model has
\(1/(p-1)\) at tested primes off \(Nxh\) and zero on the exclusions.
Coinciding tags across the two actual coordinates are impossible
in the unit rows. In the modeled sums, each such exclusion affects
the tag reciprocal harmonic by \(o(1)\) uniformly since the source
has fixed rank and all factors are \(>N^.003\).
The tested tag primes and source prime exclusions change the
remaining local product by \(1+o(1)\); target factors stay in
\(\mathfrak S(N)\). The weight of each genuine named tag is its own
angle; its reciprocal prime harmonic tends to the corresponding
interval length. The actual arithmetic errors summed over \(h,d\)
are below-root product-BV errors with fixed divisor multiplicity
of \(hd\), not progression claims about each fixed pair of tags.

The lower sieve omits receiver tag primes. Restore the physical
rough condition, and also require a squarefree receiver, by
discarding actual \(p^2\mid N-x\) with \(p>N^.003\).
The true floor bound
\(\sum_{N^.003<p\le\sqrt N}(N/p^2+1)
=O(N^{1-.003}+N^{1/2})\) pays this for both orientations,
even with divisor-bounded tag multiplicity and bounded score
weights. The upper may simply ignore these rows. Both marginals
therefore bound the **same** measure of §1. Central log changes
from own to target angles affect each bounded-rank angular score
by \(o(1)\) uniformly at the fixed positive floors, and preserve
(2) by the same actual upper. In particular this does not
change any hard tag or rough cutoff.

At relative sieve parameter 4 the true lower coefficient is
\((\log3)/(2a)>.549/a\). The true upper coefficient is
\[
   \frac{1+\int_0^1\log(1+r)/(2+r)\,dr}{2a}<.575/a.
\]
These are the usual linear sieve lower and upper formulas
with the Mertens constant canceled, as in the preceding real
receiver proofs. The two elementary strict inequalities are
also verified in the checker (positive atanh truncation and
an outward monotone rectangle bound).

## 3. The unopposed ordinary moment calculation

For a quotient rough floor \(a\), put
\[
 \kappa_a(ds)=1_{s\ge a}\frac{ds}{s},\qquad
 \mathsf B_a^\pm=\sum_{j\ge0}\frac{(\pm1)^j}{j!}\kappa_a^{*j}.
\]
Only finitely many terms affect the bounded angular ranges here,
and \(j=0\) is an atom at zero. For a fixed tag list, let \(T\)
be the remaining quotient angle (\(1-t\) or \(1-u-v\)).
The ordinary unweighted quotient rank \(r\) measure is exactly
the density at \(T\) of \(\kappa_a^{*r}/r!\). This is the
limiting actual one-arm prime harmonic/PNT count in finite
boxes of the product coordinates, with factor \(1/r!\) for
unordered distinct true quotient primes. The finite-dimensional
same mass with any angular integrand is defined by inserting
that integrand in the convolution integral.

The score attached to a quotient factor list \(\boldsymbol w\)
is \(\sum_I(-1)^{|I|}g(\sum_{i\in I}w_i)\), where \(I\) ranges over
its actual index subsets and
\[
 \begin{split}
 g_{\rm L}(s)&=(F(s)-F(s+t))/t,\\
 g_{\rm R}(s)&=(F(s)-F(s+u)-F(s+v)+F(s+u+v))/(uv),\\
 F(s)&=44(1/2-s)_+^4-112(1/2-s)_+^6 .
 \end{split}
\]
For the ordinary **first** moment, assign each quotient prime to
the chosen subset or its complement. If their total angles are
\(z,n\), the integral is the density at \(T\) of
\(g(z)\mathsf B_a^-(dz)\mathsf B_a^+(dn)\), \(z+n=T\).
For the **second** moment, assign each quotient prime to neither
subset, the first only, the second only, or both. If their respective
angles are \(n,x_1,x_2,z\), use
\[
 \begin{split}
 &g_d(x_1+z)\,g_d(x_2+z)\,
 \mathsf B_a^+(dn)\mathsf B_a^-(dx_1)
                 \mathsf B_a^-(dx_2)\mathsf B_a^+(dz),\\
 &\hspace{30mm}n+x_1+x_2+z=T,\qquad g_d(s)=g(s)+d\,1_{s=0}.
 \end{split}                                                     \tag{4}
\]
For \(A^2\), take \(d=0\).
The multinomial factors are exactly the four factorials from the
four classes, and the signs agree including for primes in both
subsets. The formula is a partition of the factors of **one**
integer, not a replacement of the actual opposite coordinate.

For the ordinary left positive moment, ranks 4–7 contribute
zero. In rank 4 this follows from
\(t^2+(1-t)^2/3>11/35\) at \(t\le .026\) and the exact
sextic rank-four formula. The other signs follow from
[the original slice identities](Proof.md), and even ranks above
six vanish. At rank 2 the positive moment is \(g_{\rm L}(0)/T\).
At rank 3 it is the positive part of
\(g_{\rm L}(0)-g_{\rm L}(w)-g_{\rm L}(T-w)\) integrated with
\(dw/(2w(T-w))\) for \(a\le w\le T-a\); the full two-factor
subset is beyond \(1/2\). The higher odd ranks \(r\ge9\)
use the original slice envelope after extracting the actual
least tag. For \(j=r-1\), the remaining \(j\)-factor simplex
mass and normalized pointwise cap are, respectively,
\[
 \frac{(T-ja)_+^{j-1}}{j!(j-1)!\,a^j},\qquad
 1056\,2^{r-5}(T/j)^3+80640\,2^{r-7}(T/j)^5.                     \tag{5}
\]
There are no ranks above 13 on the left. All ranks permitted by
the true roughness, including zero score ranks that contribute
to the shifted square, are retained in (4).

## 4. Outward checker and whole-cell selection

The attached [checker](check_one_by_two_tag_credit.cpp) evaluates
these ordinary moments by interval arithmetic. For reproducibility:

```sh
c++ -O3 -std=c++17 -ffp-contract=off -fno-fast-math \
  check_one_by_two_tag_credit.cpp -o /tmp/one_by_two
/tmp/one_by_two
```

Here are the interval rules used. If \(b_\pm(s)\) are the continuous
densities of \(\mathsf B_a^\pm\) on \(s\ge a\), multiplying each
convolution by its total variable gives
\[
    s b_\pm(s)=\pm\left(1+\int_a^{s-a}b_\pm(r)\,dr\right)
\]
with empty prefix below \(2a\).
The plus density is nonnegative and the minus density equals
\(-\rho(s/a-1)/s\le0\) with \(\rho\) the ordinary Dickman
function (or use its nonnegative integral recurrence).
On a \(10^{-4}\) grid, \(a\) is an exact grid multiple.
The two predecessor prefix intervals at a grid bin for \(s-a\)
bracket the integral, with the order reversed for the minus
density, and give enclosing density intervals by the displayed
recurrence. Atoms in (4) are enumerated separately.

For \(m\) occupied continuous classes, write their angles as
\(a+(T-ma)v_i\), where the \(v_i\) are differences of increasing
ordered separators between 0 and 1. Partition the \(m-1\)
separators into 256 equal bins. Bins that contain \(j\) separators have
exact volume factor \(1/j!\); the full Jacobian is
\((T-ma)^{m-1}\). Enclose the integrand over the *whole* bin,
using the exact cancellation of shared separators in each needed
subset sum. This is outward quadrature, not center sampling.
The score profile intervals either use first- and second-derivative
means for the one-tag divided difference, or the exact centered
quadratic and quartic uniform moments in the two-tag divided
difference of \(F\). If that latter difference straddles the
profile endpoint, use the range of \(F''\) on the full real
interval. The one-tag Taylor bound uses
\(\sup_{s\ge0}|F'''(s)|\le2400\).
The implementation uses IEEE binary64 with every elementary
round-to-nearest arithmetic endpoint widened by more than
eight times its relative unit roundoff plus an absolute reserve.
It also checks the final square-root upper by squaring it
outward. No transcendental quadrature is assumed.

The fixed \(d\) for a right tag cell with center sum \(s\) is
\(\lfloor99-380s\rfloor\), an integer rule. Take all cell
products for which the checker lower for (3) is \(>10\).
It includes 4465 whole actual interval products among 11086 candidates,
of total three-angle volume \(1.786\cdot10^{-5}\), and gives for the
two reflected orientations
\[
        2\sum_{\rm accepted\ cells}
                |I_t||I_u||I_v|\,(\text{certified lower for (3)})
                       >.0357971.
\]
All intervals, ranks and selected cells are fixed before \(N\) tends
to infinity. Here reflection uses \(1-J\), of the same length,
and no selected product is counted twice. Combining with the
prior exact exterior comparison proves the proposition.
