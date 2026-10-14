# Full Minc sixth normalized-minimum permanent conjecture

Yongxian Zhang, School of Computer Science and Engineering, South China
University of Technology; mxymmxym1@gmail.com; ORCID0009-0000-3864-3536.
14 October2026. No external funding. OpenAI AI assistants assisted.
Original exposition all rights reserved; prior results remain credited.
Preserved closed complete research stage; no solved theorem, Lean or priority claim.

## M0. Full object and time boundary

Source screening started02:35:50 UTC after the separate300-line APPT
service ended. The whole-domain mathematical phase starts02:39:11 UTC
after primary scopes and the old-route ledger were checked. Both active
source screening and mathematics count; service/preservation and actual
recovery/idle intervals do not. Without a substantial full result, preserve
and switch at45-90 effective minutes.

For every integer n>=2, let Lambda(n,k) contain all actual binary n-by-n
matrices with every row and column sum k,1<=k<=n. Let

    m(n,k)=min_{A in Lambda(n,k)} per A,
    mtilde(n,k)=m(n,k)/k^n.

The complete conjecture compares every adjacent degree1<=k<n for each n.
Original wording says decreasing without a specified weak/strict reading;
this stage's positive target is strict mtilde(n,k+1)<mtilde(n,k) everywhere,
which covers either reading. A strict reverse inequality between global
minima disproves even the weak reading. An equality alone or two arbitrary
matrices does not settle that weak whole conjecture. No selected matrix
class, order, fixed degree or asymptotic band is substituted.

## M1. Primary scope and route exclusions

The full [Wanless2007 primary paper](https://users.monash.edu.au/~iwanless/papers/mincconj6LAMA.pdf)
was read in its474-line rendering for formulation and scope. Conjecture1.1
and its three proved partial ranges are distinct from the maximum version.
The [current primary author entry](https://yair-lavi.com/mincs-list/conjecture-6/index.html)
and bounded current-primary searches do not identify a complete all-n/all-k
solution. The1965 original was traced bibliographically, not retrieved.
Exact read/access limits are recorded in MINC_SIXTH_SOURCES.json.

Known finite/sparse/dense cases remain credited inputs. In particular, the
primary2007 paper already disproves the stronger every-nested-extension
claim with A=I+P and B=I+P+P^2 for a full n-cycle, n>=9. That existing
obstruction is not new and does not refute the global-minimum conjecture.
The integral-margin minimum-is-binary assertion mentioned as a possible
stronger input is not assumed established here. This object differs from
the closed subgroup Lieb/Marcus and PSD Chollet routes, the Ryser design
minimizer assertion and the Lih-Wang chord. Old permanent-on-top or
Bapat-Sunder counterexamples and rank/order results do not answer it.

The complete map was prepared before this attempt. No new major result
or numerical campaign is claimed at activation.


## M2. Exact whole-size complement-perfect-matching average

Let A be any actual binary k-regular matrix,1<=k<n, let E be all ones,
and put C=E-A. Since C is(n-k)-regular, Hall's theorem gives per C>0.
Every actual permutation matrix P supported in C gives an admissible
binary(k+1)-regular matrix A+P. Expanding the permanent by the set I
of rows using an A entry and their column set J gives the exact identity

    sum_{P<=C permutation} per(A+P)
      =sum_{I,J: |I|=|J|}
          per A[I,J] per C[I,J] per C[I^c,J^c].           (M1)

For each selected A partial matching on I,J, the other rows must use
P on I^c,J^c; there are per C[I^c,J^c] choices for those forced entries
and per C[I,J] completions of the same P. These are disjoint actual
complement assignments. The terms at I empty/full are per C and
(per A)(per C). There is no surrogate distribution or independence.

A sufficient stronger full route would prove, for every actual A (or
just for every actual global k-minimizer),

    sum_{I,J} per A[I,J] per C[I,J] per C[I^c,J^c]
       <(per C)(per A)((k+1)/k)^n.                       (M2)

Then at least one actual complement P has the required normalized strict
bound and the complete minimum conjecture follows. No sign of M2 is
established. A reverse M2 only rejects this averaging proof, not the
existence of a better extension or the global-minimum conjecture.

For a negative complete result one can instead certify an actual current
A with permanent U and a valid lower bound L on every actual next-degree
matrix such that L/(k+1)^n>U/k^n. This proves a strict reverse comparison
between global minima even if A itself is not a global minimizer. Two
arbitrary candidates or a finite collection of next-degree matrices do
not furnish that universal lower certificate.


## M3. Exact controls and a rigorously false coefficientwise shortcut

The deterministic complement-average controls cover56 selected actual
cyclic matrices through order12. All full permanents agree with independent
DP and inclusion-exclusion. For21 controls, every actual complement P was
enumerated,3055 total, and the direct sum agrees with M1. None reverses
the proposed average inequality. This is finite-input checking, not its
whole-domain proof. The published2007 n=9 every-extension obstruction
is independently confirmed: per A=2, per B=78, with normalized reverse
numerator78*2^9-2*3^9=570. It is credited prior work, not our counterexample
to the global-minimum conjecture.

For uniform actual P<=C write f_P(z)=per(A+zP). Its averaged linear
coefficient is exactly

    E f_P'(0)=sum_(i,j) C_ij per C(i|j) per A(i|j)/per C. (M3)

A sufficient but false coefficientwise shortcut would bound the coefficient
of z^r divided by per A by binom(n,r)/k^r for every r. Already r=1 fails
on an actual binary regular family. The family and its matching counts
are existing Jerrum/Wanless input from the visually read primary
[Wanless1999 pages273-276](https://users.monash.edu.au/~iwanless/papers/HolDjokLAA.pdf),
not a newly found Holens-Djokovic counterexample.

For fixed k and f use row vertices s,u_(a,b,c) and column vertices
t,v_(a,b,c),1<=a,b<=k,1<=c<=f. In each(a,c) block include every edge
u_(a,b,c)->v_(a,beta,c) except(b,beta)=(1,1); bridge
u_(a,1,c)->v_(a,1,c+1), c<f; and include
s->v_(a,1,1), u_(a,1,f)->t. This is actual k-regular binary of order
n=k^2 f+1, with A_st=0. The published exact counts are

    per A=k(k-1)^((k-1)f)((k-1)!)^(kf),
    per A(s|t)=[(k-1)(k-1)!]^(kf).                       (M4)

They can also be seen by selecting the one branch matched to s and t:
all its bridges are forced, whereas every other branch uses only its
within-block edges. When s,t are deleted, no bridge can be used. The
actual integer DP verifies both counts at k=3,f=1,2,24; independent
inclusion-exclusion additionally verifies f=1,2. The largest actual order
217 has only15315 live DP states, but this is a check of an existing family.

Here is a separate complete elementary marginal lemma. If actual binary
C is d-regular with d>n/2, every supported edge e=(s,t) has uniform
perfect-matching probability at least1/[1+(n-1)^2]. Given a matching P
not containing e, put u=P(s), P(v)=t. If C_vu=1, a two-row swap inserts e.
Otherwise there are at least2d-n>0 rows w with both C_(v,P(w))=1 and
C_(w,u)=1. Neither s nor v is eligible, and the three-row replacement
s->t,v->P(w),w->u inserts e. Choose one deterministically. A fixed
output containing e has at most1+(n-1)+(n-1)(n-2)=1+(n-1)^2 preimages,
including itself. Counting inputs/outputs proves the asserted probability.
No unknown independence or matching-correlation property is invoked.

For the actual k=3,f=24 matrix, n=217 and its complement degree214>n/2.
M3's(s,t) term and M4 therefore give

    E f_P'(0)/per A >=2^24/[3(n^2+1)] > n/3,            (M5)

because2^24-n(n^2+1)=6,558,686>0. Thus the universal coefficientwise
binomial sufficient route is rigorously false on the actual admissible
object. This neither reverses the total average at z=1 nor compares
global minima; M2 and the complete Minc-sixth conjecture remain unproved.

## M4. Authorized service boundary

At02:56:02 UTC mathematical work reaches a safe checkpoint, approximately
20m10s effective since source screening02:35:50, excluding about2s
previous preservation. No full theorem or legal global-minimum reverse
comparison. All preservation verification, recording and the requested
new304-line APPT root-tracking service after this boundary are excluded.
The same complete target resumes after that independent service; this
is a service pause, not a closed or solved research stage.

 
## M5. Exact coupled subset kernels and balanced-distribution variant

For each j let P_j(A) be the matrix of all order-j permanents, indexed by
j-row subsets I and j-column subsets J, and put

    T_j(C)_(I,J)=per C[I,J] per C[I^c,J^c]/per C.          (M6)

Laplace expansion on a fixed I proves each row sum one; expansion on a
fixed J proves each column sum one. T_j(C) is the probability that the
same uniform actual complement matching sends I to J. Consequently

    E_(P<=C)per(A+P)=sum_j <P_j(A),T_j(C)>.               (M7)

All these nonnegative doubly stochastic kernels share the same underlying
distribution on actual full complement matchings. They cannot be replaced
by independently selected arbitrary stochastic kernels. The j=0,n terms
are1 and per A, and j=1 is zero because A and C have disjoint supports.
Doubly stochastic kernels/positive summands alone give no full M2 sign.

Regular complement degree does not make the uniform matching marginal
equal to C/(n-k). At actual n=5,k=2, A=I+P for a full cycle and C=E-A,
per A=2, per C=13, but supported marginal values are4/13 and5/13, not1/3.
All13 complement matchings were directly enumerated; independent DP and
inclusion-exclusion agree, and all six subset kernels have row/column
sums exactly one. M7 gives the actual average164/13. This is a precise
probability-shortcut obstruction, not a full-conjecture reverse comparison.

A different distribution with uniform edge marginals is always available:
Hall removal repeatedly decomposes the d-regular complement C into d
disjoint actual perfect matchings, d=n-k. Their equal mixture has mean C/d.
Thus another sufficient whole-domain route is to find a probability
distribution lambda on complement matchings with sum lambda_P P=C/d and

    sum lambda_P per(A+P) < per A ((k+1)/k)^n.            (M8)

The minimum of this linear objective over the indicated finite matching
distribution polytope is an exact well-defined full-object obligation.
No bound of M8, universal or on every global k-minimizer, is proved here.
An extension route is sufficient and stronger than the original minimum
comparison; failing all extensions of one A still would not compare every
actual next-degree matrix.

## M6. Safe resumed discovery scope

The requested304-line APPT service, final four-line delta and preservation
completed03:11:47 UTC; the full02:56:02-03:11:47 interval is excluded.
The same complete mathematical target resumed with about20m10s effective
already accumulated. A single bounded exact route screen now checked124
actual regular matrices, including explicit incidence/graph controls and
fixed-seed binary trades lowering the current permanent. All actual A/C
full permanents agree independently with DP and inclusion-exclusion.
No reverse total average was found. Observed degree-three values include
24,33,42,60,83 at orders7-11, and114 at12; none is independently certified
a global minimum here, and the latter is not the primary reported113.
These finite inputs neither solve M2 nor the original whole-degree target.

 
## M7. Complete-domain base bridges and a standard-bound limitation

Order n=1 has no adjacent degree pair, so it is vacuous. All nonvacuous
original orders and degrees are still retained in the n>=2,1<=k<n target.
The finite sets Lambda(n,k) are nonempty, for example by sums of k
disjoint cyclic permutation matrices; hence every actual minimum is attained.

At k=1 any A is a permutation, and any complement P is disjoint from it.
After permuting rows, per(A+P)=2^(number of relative cycles), each cycle
having length at least two. This is at most2^(n/2)<2^n, proving the first
normalized step. At k=n-1, A=E-P0, every augmenting complement is P0,
and the normalized full matrix n!/n^n is strictly below per(A/(n-1))
by the credited van der Waerden theorem and its unique uniform equality.
These are elementary/already established bridges, not new major results.

The standard Schrijver lower bound by itself cannot give a negative
global-minimum certificate at any adjacent degree. Write the normalized
lower base as a_k=((k-1)/k)^(k-1), a_1=1. For real x>1,

    d[(x-1)log(1-1/x)]/dx=log(1-1/x)+1/x<0.              (M9)

Thus a_(k+1)<a_k. Every actual current-degree permanent U satisfies
U/k^n>=a_k^n>a_(k+1)^n. Consequently the next-degree Schrijver bound is
already below every possible current candidate; it cannot strictly
separate the global minima in the negative direction. A reverse complete
result needs a stronger universal certificate, not another finite
comparison or the same standard bound. No such certificate is obtained.

The positive complete gap remains M2 or another rigorously valid
construction on every actual global minimizer. Actual legality, exact
parameter scope, independent integer controls, kernel positivity and
standard lower bounds have not supplied the missing total quantitative
comparison. The stage still has no full proof or complete negative witness.

 
## M8. Why continuous and minimizer-trade relaxations do not close it

For an actual global k-minimizer A, any actual Q<=A and P<=E-A are
permutation matrices and A-Q+P is still binary k-regular. Global optimality
therefore gives per(A-Q+P)>=per A. This is only a lower bound for the
same-degree traded matrix. It supplies no upper bound for per(A+P), and
does not prove the needed normalized next-degree comparison.

The unrestricted real regular-margin relaxation is strictly too loose
at every k<n. By the credited van der Waerden theorem,

    min_(X>=0, all margins k)per X=k^n n!/n^n,
    m(n,k)>k^n n!/n^n for every1<=k<n.                   (M10)

The unique real minimizer is X=kJ_n. Every actual binary k-regular matrix
at k<n has zeros, hence is nonuniform after dividing by k and has strict
van der Waerden inequality. The class is finite, so its actual minimum
remains strictly above the real relaxation value. The normalized real
minimum is constant with degree, not the original binary sequence.
Fractional interpolation/continuous descent consequently cannot be
accepted as an original witness or used to round back without a new
rigorous discrete bound. No such bound, complete sign or legal
global-minimum reverse certificate has been found in this stage.

 
Raw minimum monotonicity is elementary: every actual(k+1)-regular B
contains a perfect matching Q, and B-Q is actual k-regular with
per(B-Q)<=per B. Hence m(n,k)<=m(n,k+1). The missing complete assertion
is the upper growth bound m(n,k+1)/m(n,k)<((k+1)/k)^n; raw monotonicity
supplies the opposite one-sided comparison and cannot close it.

 
## M9. Honest natural stage boundary

The complete original-object stage closes03:36:49 UTC after approximately
45m12s effective research, counting current-primary/formulation work and
mathematics, excluding preservation and the full15m45 authorized service.
The all-n/all-degree positive assertion and a strict reverse comparison
between global binary minima remain unresolved. Exact identities and
shortcut obstructions, existing credited matching families and finite
nonviolations are exploration with zero new major-conjecture results.
MINC_SIXTH_STAGE_CLOSED.json records the actual timer, source bindings and
scope. After the requested independent366-line APPT service, screen a
different genuinely unclosed full original target before activation.
