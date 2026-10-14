# Full Minc sixth normalized-minimum permanent conjecture

Yongxian Zhang, School of Computer Science and Engineering, South China
University of Technology; mxymmxym1@gmail.com; ORCID0009-0000-3864-3536.
14 October2026. No external funding. OpenAI AI assistants assisted.
Original exposition all rights reserved; prior results remain credited.
Active complete research, no solved theorem, Lean or priority claim.

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
