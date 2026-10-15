# Independent ordinary review of the total-dimension diverging-order reduction

Status: **PASS**. Decision: **PASS** for the precise Rglob source and the
separate scopes below. This is complete ordinary mathematical reading by a
separate internal AI agent, supported by independently written finite controls.
It is not a Lean/kernel result, external human peer review, priority certificate,
effective-constant computation or new major-problem count. S9's PASS has not been
automatically extended to this new manuscript.

## Frozen source and actual reading

The canonical PAPER is 16,699 bytes, SHA-256
`75f5d9226c447c8acb4c6e609ac805e57a399a2a0dbfbaf8a3047bd5c22748e9`.
Owner ZIP SHA-256:
`06b892c0fc87cbd74ecfddcf2538d4e98d1687ab1117c1756610516c6e40cb2c`.
Owner manifest SHA-256:
`44a14627b4e90cdd959b60c68019a2a878289662eb03dd0cf6058cadb1b64cc9`.
All 44 listed owner files and the manifest were captured privately and verified.
The copies of PAPER in the two actual author runs are literal historical copies,
not additional mathematical sources. None of the source bytes or author UTCs
was modified.

I read all 366 lines of the new PAPER, all 127 lines of MATHEMATICAL_NOTES,
and all new map, README, research log, primary-scope and credited-input metadata.
The notes remain a preserved earlier working derivation; their pre-freeze banner
does not turn them into a second current theorem source. I also read the entire
213-line current author checker, the complete first-to-second executed checker
diff, both stored result summaries and all twelve author expected-error traces.
Both stored JSON results were fully parsed; I do not claim independent
recomputation of every printed numeric diagnostic. No author checker was
executed or imported in this review.

The fixed-m exact A manuscript (all 387 lines), its ordinary REVIEW and theorem
map were read completely here. The all-order historical review JSON was read
completely. Previously complete scientific readings of the captured G, V, FAST,
growing-order and X sources were reused only after exact byte equality; V and
G's relevant physical/value sections had also just been reread in S9. X's
qubit section and surrounding context, lines 95--277, and its primary-scope record
were reread here. S9's PAPER/map/source list are literally the inputs just
independently reviewed, but the core argument reproduced in Rglob was itself
checked. Fifteen credited objects were hash/size checked, with twelve literal
equalities to earlier private read inputs. The remaining three historical
review/map objects received the fresh readings specified above. The full
READING_LEDGER distinguishes these fresh and reused scopes.

## What this decision covers

All matrices are original complex PSD trace-one densities on `C^m tensor C^n`
which remain PPT after **every global unitary**, with integer `2<=m<=n`.
The objectives are moment **excess** divided by the actual maximum excess,
and entropy deficit divided by the actual maximal deficit. They are not raw
moment ratios or entropy divided by log D.

* Lemma 1 gives existence of a universal bounded omitted square mass and a
  universal strict ratio `rho0<1` for omitted nonleading eigenvalues. It
  does not give an effective numerical rho0 or dimension cutoff.
* Theorem 2 is uniform over **every dimension pair, including fixed D**,
  after one universal finite-order threshold. Its actual centered peak/body
  expression has the stated relative moment-excess and relative-log omission
  bounds as finite real alpha tends to infinity.
* Theorem 3 and the explicit benchmarked iff tests require **both D and finite
  alpha to diverge**. Equivalently, for each epsilon there are joint-tail
  bounds N and A, valid for every D>=N and alpha>=A and every dimension split.
  The smaller dimension may be fixed, grow, or alternate. This does not claim
  the T benchmark at fixed total dimension or for bounded positive orders.
* The infinite-order entropy ratio is separately exact for every dimension
  pair: `log y1/log u_D`. No infinite power moment or infinite excess is
  defined by substitution. Finite-diverging/infinite endpoint alternation
  uses the explicitly separate entropy definitions.

The two finite-dimensional cases and their quantifiers have been checked
separately; Theorem 2's fixed-D validity is not used to extend Theorem 3 beyond
its joint limit. This is an observable spectral reduction, not an all-order
classification of every body law or every finite optimizer.

## Universal physical gap: the new dimension argument

The actual body is `B={max(2,R),...,D-S+1}`. It excludes index one in every
case. Its exact size is `D-m^2+2` for m>=3 and `D-3` for qubits, including the
one-entry D=4 body. Pivot positivity follows from the actual maximally
entangled necessary witness for m>=3 and the rank-two tail witness for m=2.
It is never assumed from a candidate spectral ansatz.

For large m, the old **uniform-in-n** G12/G13 bounds supply bounded
exceptional square mass and `y2<=5/2`, while `u_D>=8/3`. This uses one fixed
large-m threshold, independent of order and state. For the finite list
`3<=m<M0`, bounded exceptional cardinality and `0<=y<=3` bound its square mass.
The finite star bound gives `g1^2+g2^2<=4`, and ordering gives `g1>=g2>=0`;
therefore `a2<=g2<=sqrt(2)`. The true pivot satisfies `b<=1/j`, yielding
`y2<=(1+sqrt(2))D/(D-S+1)`. Since m now ranges over a finite list, one large-D
threshold puts this below 5/2 simultaneously on that whole list.

Only finitely many dimension pairs with m>=3 remain. The original APPT set
is closed in the compact density set, so its continuous ordered second
eigenvalue attains a maximum. That maximum cannot equal u_D. Such equality
would also give y1=u_D, making both steps in the rank-two tail inequality
equalities. The mean of the three least tail eigenvalues would equal the mean
of all D-1 tail eigenvalues. Because `D-1>3` here, ordering forces **every**
tail eigenvalue equal to y1/3. This contradicts y2=y1. A finite maximum of
these strict ratios is below one. This is a valid use of compactness at each
fixed finite-dimensional pair, followed by a finite maximum; it is not an
unsupported compactness assertion over changing dimensions.

For m=2 the proof deliberately does not use a universal second-peak gap.
Only the bottom two indices D-1,D are omitted in addition to the retained
top coordinate. Their normalized values are at most D/(D-1), whose ratio
to u_D is at most `(D+2)/(3(D-1))<=2/3`. Their exceptional square mass is
uniformly bounded as well. Combining the finite maximum, 15/16 and 2/3 proves
the existence of the stated universal rho0. The manuscript correctly leaves
its value non-effective.

This distinction is necessary: the actual qubit APPT state proportional to
`I+2P`, with projection rank two, has
`y2/u_D=(D+2)/(D+4)->1`. Its second peak belongs to the retained body.
Neither this family nor any remaining finite D pair invalidates the proved
gap for the **omitted** coordinates.

## Centering, both error scales, and the reproduced S9 method

At nonzero actual width both endpoints lie in B, so the size-biased chord
denominator is positive. Its definition reconstructs the exact body power
sum. At width zero theta=0 and Lambda=1 have zero prefactors, while the
actual mean still need not be one. This includes the one-point qubit body.
Trace conservation and nonnegative kernels give exactly `M=K+R_E/D`, with
R_E the remaining exceptional centered kernels. Both actual linear mean
terms remain in K at arbitrarily large alpha/D.

The real-power integral remainder holds at zero eigenvalues and alpha>=2.
The new uniform square-mass/gap lemma bounds R_E by
`C alpha^2 rho0^alpha u_D^alpha`. The genuine all-unitary APPT spike has exact
cap u_D and gives `D(M*-1)>=u_D^alpha-1-2alpha`. Since u_D>=2 for all D>=4,
one universal order threshold bounds the right side below by u_D^alpha/2.
This proves the sharp **excess** estimate without any dimension limit,
including arbitrarily tiny optimum excess.

The state-relative polynomial comparison was independently checked rather
than inherited by a PASS label. For positive deviations the kernel divided
by their square is nondecreasing. Splitting the actual largest deviation
at 1/alpha compares every omitted positive kernel to the actual peak kernel,
or bounds its multiplier by e. Negative deviations use the quadratic Taylor
bound. The uniform omitted square mass consequently gives
`R_E<=C alpha^2(1+H(y1))`. Positivity of retained kernels gives
`D K>=1+H(y1)`, hence `M/K<=1+C alpha^2` for every state, including those far
from optimality and those with negative holes or constant bodies.

For chi=`alpha log u_D-log D`, split at zero and at
`(-log rho0)alpha/2`. The spike log lower bound cancels exp(chi) when chi<=0;
the intermediate range has a positive constant log denominator and decaying
numerator; the final range has log M* bounded below by a fixed multiple of
alpha and uses the polynomial actual-peak comparison. The stated logarithmic
error follows with universal constants. No logarithm of an uncontrolled
optimum-relative additive error, or a premature assumption `actual y1->3`,
appears. These arguments explicitly credit and reproduce the S9 method;
the new all-dimension gap and qubit adjustment are distinct additions.

## Fixed-m sharp benchmark bridge and the joint quantifier

For fixed m>=3 let `q=(m+1)/(m-1)`, `t=q-1` and `delta=t/2`. Direct
differentiation gives the manuscript's nonnegative bulk width derivative,
including theta=0 and theta=1. The displayed eta derivative is positive at
positive width and eta(t)=2(m-2)/(m-1)<2.

Split all widths, without discarding either boundary, at delta. In the lower
part the bulk is at most `(1+delta)^alpha` and the calibrated head at most R_D;
in the upper part the bulk is at most F_q and the head at most
`R_D[(3-eta(delta))/3]^alpha`. The explicit theta=1/alpha choice gives
`F_q>=q^alpha/(alpha exp(t))`. Thus the first extra bulk is exponentially
small relative to F_q, and the second extra head exponentially small relative
to R_D. Lower choices at width t and width zero attain at least F_q and R_D.
This proves `T/max(F_q,R_D)->1` uniformly in D. A factor-two sandwich or
relative log accuracy from X would not suffice for this step.

The captured ordinary A5 theorem has exactly the needed quantifier: for
each fixed m>=3, **one** eventual D0(m) works at **every** order. At those
dimensions the actual maximum is exactly the maximum of the hole moment,
the integer-rank q-projection moment, and the pole moment. Its full proof,
earlier ordinary review and source map were read; no order-dependent sequence
of thresholds is substituted for this theorem.

Choose once `q<u0<3` and A large enough. Above A log D, q-based bulk and the
hole are at most `D(q/u_D)^alpha` times R_D, hence at most R_D/D eventually.
The pole ratio to R_D is exactly `1+(D-1)/3^alpha`, uniformly tending to one.
This branch retains u_D exactly and allows arbitrary alpha/D, including
alpha much larger than D.

Below A log D with alpha diverging, the exact continuous theta optimum is
as printed and is asymptotic to 1/(t alpha). Its nearest integer j/D is
interior eventually, since D/alpha diverges in this band. The joining interval
has theta at least half theta*, and the absolute log-moment Hessian is bounded
by `1/theta^2+alpha t^2=O_m(alpha^2)`. The stationary first derivative vanishes;
Taylor therefore gives `0<=log F_q-log F_int<=C_m alpha^2/D^2=o(1)`.
The actual winning integer rank need not be the nearest rank for this lower
bound; it only improves it. Ranks remain genuine integers and ties are not
replaced by a fractional rank. Hole moment tends to one, pole lies between
R_D and R_D+1, and F_q diverges. These estimates prove the required raw
moment ratio against max(F_q,R_D), and therefore against T.

The half-rank all-unitary APPT projection gives a dimension-uniform fixed-m
order-two moment above one. Convexity of the scalar log-moment, through its
zero at order one, gives exponential growth in alpha-1 thereafter. Thus
M* diverges on every fixed-m diverging-order path, so raw moment and **excess**
relative comparisons coincide here. At growing m, instead, G1/V18 retain
the first nonzero excess for alpha=o(m), and V1/V17 give the positive-excess
floor for alpha>=epsilon m. This avoids the raw-moment fallacy when M*->1.

Qubits use exact T=M* for D>=6 via X's explicit A/B/C compact families with
their actual integer multiplicities and ranges. Song--Chen Theorem 10 is an
**ordinary external theorem input**; X's mapping and trace-convexity argument
were checked in their original ordinary scope and reread where used. The
external full proof is not newly audited. In particular this uses trace
convexity for scalar powers, not false operator convexity for alpha>2.
The finite D=4 pair is outside Theorem 3's joint-D limit, while remaining
inside the independently proved Theorem 2.

Any bad joint D/alpha sequence has a subsequence with m diverging, or a
subsequence with one fixed integer m. The growing-m and all fixed-m cases
above rule out each possibility; m=2 has exact calibration. This proves the
stated joint-tail uniformity over all dimension splits. Concavity of
log(1+x) transfers the positive excess ratio to the positive log ratio.
Combining these benchmarks with the all-state nonnegative omissions proves
both directions of both actual-state iff tests. No instantaneous exact
argmax-distance replacement or independent saturation of peak and body is
assumed. The infinite-order entropy endpoint follows separately from the
attainable exact peak cap.

## Independently executed diagnostics and honest failure history

Own `reviewer_checks.py`, SHA-256
`4861731d347f1d29cd38a533cc8526084c3274b114355bb876e3469d136db7e2`,
was written independently, with no author helper import or AST reuse. Its
first mathematical run `reviewer-runs/20261015T161243.469602Z` passed.
Actual RESULT SHA-256:
`edc994607758df3a0d1d58c24ce97483e99f7caa7ece8fcdafbee2c0a375247a`.
Runtime: Python 3.10.12, Sympy 1.9, Mpmath 1.2.1, 300 decimal digits.

It checked 7 exact symbolic derivative/normalization identities, 390 exact
compressed integer-spectrum cases, 63 qubit-family boundary/normalization
cases, and 99 stable real-order centered/actual-peak cases. Fixed D=4 and
noninteger orders far above D were retained. The exact body interval and
counts, constant nonunit body means and nonzero actual chord losses are
present. Positive bounded-perturbation, projection, pole and singular-hole
families are actual APPT by their analytic all-Schmidt witness estimates;
the qubit boundary families retain the explicitly credited external
membership/classification input.

There were also 48 fixed-m scalar parameter triples with 13 width samples
and endpoints/stationary fractions, 32 physical integer-rank Hessian controls,
and 16 high-order calibrated peak-band controls. These are finite diagnostics
of an all-width analytic proof. They do not compute unknown finite APPT
maxima, certify a global continuous-width extremum or produce the
non-effective universal compactness constant. The sampled local omitted gaps
are explicitly labelled local rather than mistaken for rho0.

Seven false variants caused seven actual preserved AssertionErrors: count
the qubit peak twice; force a false uniform qubit second-peak gap; erase a
nonunit one-point body mean; replace an actual three-level body by its endpoint
chord; infer sharp peak accuracy from relative logarithmic accuracy; replace
u_D by three at large order; and assert the continuous maximum equals the
integer value with no rounding loss. The last diagnostic checks a numerically
nonzero finite lattice loss and is not an interval-certified root calculation.
The log-versus-moment physical countercontrol compares actual pole-family
data, not an asserted computed finite M*. There was no unexpected mathematical
control failure and no author mathematical source finding.

Two **real reviewer capture failures** preceded mathematical controls. The
first capture assumed only one file in the archive could share the new PAPER
hash; the archive properly contains its canonical copy plus two author-run
copies. The second assumed the manifest's files field was a list; it is a
path-to-hash dictionary. Both original capture programs, actual tool error
text, recorded UTCs, diagnostics and file hashes are preserved under
capture-failures. Only private capture code was corrected, after which all
45 source files verified. The failure records are not discarded or relabelled
as mathematical counterexamples, and no source correction was needed.

The two author PASS runs, their distinct executed source hashes and twelve
expected-error traces remain author evidence, not my independent execution.
Their first finite family set had no nonzero chord-loss case; my independent
actual three-level controls specifically exercise that omission-sensitive
case. Their numeric samples and mine do not replace the universal proof.

## Bound conclusion and stopping boundary

REVIEW.json, READING_LEDGER.json and REPORT_BINDINGS.json bind the exact
source, read scope, result and actual failure bytes. Historical pending
banners remain unedited; future public status wrappers need their own byte
binding. No future layout, transport, public link check or publication is
guaranteed here. No external raw primary text or tool excerpt was newly
copied into this review.

This decision covers only the new Rglob paper at the bound SHA. It does not
cover S8, any later manuscript, a full geometric all-positive-order assembly,
effective smallest thresholds, eigenbasis rigidity, absolute separability,
new Lean work or an expanded old audit. Frozen S9 and earlier reports remain
unchanged. The two finite requested reviews, S9 and Rglob, are complete;
further research is stopped pending an explicit separate request.
