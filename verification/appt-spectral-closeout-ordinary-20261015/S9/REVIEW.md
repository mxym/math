# S9 independent ordinary mathematical review

Decision: **PASS** for the precise frozen source and scope below. This is an
internal review by a separate AI agent. It is not Lean/kernel verification,
external human peer review, a priority certificate or a completed-major-problem
count. Source reading, proof reconstruction and the separate finite controls
have now been completed; the earlier pause checkpoint correctly remained
INCOMPLETE at its creation and has not been altered.

## Bound source and actual reading

The reviewed PAPER is 16,144 bytes, SHA-256
`812ba384981a4ed6ae1ae62d93723fc0505609b7ecf7997c452331947ffcb078`.
The owner ZIP is
`33f3d58c6a47b0009146ce4e6e25bb65892cd1c52731e58499adf2690dc25cb9`;
the owner manifest is
`417c88541d80f21932880f8ae37fd15772acf9361a7c851f5e88ccafff447932`.
The private owner snapshot has all 23 listed files and its manifest. No author
source, original stored result or timestamp was changed.

I read the entire new PAPER, entire separate COVERAGE_AND_LIMITS, theorem map,
scope/target/source/attempt metadata, author checker and both author preparation
programs. I did not execute, import or copy mathematical helpers from those
programs. The stored author result was fully parsed; all 47 row records and their
diagnostic fields were inspected, but I did not independently recompute their
long exact numerator strings. Its execution remains the author's execution.

The complete old G, L, V, S, SPECTRAL_PROFILE, UNIFORM_PROFILE, small-order,
purity-rigidity and FAST-spectra sources had already received complete readings
in my earlier S5 review. Nine such copies are literally identical to those
earlier inputs, as independently checked. V was reread completely in this review;
G through G22 was reread on resumption. FAST_ORDER_VALUE was newly read completely
in S9. The entire separate GLOBAL source was previously read in its own ordinary
review and matched here byte for byte; its first 141 lines were also reread.
The separate reading ledger records reuse, rather than claiming a fresh complete
reread of each old file. The full PAPER, appendix and V were reread on resumption.

## Exact accepted domain and conclusions

The objects are original complex positive semidefinite trace-one matrices on
`C^m tensor C^n` which remain PPT after **every global unitary**. The domain is
every path with integer `2<=m<=n`, `m->infinity`, real `alpha->infinity`, with no
relation between alpha, m, n or D, and with arbitrary oscillation between their
scales. Alpha may exceed D by an arbitrary factor. The finite estimates apply
after common universal m/alpha thresholds; this is not a finite statement for
every m>=3 and alpha>=2 without thresholds. Fixed m, bounded alpha and alpha=0
are outside S9.

Theorem A retains the actual largest centered kernel and every actual middle
kernel. The omission is exactly the nonnegative sum of the remaining exceptional
kernels divided by D. It is at most
`C alpha^2 (15/16)^alpha` relative to the actual optimum moment **excess**;
the separate relative logarithmic omission is bounded by
`C[alpha^2 (15/16)^(alpha/2)+log(1+alpha)/alpha]`.

Theorem B correctly uses the already credited calibrated finite scalar V. Its
relative excess, not just its raw moment, matches the actual optimum along
every allowed path. Both stated necessary-and-sufficient actual-state criteria
then follow: retained centered excess over `V*-1` for sharp moment-excess
optimality, and `log(1+retained excess)/log V*` for relative entropy optimality.
They are distinct objectives. There is no new VALUE optimization theorem,
instantaneous-argmax distance requirement, or full geometric all-order rigidity
claim hidden in this conclusion.

## Reconstruction of the all-state argument

1. The true inclusive body indices give `N=D-m^2+2`, not D or D-m^2. Its
   endpoints belong to it. Pivot positivity and the width bound are genuine
   necessary all-global-unitary APPT inequalities from G. For nonzero width,
   the actual upper endpoint ensures the size-biased denominator is positive.
   Convexity of `x -> (1+kappa x)^alpha` gives the bounded chord functional.
   At width zero, the conventions multiply a zero coefficient; they never set
   the actual mean to one.
2. Multiplying the definition of Lambda by its actual denominator reconstructs
   the exact body power sum. Subtracting the actual linear mean contribution
   gives the mean of `H_alpha(y)=y^alpha-1-alpha(y-1)`. This is nonnegative.
   Trace conservation then proves exactly `M=C+R_E/D` with `R_E>=0`. The body
   mean before exponentiation and the term `alpha(mu-1)` remain indispensable.
3. G12 gives a uniformly bounded exceptional square sum. G13 gives the actual
   second-peak bound tending to `1+sqrt(2)`, whereas the actual exact peak cap
   is `u_D=3D/(D+2)`. After common m thresholds one may use `v_m<=5/2`,
   `u_D>=8/3`; their ratio is at most 15/16. Taylor's nonnegative integral
   remainder, valid at zero eigenvalues and for real alpha>=2, therefore
   bounds the entire omitted centered sum by
   `C alpha^2 (15/16)^alpha u_D^alpha`. Its cardinality is not multiplied in
   place of its square mass.
4. The actual normalized pole `(I+2vv*)/(D+2)` is APPT for all global unitaries:
   any partially transposed pure projector has minimum eigenvalue at least
   -1/2. Convexity gives `1-t_D^alpha<=alpha(1-t_D)` for every real alpha>=1,
   including alpha much larger than D. Thus its exact centered excess gives
   `M*-1>=u_D^alpha/(2D)` after a universal alpha threshold. No alpha/D
   expansion occurs. This proves the claimed relative excess omission even
   when the optimum excess is arbitrarily small.
5. The extra bound needed before taking logarithms is valid for **every**
   actual state, without assuming its peak is near three. For positive x,
   `H(1+x)/x^2` is nondecreasing. If the actual peak deviation is at least
   1/alpha, compare every other positive exceptional kernel to its kernel;
   the negative kernels are at most `alpha(alpha-1)x^2/2`. If the peak
   deviation is smaller, the positive Taylor factor is at most e. Both cases
   give `R_E<=C alpha^2(1+H(y1))`. Positivity of the retained kernels and
   `D C>=1+H(y1)` imply `M/C<=1+C alpha^2`, hence a logarithmic omission of
   order `log(1+alpha)`.
6. Let chi be the exact `alpha log u_D-log D`. If chi<=0, the spike logarithm
   is at least `exp(chi)/3`, cancelling the same factor in the omission.
   If `0<chi<=(-log(15/16))alpha/2`, it is bounded below by log(3/2) and
   the omission decays exponentially. Above that threshold it is at least
   a fixed positive multiple of alpha, so the actual-peak polynomial
   comparison proves the asserted `log(1+alpha)/alpha` term. These three
   alternatives exhaust all paths and allow arbitrary switching between them.
7. For alpha=o(m), G1 and V18 separately prove the same first nonzero
   `u_D^alpha/D+alpha(alpha-1)/(2m^2)` excess. For alpha>=epsilon m,
   V1 proves a raw moment ratio, and V17 supplies the missing fixed positive
   excess floor: the explicit fair two-point moment is nondecreasing in
   alpha>=1 and tends at epsilon m to cosh(epsilon)>1. Raw accuracy is
   therefore sufficient in that range. A bad all-path subsequence must have
   alpha/m tending to zero or bounded below along a further subsequence;
   both are ruled out. The same contradiction gives uniformity over any
   `alpha>=L_m->infinity`, all n>=m. Concavity of log(1+x) transfers the
   positive excess ratio to the positive logarithm ratio, even when both
   excesses vanish. This supplies the bridge before either iff is invoked.

## Appendix, actual-state attainability and attribution

The moving-tie construction is a separate consequence of the already proved
GLOBAL phase theorem and L value theorem, not an input to the core reduction.
At fixed c=1/10, the rigorously established lower coexistence threshold is
positive, strictly below the upper threshold, and has a distinct interior
mixed coexistence point of width below two. For
`n=ceil(3^(cm)/(m(r_B+1/m)))`, integer rounding changes `3^(cm)/D` by an
exponentially smaller amount than 1/m. For all large m the instantaneous
parameter is strictly within the mixed interval and its unique maximizer tends
to that interior point.

The actual integer-rank projection density in the appendix is all-unitary APPT:
the negative Schmidt trace of any projection is at least `-(m-1)/2`. Its rank
is nearest to the true fair-bulk maximizing fraction times D; both multiplicities
are much larger than m^2, so the actual body contains both levels. Its moment
tends to the pure-bulk value, which is also the limiting optimum at coexistence.
Its width is exactly two. It is consequently entropy-nearoptimal while remaining
a positive distance from the instantaneous exact mixed argmax. The correct older
S theorem uses the entire argmax of the **limit** pair, including the bulk point.
The appendix does not falsify that older theorem and does not support a new
instantaneous-distance substitute. All fixed-c limit and physical-loss ranges
of the cited S/GLOBAL results remain intact.

The appendix coverage table is explicitly a historical coverage plan, not a
certified assembly. Its frozen statements about other scopes being pending
describe its original capture time; they are neither dependencies nor current
dispositions of those other later-reviewed sources. FAST branch minima, the
sublinear weighted sum, and actual peak/width compatibility are not equated.
The manuscript credits G/V/FAST and the independent phase geometry accurately;
it makes no historical-first, full FEI-like problem, or new-major-count claim.

## Independently executed controls and real failure record

Own source `reviewer_checks.py`, SHA-256
`e6535a3cd26a8145dc83b08303220229c6feba491e3c07b356e3dfecd1acc55c`,
was written independently in this directory without author imports or AST reuse.
Its first actual run, `reviewer-runs/20261015T160112.905104Z`, passed.
The actual result has SHA-256
`6684412c0c2136b21538dbb81b01500069af02d98f3bc75d15c98c5b79467df1`.
Python 3.10.12, Sympy 1.9, Mpmath 1.2.1, 420 decimal digits were used.

The run checked 10 symbolic kernel/centering controls, 216 exact
Fraction-based compressed actual integer spectra and 108 stable real-order
controls spanning all three chi regimes, including noninteger alpha and
alpha far above D. Kernels and logarithmic differences use expm1/log1p rather
than subtracting tiny deficits from one. The exact body membership and all
integer multiplicities remain present. Projection, positive three-level,
pure-pole, singular-hole and uniform states are actual APPT families, with
the preceding analytic witness bounds giving their status; no finite sample
certifies the full APPT set or evaluates its exact maximum.

A separate actual three-level path uses even k, m=k^2, alpha=k,
`n=m 3^(2k)` and full spectral weights 1/4,1/2,1/4 at `1+1/m,1,1-1/m`.
It is normalized `I+Y` with `0<=Y<=2/(m-1) I`, so the negative Schmidt
trace proves all-unitary APPT. Its actual Lambda is O(k/m)->0, yet its
moment excess is asymptotically half the optimal first nonzero excess.
Dropping Lambda changes that ratio to one. The four exact examples k=4,8,16,32
have actual ratios approximately .49930,.50030,.50012,.50003, while omission
gives .99845,1.00060,1.00023,1.00007. The comparison scale is the proved
asymptotic G1 scale, explicitly **not** a finite exact optimum.

Seven intentionally false variants triggered seven real AssertionErrors, each
with its actual traceback preserved: omit the actual chord loss; assume width
zero implies unit mean; assume it implies zero centered body; omit the linear
mean centering; discard the other exceptional kernels exactly; replace the
exact u_D by three at alpha=D^2; and force sharp peak accuracy from a small
relative logarithmic peak loss in an actual positive pole family. There was
no unexpected control failure and no author mathematical source finding in
this S9 review. Passing samples do not supply the universal constants or
replace the all-state proof above. No fabricated or unexecuted failure is
reported as an actual run.

## Preservation and limits of this decision

REVIEW.json, READING_LEDGER.json and REPORT_BINDINGS.json bind the decision,
source reading, actual program/result/trace bytes and private preservation.
The old pause checkpoint and other purely operational capture records are
classified separately; a future public package may omit those private
operational files if the omission and their hashes are disclosed. Their
original private bytes remain preserved. This report does not warrant any
future publication layout, link validation or Git transport.

No Rglob, fixed-m/fixed-D extension, S8, new conjecture, new Lean theorem or
expanded audit is covered. Rglob requires its own new full review. No author
or root tree, old review, Gaussian worktree or old audit input was modified.
