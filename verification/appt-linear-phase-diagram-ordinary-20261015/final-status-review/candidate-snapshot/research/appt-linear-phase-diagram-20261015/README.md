# Complete linear-order APPT scalar phase diagram

This package determines the complete scalar argmax for every real c>0 and
r>=0, using four separately source-bound complete ordinary internal AI-agent
reads. It refines the already proved all-order entropy VALUE and the original
linear-order actual-spectrum criterion; neither earlier theorem is claimed new.

Use the earlier sharp profile F=B+rP, with

    B=exp(-c L h)[1+h(exp(cL)-1)],
    P=exp[-c(Lh+2L^2/(3(2-L)))], 0<=L<2,
    P(2,h)=0, 0<=h<=1.

The zero-width pole class has value 1+r. The pure bulk point is
(2,h_b(c)), with h_b(c)=1/(2c)-1/(exp(2c)-1) and value b(2c).
The maximum is over the complete compact scalar rectangle, not a sampled grid.

There is exactly one c_star, with certified rational enclosure

    519/2000 < c_star < 13/50,

at which the mixed regime ends. For 0<c<c_star there are two unique real
analytic coexistence curves 0<r_B(c)<b(2c)-1<r_P(c). The strict mixed
phase is unique and nondegenerate throughout its region; both curves meet
at one unique nondegenerate interior triple point. The fixed-c classification is:

| Parameters | Complete scalar maximizing classes |
| --- | --- |
| 0<c<c_star, r<r_B(c) | Pure bulk only |
| 0<c<c_star, r=r_B(c) | Pure bulk and the unique interior mixed point |
| 0<c<c_star, r_B(c)<r<r_P(c) | Unique interior mixed point |
| 0<c<c_star, r=r_P(c) | Unique interior mixed point and pole class |
| 0<c<c_star, r>r_P(c) | Pole class only |
| c=c_star, r=b(2c_star)-1 | Exactly pure bulk, one interior mixed point, and pole class |
| c>=c_star away from that triple point | Pure envelope max{b(2c),1+r}; only bulk below its crossing, only pole above, both at a pure crossing |

At c=c_star the last row is used away from the triple crossing. The pole
class retains all redundant h values at L=0; it is not artificially made a
single scalar pair. The mixed r-window closes linearly at the triple point.
No monotonicity of those curves beyond the proved statements is added.

The proofs and exact trust boundary are:

1. [Last boundary](author-snapshot/LAST_MIXED_BOUNDARY.md): uniform endpoint
   exclusion and an interior tie at every positive mixed boundary.
2. [No islands](author-snapshot/NO_ISLANDS.md): the strict mixed-c set is
   exactly one interval; the fixed-width crossing is proved analytically.
3. [Critical uniqueness](author-snapshot/CRITICAL_UNIQUENESS_CERTIFICATE.md):
   a 73-leaf exact integer certificate plus analytic tails proves the unique
   nondegenerate triple point and the local analytic diagram.
4. [Global mixed phase](author-snapshot/GLOBAL_MIXED_PHASE.md): a separate
   74-leaf certificate with removable K=0 charts proves the two-turn stationary
   structure and every global mixed phase/tie for all c and r.

[The author map](author-snapshot/THEOREM_MAP.md),
[literal source inputs](author-snapshot/SOURCE_INPUTS.json),
[four separate independent decisions](REVIEW.md),
[complete independent evidence](../../verification/appt-linear-phase-diagram-ordinary-20261015/README.md),
and [final source/status/index binding](FINAL_STATUS_BINDING.json) retain the
exact source versions and scope. Old pending/open banners inside immutable
author papers and earlier reviews describe their historical stage. The
current disposition is the four-scope combined report and this status page.

For the original matrices, fix c>0 and finite r>=0 and take arbitrary integers
2<=m<=n, m->infinity, alpha>1, alpha/m->c, 3^alpha/(mn)->r. The already
proved S theorem transfers the full scalar argmax, retaining actual parameter
distance, middle chord/spread loss J and actual peak loss. It gives the stated
one, two or three attainable empirical body laws on actual complex trace-one
APPT densities under every global unitary. At ties sequences may alternate.
One-sided parameter approach to coexistence does not by itself select a phase
at a shrinking gap. Interior peak corrections are not used at L=2.

The earlier [two-threshold and small-c expansions](../appt-linear-phase-geometry-20261015/README.md)
retain their own exact source and review scopes. No old PASS is relabeled as
coverage of the four new proofs. The authored integer engines were fully read
and actually replayed in private scratch; separately written symbolic and
coverage controls and eight real damaged-certificate replay failures are
retained. This is not a newly independent interval engine or a Lean kernel
verification. See [STATUS.md](STATUS.md) and the precise independent reports.

There is no exact finite-dimensional optimizer assertion, simultaneous
c_m->0 physical theorem, complete all-order spectral classification, general
ASEP equivalence, priority certification or new major-problem count.
Yongxian Zhang, South China University of Technology; no external funding;
OpenAI AI assistants assisted. Original rights reserved; third-party notices
kept. No new Lean/audit root, submission, email, Release or DOI.
