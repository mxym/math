# Exact phase-5 spectral theorem map

Status: author complete, new ordinary independent full read pending.

Original domain: every actual complex PSD trace-one density APPT after every
global unitary on C^m tensor C^n, 2<=m<=n,m->infinity,real alpha->infinity,
alpha/m->0. No aspect-ratio restriction. Use moment EXCESS and first-nonzero
relative entropy deficit, not raw moment or entropy divided by log D.

| Item | Necessary and sufficient claim | Main proof input |
|---|---|---|
| A | (M-1)/(M*-1)->1 iff wp min(1,h)+wb min(1,db)->0 | Uniform actual-state kernel identity, variance overshoot control and exact body-spread identity |
| B | e/E->1 iff wp min(1,h/(1+chi_plus))+wb min(1,db)->0 | A on bounded-above chi; separate actual-peak necessity and state-dependent log reduction for chi->+infinity |
| C | On each liminf wb>0 subsequence, db->0 iff full actual empirical W_2 law tends to equal atoms at -1,+1 | QE=O1, gamma->infinity, exact trace centering and vanishing exceptional second moment |
| D | When both weights stay positive and nearoptimality holds, alpha eta_m->0 and (m/alpha)(2-L)->infinity | Actual L7 peak/width bound with h->0; no independently attached peak |

Definitions: U=u_D^alpha,V=alpha(alpha-1)gamma/2,wp=U/(U+V),wb=V/(U+V),
chi=log(U/D),h=alpha log(u_D/y_1). Actual L,theta,J are computed on the
original middle interval; db=(2-L)+|theta-1/2|+J. J is explicitly retained.

The weighted SUM handles all limits U/V->0,finite positive,infinity and
arbitrary oscillations. If both terms matter, both must saturate. Coarse
o(U+V) errors are not logged in the large-chi proof; it proves y_1->3 and
then a stronger actual-peak-relative identity first. Total Q/gamma may
exceed one on negligible-weight subsequences, so its weighted overshoot
is controlled explicitly rather than canceled against a negative loss.

Credited value: G1 already proves M*-1~(U+V)/D uniformly in this range.
Credited physical inputs: G7-G19 actual witnesses, bounded middle interval,
QE=O1, Q<=zeta_m(gamma+8), exact cap u_D, second-eigenvalue gap, and actual
L7 peak/width coupling. Actual middle definitions agree with S; no prior
full proof is claimed as newly audited or formalized.

Counterexamples in PAPER section 9 are original actual matrices. A balanced
pure pole refutes a branch-min criterion; a three-level operator-interval
state refutes deleting J; a reduced-strength pole separates entropy and
moment scales. Their physical witnesses are explained or credited. The
18 exact finite controls supplement these analytic examples and check an
exact nonzero actual-middle mean term; they do not prove infinite limits.

Excluded: complete fixed-m synthesis, fixed finite order with unrestricted
growing aspect, all zero-order rigidity limits, alpha/m->positive c or
infinity, every finite optimizer, eigenbasis rigidity, APPT=ASEP, complete
Lean, an expanded old audit, historical priority, external human peer
review, external submission, or a new-major count. The scope is exactly
the growing-sublinear all-aspect spectral gap identified above.
