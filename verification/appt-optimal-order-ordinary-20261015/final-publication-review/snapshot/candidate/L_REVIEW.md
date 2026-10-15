# Independent ordinary review of the new L0-L2 optimization theorem

15 October 2026, Asia/Shanghai. Reviewer: the resumed independent review
agent, separate from the author/root. This is an internal AI-agent ordinary
mathematical review, not external human peer review, Lean verification,
an expansion of old audits, a global numerical certificate, or a priority
certificate. Old I/J/K PASS records do not automatically cover L.

**Conclusion: PASS for the complete revised L0-L2 target bound below. No
additional hypothesis or target narrowing is needed.** During this read
the reviewer supplied explicit cancellation identities for the joint
alpha=1/small-contrast singularities; the author adopted and disclosed
them. This contribution is transparent, not described as a blind review.

## Frozen source and actual read scope

The original complete PAPER (192 lines), THEOREM_MAP (35 lines) and author
checks (156 lines) were read. After the explicit kernel identities were
added, the entire revised PAPER (205 lines) and REVIEW_HISTORY (20 lines)
were read. The map and checks remained byte-identical. Final SHA-256:

- PAPER.md: `c76f83bf7bb4a42eee81cafbab6fd8cdb430312fc7026503acbc86a9dfbda58b`
- THEOREM_MAP.md: `4e52fe369cdfb0214aa7396eb0a8de608e6891cb093cf3de78e0ad085b1a7fc7`
- checks.py: `745f56a514b46ea2f115ec80561c61ad3dc6a68ccb1471da11a1e63d052877c5`
- REVIEW_HISTORY.md: `59ad47b0ea1fb37225308afeaef58021fa858dd5695db3a057eff2cb0c808f9e`

The original source SHA-256
`1245dcc7b67f488303aae61f96828cf8004b2525e97e4cccf5036df5d8b251ea`
is retained in snapshot/L-v1/. The revised source is in snapshot/L/.
No author source was edited by this reviewer.

The full I313/J230/K336 mathematical inputs were already read and reviewed
in this same agent session. For L's new compact-interval and final-onset
uses, the targeted proof ranges I69-253, J126-205 and K263-317 were
additionally reread. This does not claim a fresh read of every old file or
rerun of its controls. PUBLISHED_INPUT_COMPARISON.json records a read-only
byte comparison against commit
`5522928ae7e8b1960dedb790d7f3506f3b1f5f0b`: the published I/J/K sources
have exactly the previously reviewed mathematics plus their separately
bound status differences. Their whole differences match the published
FINAL_STATUS.diff files; the final bindings and reports are retained in
snapshot/published-inputs/.

## L0: a genuine compact-uniform LOWER barrier, including alpha=1

J's two analytic critical-parameter branches are interior at every
positive finite order. Their images on the preassigned compact I are
compact interior sets. Thus both signs' head masses, z parameters,
positive D_s values and next coefficients have common bounds, including
a common separation of the negative raw head from zero. The construction
does not assume a compact-uniform classification of arbitrary optimizers
outside the coupled K neighborhood.

The explicit revised (5a) identities are correct. If q=1+kappa and
w=psi_alpha(q)/kappa, then

    Q=alpha*kappa+(alpha-1)*kappa*w,
    H=alpha*h+(alpha-1)*DeltaPsi,
    (kappa*H-Q*h)/(Q-kappa)=(DeltaPsi-h*w)/(1+w).

The stationary trace factor is
(1+w)/(1+(alpha-1)*w/alpha). Substituting it into I's body formula gives
exactly B=w*ell((alpha-1)*w/alpha)-log(1+w). At alpha=1 these reduce to
the separately proved von Neumann body/gain formulas. The kernel is
jointly analytic for alpha>0 and positive raw bases; its double zero at
y=1 makes w analytic at kappa=0. The apparent alpha-1 denominator has
been eliminated, rather than merely filled by pointwise continuity.
All remaining denominators are uniformly protected on a neighborhood of
the compact parameter set. This proves the common analytic Taylor
remainders, including through alpha=1, actually needed by (6).

The uniform crossing expansion therefore gives a bounded next coefficient
for BOTH signs. Choosing a single B0 such that B0+a_s>=2, and then a
common sufficiently large m, places
n=floor(d_alpha*m^2-B0*m) at least order m below the selected winning
sign's real crossing. The entire real segment is in uniformly comparable
cubic total dimensions. The exact negative n derivative is bounded below
in magnitude by c*m^-5 there, since g stays uniformly positive. This
gives the stated c*m^-4 real head advantage over the real bulk envelope.

The real maximizing rank has a common fraction 1/2+O(1/m), including at
alpha=1 via the regular stationary trace formula. Both adjacent integers
are consequently physical. Its rounding loss O(m^-8) cannot consume the
m^-4 advantage. The rounded state is actual all-global-unitary APPT by
the order-independent physical boundary proof. It beats even the REAL
bulk upper bound, hence beats the true integer bulk. This is an actual
counterexample at that integer n, rather than a restricted-family
upper approximation to the quantum maximum.

Such failure at n forces N_alpha>n for the full FINAL definition, regardless
of earlier isolated bulk equalities. The floor arithmetic gives the
claimed common N_alpha>=d_alpha*m^2-C_I*m. Infinite N satisfies it
automatically. Every order in I, including m-dependent choices and either
leading-sign tie, is accounted for. No uniform all-I upper theorem or
full optimizer classification was smuggled into this lower-barrier step.

## L1: closed final-onset sublevels and actual integer attainment

For each fixed m,n the original APPT feasible set is nonempty and compact,
as an arbitrary intersection of the closed global-unitary PPT conditions
inside the finite-dimensional compact density set. At any positive order
interval, spectral power sums and their order derivatives extend jointly
continuously to zero eigenvalues: x^alpha*log(x)->0 uniformly when alpha
stays above a positive lower bound. The log power sum stays nonsingular
on normalized density matrices. Its integral difference quotient at one
proves joint entropy continuity through alpha=1, even for singular states.
Maximum over this FIXED compact feasible set therefore makes E_alpha
continuous. The finite integer-rank maximum G_alpha is continuous too.
Neither maximum needs a differentiable optimizing branch.

The identity between {N_alpha<=N} and the intersection of the equality
sets E_alpha(m,n)=G_alpha(m,mn) for ALL integer n>=N is exact in both
directions, including N_alpha=+infinity. Each equality set is closed;
so is their infinite intersection. A finite prefix of dimensions would
not prove this statement, and is not what the manuscript uses.

The candidate alpha_0+u_c/m is inside I eventually and has finite FINAL
onset by K3. Hence the set of finite integer values of N taken on I is
nonempty and has a least integer, attained by the definition of that
value set. The minimizing set is exactly its closed sublevel. Allowing
other orders to have infinite onset is harmless. This proves the stated
finiteness, actual attainment, nonemptiness and closedness without
minimizing a surrogate continuous crossing function.

## L2: EVERY minimizer and EVERY fixed additive near-minimizer

J's derivative signs are strict and continuous on each relevant fixed
compact one-sided interval. Their positive minimum magnitudes yield
d_alpha-d_0>=c_I*|alpha-alpha_0| after integration. This is a common
linear leading barrier, not merely a unique limiting minimum.

For an arbitrary order with N_alpha<=M_I+B, L0 and the finite candidate's
upper bound first imply |alpha-alpha_0|<=U_(I,B)/m. This first localization
is essential: K cannot simply be applied to the entire compact I. Once
u=m*(alpha-alpha_0) is uniformly bounded, the new K3 theorem DOES supply
the common O(1) expansion of the true integer FINAL onset for every such
order. Alpha is held fixed while n ranges over its future tail, exactly
as the definition requires.

The two affine lines V(u) have opposite strictly signed slopes, and meet
at u_c with value a_c. For u on either side the corresponding line gives
the exact linear loss with slope sigma_+ or -sigma_-. Thus (12) holds
globally. The candidate upper bound and this loss imply
|u-u_c|<=C_(I,B)/m; dividing by m yields the full O(m^-2) order
localization. The same uniform expansion at an attained minimizer gives
both sides of M_I=d_0*m^2+a_c*m+O(1). Every order in the minimizing or
fixed-additive-gap set was arbitrary, so the conclusions are not merely
subsequence existence statements or calculations on a chosen branch.
Integer ties and potentially many finite minimizing orders are retained.
No sign for u_c, exact finite minimizing set, or uniqueness is assumed.

## Actual independent controls and their provenance

The author's initial run 20261015T075841.189768Z and revised run
20261015T080542.309850Z are author executions. Their code/result records
were read; I did NOT execute that script or relabel those results as
independent evidence. Source versions and the disclosed reviewer algebra
contribution are retained in the history.

I wrote independent_checks.py in this directory, using the regular-kernel
expressions to stress the NEW compact/alpha=1 gates. Its actual run
`runs/20261015T081127.835786Z/RESULT.json` is PASS and binds the revised
source plus the credited mathematical copies. No unexpected independent
control execution failed in this L review. The run includes:

- Five exact symbolic regular-kernel/normalization identities.
- Eighteen actual integer-dimension lower-witness cases, with physical
  adjacent ranks, beating even continuous bulk; orders include one and
  one plus/minus 1e-100 as well as separated points from 0.12 through 8.
- Eighteen joint-singularity identity checks down to contrast 1e-40.
  The old raw quotient is compared at extra working precision away from
  exact alpha=1; at one the separate exact von Neumann formulas are used.
- Three singular-density joint entropy-continuity checks and exact
  logical counterchecks to false uniqueness after integer rounding and
  replacing an infinite final tail by finitely many tested dimensions.

The rank-deficient density and logical toy examples are not claimed to
be APPT states. The lower witnesses are physical boundary-family states
by the credited all-unitary feasibility proof. These finite computations
do not certify a cutoff over the entire compact I, optimize the full
quantum feasible set, or calculate the true global M_I numerically.
The mathematical proof supplies those full L0-L2 quantifiers. Decimal
constants in the run are illustrations, not exact definitions or rigorous
interval certificates. Older I/J/K control/audit histories are unchanged.

## Scope and literal conclusion

The theorem minimizes the TRUE integer FINAL N over ANY preassigned fixed
compact positive interval containing alpha_0 in its interior. It covers
every minimizer and every order within each fixed additive B, including
orders selected differently at every m. It does not minimize over the
whole positive axis, permit growing intervals or orders tending to zero/
infinity, prove uniform all-order exact optimizers, give effective cutoffs,
an exact finite M_I/minimizing set, a unique minimizing order, ASEP, a new
formal theorem or a new major-conjecture solution.

Only this independent review directory was written by the reviewer. The
literal mathematical PASS binds the revised hashes above. Future changes
need a further read; final status-only edits and new public README/index
claims need a separate exact-difference binding. This report certifies no
unknown future mathematical extension or exhaustive literature priority.
