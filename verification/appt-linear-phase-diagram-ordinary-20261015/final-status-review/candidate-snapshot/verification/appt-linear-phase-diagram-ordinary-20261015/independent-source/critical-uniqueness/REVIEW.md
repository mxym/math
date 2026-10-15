# Independent ordinary review: unique last interior phase and local diagram

Decision: **PASS for the exact manuscript, exact interval engine and exact certificate identified below.** This is a complete internal AI-agent mathematical and code read with an actual private replay and independent auxiliary controls. It is not a new independent implementation of the author's interval engine, Lean verification, external human peer review or priority certification.

## Exact inputs and actual executions

The complete `CRITICAL_UNIQUENESS_CERTIFICATE.md` has SHA-256 `be76b90de9277fab91c1f676f8de7619c2d58a5b79cf65cf06839d7ce8e7637e`. The complete interval-engine source has SHA `78ab0341d6079ceedb7be01abc9eba8608d50df0ad2136fa53b554a547c6ce1c`; its exact certificate has SHA `f9dd26bc8b4769a22aac06d07ba76587da18ccbc0ec62292856fcf1ae7eee878`. The replayer source SHA is `a50e67cb61b643818d14957fa6e8b2d25a3ebca1d054f85d297bc78959fe8d35`. All were read, including every proof section, all arithmetic routines and the complete replay logic. Certificate data were independently parsed and structurally checked; every stored numerical bound was recomputed by the unmodified authored replayer.

The owner ZIP SHA is `f4cac6255270398fd2370db0a0ef117572f01ca251892081b83b8a69a0f8d14b`. It was copied, hash-checked and safely extracted to a new private snapshot before any execution. The replayer was invoked only in a further private scratch containing literal inputs. The certificate generator was never executed. Actual run `20261015T124716.398448Z` passed and retained the original certificate bytes and its started/completed UTC strings exactly. A new private replay-output timestamp is explicitly a reviewer execution record of author code, not a changed author certificate or a newly independent program.

The exact dependencies are the separately fully read LAST and NO_ISLANDS sources, plus the already reviewed c>=1 theorem and immutable credited L/S inputs. Their original complex-density domain and physical losses are unchanged. No author/root input or old published review directory was modified.

## Interval engine and full coverage assessment

**Integer arithmetic is outward.** Intervals use integer endpoints divided by S=2^160. Addition and negation are exact; multiplication takes all four endpoint products with floor/ceiling division. Inversion swaps the appropriate nonzero endpoints and rounds outwards, including negative intervals. Rational initialization, subtraction, repeated nonnegative integer powers and interval intersection preserve containment. Python arbitrary-precision integers avoid overflow. Every division or logarithm domain required in the certificate is checked. The source has no floating literal supplying a mathematical sign. Independent interval dependencies may make a bound wider, never narrower.

**The transcendental enclosures have valid uniform remainders.** For 0<=t<=2, the degree-96 exponential polynomial has positive remainder at most 9*2^97/97!. Its rounded recurrence bounds every term, and exp(2)<9 follows from the elementary exponential-series bound. The log reduction places its mantissa in[1,2] by integer shifts and outward rounding. The atanh expansion has z in[0,1/3], and its omitted tail is at most 9/[4(193)3^193]. The computed log2 interval is combined with an integer exponent using proper signed interval multiplication. Endpoint monotonicity extends point enclosures to input intervals. No library exp/log implementation is trusted for certificate signs.

The formulas for q,s,w,g,g' are enclosed using their proved monotonicities. The global 0<s'<=1/12 inequality follows from the fully convergent sinh-series coefficient proof in the manuscript. The safe enclosure [0,1/12] and g''=s'd+s^2q give a valid, possibly conservative, second-derivative bound. I independently differentiated W in k and x: both the g''/Delta and (g')^2/Delta^2 terms carry the negative signs stated. All a_k and a_kk constants agree.

**Analytic tails complete the continuum domain.** For every K in[519/1000,13/25], x<=1/10 is inadmissible by the certified monotone w/g constant. On x>=9/10, the exact inequalities yield W>27/(100delta)+log(delta)>=27/10-log10>1/5. They use the certified r_0 upper bound and g' lower bound, with K>1/2 and x>=.9. Thus these entire tails are excluded, not left to a mesh. The pure endpoints x=0,1 are treated separately.

**Every certificate leaf is an interval proof.** The replayer verifies rational endpoints, positive leaf length, exact adjacency, total lengths, and exact numerical-bound equality. There are precisely:

- 27 fixed-K upper-value leaves covering x in[.1,.9]; all have strictly positive W with lower bound exceeding 1/10000;
- 32 left and 13 right leaves covering the entire K band outside the core, excluding simultaneous W=W_x=0;
- one entire K-band/core-x box with v>0 and W_xx>1/10, together with strict opposite W_x signs on x=.5 and x=.55.

These are 73 leaves, including 45 full-K stationary-exclusion strips. The upper-value mean-value refinement uses a derivative enclosure over the whole x leaf, not a midpoint derivative. Its intersection with the direct enclosure remains rigorous. Different covers are not reused at an unjustified K value. The lower witness has v>0 and W<-1/5000 at exact rational K=519/1000,x=521/1000. This proves K_star above that endpoint. At the upper endpoint no interior tie is possible, and the last-boundary theorem excludes equality K_star=13/25. The certified result is strictly 519/2000<c_star<13/50; the more precise decimal found by an auxiliary root search is illustrative only.

## From the certificate to the full theorem

The no-islands theorem supplies one last parameter K_star. At its interior tie, constrained mixing is uniquely h=v/k and the optimized U gives W=W_x=0. The tails and forty-five outer strips force every tie into x in(.5,.55). Strict W_xx>1/10 throughout that box makes W_x strictly increasing for each fixed K, so at K_star at most one interior tie exists. LAST supplies one, hence uniqueness. W_K>0 follows from the separately reviewed analytic no-islands argument. The crossing curve consequently has second derivative -W_xx/W_K<0 at its unique global maximum.

Strict h convexity and (U_min)_xx=r_0 W_xx>0 give positive-definite Hess U by its Schur complement. At coexistence the exact product identity and vanishing gradient give Hess F=-P Hess U, negative definite. The linear L=2x change preserves definiteness. This is a global uniqueness conclusion for the last interior tie, not merely a chosen numerical root.

The analytic critical branch z(c,r) is then justified by IFT. The proof also excludes new global maxima arriving from scalar boundaries: the h-sensitive small-L estimate works uniformly for nearby positive r; near L=2 the linear bulk deficit dominates the exponential peak; the two h faces are strictly below the pole; the remaining compact set has a triple-point gap outside the one interior neighborhood. Thus the exact local representation V=max{b(2c),1+r,M(c,r)} is established, rather than just a stationary branch.

At the triple point M_r=p in(0,1). Therefore both coexistence equations have nonzero r derivatives and unique analytic zero curves. Along the pure crossing, the path using the U-minimizing h need not optimize F away from the triple point; the source correctly uses it only for the first derivative where the scalar gradient vanishes. This gives D'=-2p r_star W_K and the stated coefficients

    r_B-r_0 = 2 r_star W_K (c-c_star) + O((c-c_star)^2),
    r_P-r_0 = -2p r_star W_K/(1-p) (c-c_star) + O((c-c_star)^2).

Their difference has the positive closing coefficient 2r_star W_K/(1-p) on the mixed side c<c_star. The strict r monotonicity of the two gap functions gives the full nearby bulk/mixed/pole diagram and exact two-phase boundary ties. For c>c_star these analytic curves still exist as equations but are not global mixed boundaries; the manuscript explicitly keeps that distinction.

**Actual quantum consequences retain all S hypotheses.** For every fixed limiting pair in this neighborhood, the full scalar argmax, actual spread J and actual peak loss classify genuine complex-density APPT near-optimizers after every global unitary. All integer n>=m paths in the original fixed positive c window remain allowed. At the triple point exactly three distinct empirical body laws are possible and each is physically attained: atom gaps 0,2 and L_star in(1,1.1). Tied subsequences may alternate. This does not claim that convergence to the triple point from one side forces a phase selection without controlling the vanishing gap. No interior peak formula is extended to width 2 and no simultaneous c->0 physical theorem is added.

## Independent controls, actual failures and disposition limits

The separately written `independent_checks.py` imports no author module. Its actual run `20261015T125457.850334Z` PASS checks fourteen symbolic identities, complete exact rational partition/sign serialization, and finite calculus diagnostics with 650 digits. Its numerical triple point is only an illustration. Five actual expected AssertionErrors have witnesses for omitted admissibility, an unconditional elasticity bound, a reversed curvature bound, incorrect phi monotonicity and a reversed window-closing sign. These do not replace the written full-domain proof or interval arithmetic.

The reviewer also selected four private certificate corruptions and actually ran the unchanged authored replayer on each. Run `20261015T125541.063539Z` records four nonzero exits with retained AssertionError tracebacks: an upper-cover hole, a whole-K strip hole, a forged core bound, and a widened declared K domain. Every damaged input, exact executed script, stdout and stderr is retained. These are expected adversarial failures, not failures of the original theorem or an independent engine implementation. The original owner certificate/source bytes remain unchanged. There was no unexpected execution failure or mathematical correction in this scope.

The old bounded literature screens are retained with their actual abstract-only/read-date limitations. No new full-text or priority audit is claimed. This PASS covers the unique last mixed point and its complete local critical diagram. Global uniqueness of every mixed optimizer at arbitrary 0<c<c_star and r is a separate fourth manuscript, explicitly PENDING here. No old Lean scope, finite-dimensional exact optimization, publication event, future layout/transport or new major count is certified.
