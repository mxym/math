# Independent ordinary review: first bulk coexistence threshold

Decision: **PASS for the exact B1--B19 source and scope below.** This is an internal AI-agent full mathematical read, supported by a newly written independent program. It is not Lean verification, external human peer review, a priority certificate, or a new major-problem count. No mathematical correction was required in this new source and no finding remains unresolved.

## Inputs and actual read scope

The entire `PAPER.md` was read, including all threshold proofs, all asymptotic coefficients, the complete physical paragraph and exclusions. The unchanged mathematical SHA-256 is `3e1f67ee40b28af0b9de3a643488524fdb38f508d663f63e2ec82f7bc4322804` (11627 bytes). The literal reviewer copy is `PAPER_V1.md`; `snapshot/PAPER.md` is byte-identical. The complete new theorem map, research log, credited-input manifest, bounded primary-scope record, requirements, author checker and its sole recorded result were read as well. `INPUT.json` binds all 26 captured author files, including the executed author script and result.

The eleven credited inputs were compared with the reviewer's previously held, fully read L/V/S and T v2 sources or reports; `DEPENDENCY_BYTE_COMPARISON.json` records the actual matches. L is `49b33ee7edb2e326619a144f4343e78d896c47cfe4d9e524c16cd6790a0e001d`; V is `7b9846a394673aee0fe97a1f0b7b2c01a197ab6b3e9854fac7201e0eb562b269`; published S is `6ae480fc6d67c4b138e852c68529f81b9e39923828eb0c13d15cced5e439ab54`. The eight repository files are bound to immutable main `c4e0d9e713ba349d376469231789bb7b36915b7d`. The other three are T v2 PAPER `83c2240adfbca39009ff446504cc477f47684a0e5de1db52439862053bbcad79` and the reviewer's literal old reports `302bfa967e5e8871066700cbb799598a3486a8bfc7f923f9d239de4b9af5952d` / `5c9276d00f19e1c7fe3253a6ec840833625f95edc19a5a66b1e23d34bc184b21`.

This review reuses those earlier full reads after byte comparison and rechecks their specific scalar/physical hypotheses; it does not describe them as freshly repeated audits. Only T2's already reviewed all-c pole threshold is used from T, not the new c>=1 extension. The all-order value theorem was already completed in V and is explicitly credited. No author code was imported or executed by the reviewer.

## Mathematical assessment

**All positive c: a positive, attained, continuous lower threshold.** For every c>0, B(c,L,h)<=b(cL)<b(2c) at L<2, with P>0 there. Thus U=(b(2c)-B)/P is positive. At L=0 its value is the bare crossing b(2c)-1. As L approaches 2, the lower bound

    [b(2c)-b(cL)] exp[cG(L)] >= C(2-L) exp[C'/(2-L)]

diverges uniformly in h, locally uniformly in c>0. The constants follow from b'>0 on a positive compact interval and the exact G formula; they need not be uniform as c tends to zero. This gives attainment, strict positivity and local common compact sublevel sets, hence continuity of r_bulk(c). The identity F-b(2c)=P(r-U) proves the entire onset/tie statement: a unique bulk pair below the threshold, that pair plus *every* U minimizer at the threshold, and no width-2 maximizer above. Zero-width and multiple-width ties are retained for general c.

**Exact mixing elimination includes the clamp.** Multiplying the original quotient by exp[c(Lh+G)] gives exactly B4. Its second h derivative is exp(a+g(K)+kh)k^2>0. The unique unconstrained minimum is h_U=(log A(k)-g(K))/k, and A(k)<exp(k), g(K)>0 imply h_U<1. Thus only the lower clamp is needed. For h_U<=0 the actual value is exp(a)(b(K)-1), at least the zero-width competitor. The logarithmic expression B6 applies only when h_U>0. Direct substitution yields precisely exp(a)(g(K)-g(k))/q(k); the reciprocal q and the protection exponential are both essential. No formal negative mixing is treated as feasible.

**The small-c result is global before any local IFT.** The even analytic expansion g(k)=k^2/8-k^4/576+O(k^6) implies b'(k)>=k/8 on one sufficiently small nonnegative interval. Integrating gives B9 for every L and h. An interior trial at L=2-(8/3)c has U=O(c^3). Since P<=1, every global minimizer consequently satisfies 2-L<=C c. This first localization yields L>=1 eventually, k/(2c)->1, and a positive h_U tending uniformly to 1/2.

Writing t=(2-L)/c then gives the stronger lower bound

    U/c^3 >= (t/8) exp[2/(3t)]

for all these global minimizers. It diverges as t tends to zero, while the earlier estimate bounds t above. Every global minimizer is therefore in one fixed positive compact t interval. This step excludes moving and exponentially thin boundary layers; it is not inferred from local Taylor expansions or finite stationary computations.

On that common interval, B11 extends analytically through c=0. Indeed

    g(2c)-g(2c-c^2 t) = c^2 t integral_0^1 g'(2c-s c^2 t) ds

has an exact factor c^3 since g'(0)=0 and g is analytic. The other factors are analytic with q(0)=1. The limiting function psi(t)=(t/2)exp[8/(3t)] has a unique global minimum at 8/3 and positive curvature 3e/16 there. Uniform compact convergence forces all global minima into that neighborhood; analytic IFT then makes the stationary/minimizing branch unique for every sufficiently small c>0. Global localization is what upgrades local IFT to the claimed unique global branch. No explicit universal small-c cutoff is supplied or asserted.

**All B7 coefficients independently recomputed.** The expansion of Phi is

    exp[8/(3t)] [t/2 + c(-t^2/8-5t/6) + O(c^2)].

At t=8/3 the c coefficient is -28e/9 and its t derivative is -e/3. Dividing the negative mixed derivative by psi'' gives t'_B(0)=16/9. The mixing expansion is 1/2-c/6-(t/6)c^2+O(c^3). Hence

    t_B = 8/3 + (16/9)c + O(c^2),
    L_B = 2 - (8/3)c - (16/9)c^2 + O(c^3),
    h_B = 1/2 - c/6 - (4/9)c^2 + O(c^3),
    r_bulk = (4e/3)c^3 - (28e/9)c^4 + O(c^5).

These formulas and needed differentiated errors follow from the analytic branch. In particular, fixing h=1/2 or dropping 1/q changes the next coefficients. The cubic scale is strictly below the bare quadratic crossing for small c.

**Exactly two phases at onset, with a genuine derivative jump.** Since r_bulk<b(2c)-1 at small c, zero width is strictly suboptimal at this threshold. The unique U minimizer and the unique bulk pair are the entire scalar argmax. A convex hull of the two scalar pairs is not inserted. Strict h convexity and the positive optimized width curvature c Phi_tt give a positive-definite Hessian of U by its Schur complement. At coexistence, differentiation of the exact identity gives Hess F=-P Hess U. For each fixed small c the mixed point is nondegenerate; compact U sublevels put all nonbulk maxima near it when r decreases to r_bulk from above. IFT gives the claimed unique analytic maximizing branch immediately above the threshold.

The active slopes at coexistence are 0 and P_B>0. Thus the left and right derivatives of F_* are respectively 0 and P_B; for log F_* they are divided by b(2c). Using the rescaling gives c(L_B h_B+G(L_B))->1, so P_B and the limiting log derivative jump tend to exp(-1). This concerns r derivatives, not a claim that the full optimum is smooth across coexistence.

**The r interval conclusion is exact and does not settle c topology.** For an interior width, the identity

    b(2c)-1 = P U + (1-P) Q,  Q=(B-1)/(1-P)

shows U<bare if and only if Q>bare for the same competitor. Strict inequalities cannot come from width endpoints. Taking the attained minimum/maximum proves either equality of both thresholds with the bare crossing, or r_bulk<bare<r_crit. Combining the two exact optimum criteria makes the set where F_* exceeds both pure values exactly the one open interval (r_bulk,r_crit). This excludes separated intervals in r for each fixed c. It does not prove connectedness in c, a unique c boundary, or a complete intermediate-c phase diagram.

**Original matrices, all near-optimizers, and iterated limits.** The physical consequences retain actual complex PSD trace-one matrices, APPT after every global unitary. Fix one sufficiently small c>0 and take arbitrary integer sequences 2<=m<=n, m->infinity, real alpha>1, alpha/m->c and 3^alpha/(mn)->r_bulk(c). The full S equivalence retains distance to the full two-point scalar argmax AND the middle chord/spread loss J->0 AND the actual peak loss->0. This is a criterion for all actual near-optimizers, not merely for the exhibited rank family. S supplies physical integer-rank realization of both scalar pairs; alternating subsequences are allowed.

The two displayed empirical body laws are the possible 1-Wasserstein subsequential limits, as consequences of that full criterion. They are not offered as a replacement positive-r iff criterion. At the bulk phase the actual peak moment tends to zero. At the interior mixed phase it tends to r_bulk P_B>0 and S's interior peak formula gives

    m(3-D lambda_max) -> 3(L_B h_B+G(L_B)).

The width-2 bulk point is not fed into that interior formula. Only after the fixed-c physical limit does c->0 give c times the right side tending to 3, mixed peak moment asymptotic to (4/3)c^3, and both body laws tending to the symmetric +/-1 law. No uniform actual-spectrum theorem on simultaneous paths alpha/m->0 has been proved or silently inferred.

## Independent controls and author evidence

The reviewer wrote `independent_checks.py` without author imports and actually ran it once, in `runs/20261015T115337.425416Z`, status PASS. Runtime: Python 3.10.12, Sympy 1.9, Mpmath 1.2.1, 400 decimal digits. Script SHA-256: `c29ff5c07a14fc4fe435b28931367572b1ab2036c51df28a97a210bc6442b761`. Result SHA-256: `45d997fb2b7f4ce5bbfd43455dd0825b3de5f973da5aee09986a26a9a391b7f4`.

Its evidence comprises thirteen exact symbolic identities including every B7 coefficient; forty-two widths covering both constrained mixing branches and 210 direct comparisons; forty-two weighted-threshold identities; ninety-six global gap diagnostics; six small-c stationary diagnostics down to c=1e-20, including Hessian signs and slope; and three exactly integer-dimension/projection-rank, trace-normalized physical-family diagnostics at m=3000,9000,18000. The construction uses the credited actual Schmidt SOS sufficient theorem, not sampled-unitary tests. The trace, moment and peak-height computations retain floor/clipped integer rank and the exact normalization denominator. Finite family or findroot diagnostics do not prove global uniqueness or the all-matrix upper bound; the written proof and credited S supply those.

Eight deliberately false assertions actually raised AssertionError, with their witnesses and caught exception messages retained in the result: replacing the cubic threshold by the bare crossing; reversing the quartic sign; fixing h=1/2 too early; applying B6 to a clamped negative h_U; omitting 1/q; removing the protection exponential; merging the onset thresholds; and treating the width-2 peak factor as positive. There was no unexpected failure in this new reviewer execution. The exact executed script and complete result remain saved.

The author's checker and its sole run `20261015T113652.131637Z` were fully read but were not executed by this reviewer and are not called independent evidence. Its recorded PASS has ten symbolic checks, forty-nine fixed widths with five comparisons each, 160 gap diagnostics, four small-c branch diagnostics, six integer-family diagnostics and six false-variant regressions. These are author-run finite diagnostics. Their captured bytes, input hashes and runtime are retained without broadening the claim they support.

## Limits and disposition

The bounded primary scope reuses the already checked official abstract/version pages with their original checked date and explicit non-full-text limits. I did not perform a new full-text collision audit or establish priority. The historical pending author banner remains part of the exact frozen source; this report supplies the current mathematical disposition.

The PASS does not establish exact finite extrema, all-c threshold uniqueness, absence of c islands, a new all-order value theorem, complete all-order spectral rigidity, simultaneous c_m->0 physical uniformity, Lean coverage or any enlarged formal audit. No root/author source was modified, no repository operation or submission was performed, and no subagent was opened. Final corpus metadata, README/index binding, figures, transport and future evidence layout are outside this report.
