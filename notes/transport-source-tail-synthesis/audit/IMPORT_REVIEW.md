# Independent import and coverage review of B

Date: 2026-10-07. Review type: independent model-based audit of source imports, hypothesis transfer, statement scope, numbering and attribution. This is not external human peer review, Lean or other proof-assistant verification, a complete revalidation of the historical potential theorem, or a novelty/priority certification.

## Result

**No material mismatch was found in the imported constants, stated theorem numbers, or mathematical direction of the principal source results.** B correctly keeps the potential estimate (P) separate from density regularity, retains global zero extension, distinguishes the stronger 007 tail coefficient from the 001 minimum-weight coefficient, and does not turn a characterization of its interpolation method into necessity for transport stability.

The synthesis is a conditional mathematical synthesis at the stated pinned snapshot. The accompanying corrected version applies all 11 recorded exposition and status edits, including the source descriptions and terminal reference list described in §7 below. Section 1 and all 10 theorem, lemma, corollary and proof environments remain unchanged.

## 1. Exact evidence and scope

Reviewed material:

- The pre-correction synthesis TeX, especially lines 26–145, 149–205 and 209–269.
- The accompanying mathematical review.
- The dependency manifest containing 57 source inputs.

All line references to B in this review refer to that audited pre-correction TeX. Line references to historical sources refer to their pinned versions. The exposition edits can shift line numbers in the corrected synthesis.

Primary material was read from Git objects at base `c897a556e12e460380c7cf521e88f84286994915`. Every examined `.tex` and `.md` source matched its SHA-256 in the dependency manifest. The historical sources were unchanged.

The 001v3 manuscript at first-public commit `5c6c088aa5abf1c1a4bdca6a8ce5beaa27faaef3` is byte-identical to the manuscript at the base (Git diff is empty). The principal mathematical source files examined here also have no changes between the base and comparison commit `769b82dc432869476f5666d824f93de0f11482e9`. These checks support the particular references below, not a global claim that the repository is unchanged.

This audit reconstructed the local imported inequalities and checked the source statements and relevant proof mechanisms. It did not independently redo all finite-cell approximation/cancellation arguments underlying 001v3 or every historical lower construction. No local-source reading is treated as an exhaustive literature search.

## 2. 001v5: exact weight, means, limits and the prior sufficient direction

Primary source: [001v5 manuscript](https://github.com/mxym/math/blob/c897a556e12e460380c7cf521e88f84286994915/preprints/001-strongly-log-concave-brenier/v5/manuscript.tex).

### Lemma 3.1, `lem:minimum`, lines 174–243

The source assumes:

- A finite nonnegative representative of any Lebesgue probability density on all of R^d.
- Proper convex functions taking values in (−∞,+∞], finite ρ-almost everywhere.
- Both gradients in L²(ρ), and u−v−a in L²(ρ) for some constant a.
- No lower-semicontinuity requirement for these convex functions.

The exact weight is W=6A+2B with
A=|m(x−he_j)−m(x)|/r(x), B=1−m(x)/r(x), m=min(r(x),r(x+he_j)); both quotient-defined weights are set to zero at r=0. The conclusion has coefficient **12d/h²**, coordinate energy |∂_j u|²+|∂_j v|², and **0≤W≤8**, for every h>0.

B lines 37–40 and 149–159 reproduce this correctly. Algebraically, m(x)=r(x)(1−d_+) and m(x−he_j)=r(x)(1−d_−) on r>0, so A=|d_+−d_−| and B=d_+. The zero convention agrees as well.

The source proof controls both finite-difference endpoints by m≤r and m(x−h)≤r; it never assumes translated L²(ρ) integrability. Convexity along a segment remains valid even if the density vanishes between its endpoints. Proper convex domains have nonempty interior because they have positive Lebesgue measure, and their boundary is null. The signed-square estimate contributes 6A after the three-term-square inequality; the remaining weight contributes 2B. These facts justify B's general-domain import without silently restricting to globally finite potentials or connected density support.

Infimizing in a gives B's centered δ: on a probability space the minimizing constant is the mean once u−v is square-integrable up to a constant.

### Proposition 4.1, `prop:mean`, lines 259–284

Exact assertion: λ_j(h)=∫W_j,h dρ≤7ω_j(h), where ω_j(h)=||r(·+he_j)−r||₁. If the directional distributional derivative is a finite measure, ω_j(h)≤h TV_j(r). Boundary jumps of the zero extension count.

The constant **7** is universal and sharp. Its proof uses ∫(r−m)=ω/2 and ||m(·−h)−m||₁≤ω. Thus 6ω+2(ω/2)=7ω. For the unit-interval indicator and 0<h<1/2, λ=14h and TV=2, so equality holds.

B lines 236–244 correctly get ∫F_h≤Σ_j λ_j≤7Sh, S=Σ_j TV_j(r), and then the good-region term 14ShL². No unweighted interior derivative has replaced the distributional BV quantity.

### Proposition 4.2, `prop:bv-tail`, lines 286–325

Exact general/BV bounds:

D²≤12dδ²/h²+2L²Σ_j λ_j(h)+8τ(L),
D²≤12dδ²/h²+14ShL²+8τ(L).

The tails are radial squared-gradient tails. Their coefficient 8 has **no extra dimension factor**. B lines 232–244 derive the same bound, initially using ∫F_h≤Σ_jλ_j. Its finite-moment exponent (q−2)/(3q−2) agrees with the source. The profile-max route can change an admissible dimension-dependent constant without creating a new transport exponent or sharpness result.

### Proposition 5.1, `prop:weight-limit`, lines 381–421

For **every** probability density r in global W¹,¹(R^d), the source proves
rW_j,h/h → 6|∂_j r|+2(−∂_j r)_+ strongly in L¹(dx).
It additionally proves absolute continuity of the limiting measure with respect to ρ, λ_j(h)/h→7||∂_j r||₁, and ||W_j,h||_p=o(h^(1/p)) for every p>1.

B's corollary lines 136–145 has exactly the same L¹ limit on the root-Sobolev subclass. The prose and review correctly avoid claiming that the new rooted-L^s assertion contains all of Proposition 5.1. For example, a marginal behaving as x^b at zero with 0<b≤s−1 can be W¹,¹ while its zero-extended 1/s root is not W¹,s. Multiplication by σ^(s−1) and Hölder recovers the old L¹ formula only where the stronger root assumption holds.

### Theorem 6.1, `thm:fisher`, lines 494–554

The old theorem assumes p=q/(q−2)>1 and r^(1/p) in **global** W¹,p, including zero extension. It proves a sufficient convex-gradient one-third interpolation estimate and a transport estimate **only with (P)** and the imported convex-domain hypotheses. With J_p=Σ_j p||∂_j r^(1/p)||_p, its displayed interpolation constant is
sqrt(3)·2^(−1/3)·(12d)^(1/6)·(14J_p)^(1/3).
The transport constant replaces 14J_p by 14J_p A_ρ.

The proof already contains ||d_j,t||_p≤|t|p||∂_jσ||_p and ||W_j,h||_p≤14h p||∂_jσ||_p. It does **not** state the converse characterization or the strong rooted-L^p first-order limit proposed in B. B and its review correctly count the old sufficient direction only once with 008.

## 3. 001v3: (P), constants and the proper-domain bridge

Primary source: [001v3 manuscript](https://github.com/mxym/math/blob/c897a556e12e460380c7cf521e88f84286994915/preprints/001-strongly-log-concave-brenier/v3/manuscript.tex).

### Theorem 1.1, `thm:strong`, lines 76–91

The exact source is a full-dimensional probability
r=Z^(−1) exp(−κ|x|²/2−W), κ>0,
with W proper, lower-semicontinuous and convex. It includes nonsmooth W and hard convex boundaries. For every target in P₂ it supplies a finite convex representative on D=int(supp ρ), in L²(ρ), unique up to a constant, and its unique centered representative. The squared estimate is 2/κ times W₂²; hence **A_ρ=sqrt(2/κ)**. The representative has a proper lower-semicontinuous convex extension to R^d, possibly +∞ outside D.

### Theorem 1.4, `thm:compact`, lines 127–148

The exact source is a full-dimensional log-concave probability density supported on a compact convex body K⊂B_R, R>0. It supplies centered potentials in L²(ρ), finite and convex on int K, for **all P₂ targets**, with **A_ρ=(1+sqrt(162))R**. No positive lower density bound or boundary regularity is imposed. Extension outside the source interior may take +∞.

B lines 185–205 and the review retain the correct constants and all-P₂ quantifier. The corrected synthesis and its review explicitly state the full-dimensional compact-convex K hypothesis and the proper-convex extension convention given above.

For the synthesis's transport applications, the following remain necessary and are explicitly present in B:

1. The source is absolutely continuous and belongs to P₂.
2. Each target belongs to P₂, and to P_q where q-moment conclusions are used.
3. The convex representatives meet the proper-domain, finite-a.e. and L² difference assumptions of Lemma 3.1.
4. Gradient L² integrability follows from the target pushforward and P₂; it is not a bounded-gradient claim.
5. Centering and (P) are a separate verified input, not a consequence of BV, W¹,¹, smoothness, full support, or the root condition alone.

The standalone root theorem has none of these transport hypotheses and correctly needs no source second moment. B's profile pairing is finite because F_h≤8 and targets have finite second moments, including atomic targets. No independence or realizability of rearrangement extremizers is imported.

## 4. 007: coefficient 4 and source variations

Primary sources: [007v1](https://github.com/mxym/math/blob/c897a556e12e460380c7cf521e88f84286994915/preprints/007-tail-brenier-stability/v1/main.tex), [007v2 combined manuscript](https://github.com/mxym/math/blob/c897a556e12e460380c7cf521e88f84286994915/preprints/007-tail-brenier-stability/v2/main.tex), and [007v2 extension](https://github.com/mxym/math/blob/c897a556e12e460380c7cf521e88f84286994915/preprints/007-tail-brenier-stability/v2/extension.tex).

- Theorem **1.1** in both versions is the tail-sensitive interpolation theorem. In v2 it is at main.tex lines 52–123 (v1 lines 51–122).
- Its domain is an open convex D, density zero off D with finite integrated coordinate-slice variation, u,v finite convex on D, L² gradients, and L² difference. The variation normalization is V(r)=½Σ_j TV_j(r), including boundary jumps.
- Its exact bound is D²≤12dδ²/h²+28V(r)L²h+**4**τ(L). Thus S=2V(r), and its good-region coefficient is the same **14S**, while its tail coefficient is strictly better than 8.
- The improvement comes from the common-good interval where both one-dimensional derivatives have magnitude ≤L, then the pointwise bound by four times the actual large-derivative squared tails. Coarea counts the original density-level interval once. This does not follow merely by replacing the maximum weight 8 by 4 in 001's proof.
- Theorem **3.1** applies the tail result under (P); Corollary **3.2** supplies the strong and compact source classes; Corollary **4.1** gives stretched-exponential upper tails. Their transport overlap with 001v3 is not a new result to recount.
- The v2-only **Proposition 5.1** is the full raw-translation-ratio sufficient condition, with coefficient 8 in its h·ratio term. This is a different “8” from the BV tail remainder and should not be conflated with it.
- **Corollary 5.2** treats specified superquadratic confinement with quantitative growth assumptions. **Corollary 5.3** treats every fixed product source exp(−κ_j x_j²/2−λ_j|x_j|^(m_j)), κ_j,λ_j>0 and m_j>2; its one-third power is sharp for each such source when d≥2 using three atoms in B₁. The per-source qualification in B is correct.
- **Theorem 6.1** constructs one fixed C∞ positive full-support 1-strongly log-concave source with the general finite-q optimal power, and the q=2 obstruction. It does not assert a positive matching finite-q endpoint constant or an all-small-distance two-sided envelope.

B's finite-q endpoint-ratio statement for 007 is also supported by the displayed formulas, although not separately named as a theorem there. In extension.tex lines 228–231, with θ=1/2−1/q and a_q=θ/(1+θ), D_n∼sqrt(d₀)m_n^θ, w_n∼k a_n m_n^θ, and m_n/a_n∼Z₁^(−1)e^(−B_n)→0. Thus D_n/w_n^(a_q) is a positive constant times (m_n/a_n)^(a_q)(1+o(1)), tending to zero. This is a derived observation from the source, not a new endpoint sharpness claim.

The stronger stretched-exponential logarithmic obstruction belongs to **001v5 Theorem 12.1**, not the original 007v2 Theorem 6.1. B's “What remains separate” paragraph should continue to be read with this distinction; no claim that 007 already proved that stronger obstruction is warranted.

## 5. 008 and the critical supplement

Primary sources: [008v1](https://github.com/mxym/math/blob/c897a556e12e460380c7cf521e88f84286994915/preprints/008-density-overlap-phase/v1/main.tex) and [critical slowly-varying supplement](https://github.com/mxym/math/blob/c897a556e12e460380c7cf521e88f84286994915/notes/critical-boundary-slow-variation/manuscript.tex).

Exact numbering in 008:

- **Theorem 1.1**, lines 51–66: the complete two-sided all-small-distance modulus for the explicit product source.
- **Theorem 1.2**, lines 68–86: root/Fisher sufficient transport criterion under (P), plus the source-class optimality of the fourth-moment Fisher threshold.
- **Lemma 2.1**, lines 106–122: Xi≤sB and the root-Sobolev sufficient bound.
- **Theorem 2.2**, lines 124–169: overlap interpolation with coefficient 14.
- **Corollary 2.3**, lines 171–191: conditional transport modulus.
- **Lemma 4.1**, lines 228–249: the three boundary root-translation regimes used directly in B.

The source is specifically f_b(x)=c_b x^b e^(−x²/2)1_(x>0), multiplied by transverse g(z)=c_g exp(−1/(1−z²))1_(|z|<1). It is not an arbitrary density with a boundary vanishing order. The zero extension is essential: b=0 has a trace jump, while the transverse roots have zero trace and lie in every finite-order W¹,s. For s=q/(q−2), the three bounds are exactly those in B:

- b<s−1: h^((b+1)/s).
- b=s−1: h(1+log(1/h))^(1/s).
- b>s−1: h.

The critical transport logarithm has power **1/(3s)**. B correctly distinguishes its root-based upper derivation from the separate globally convex, exactly mass-matched lower constructions. The critical lower example allows atom count to grow; a fixed-atom claim would be false to the stated scope. The whole phase diagram is for d≥2 and a fixed displayed source, not a general classification.

The supplement's **Theorem 1** assumes q>2, s=q/(q−2), b=s−1>0, d≥2, and a positive C² L near zero with x(log L)'→0 and x²(log L)''→0. Its first marginal is **f(x)=c x^(s−1)L(x)e^(−x²/2) for 0<x<a**, extended with a C², 1-strongly convex potential and quadratic tail; it has the same transverse g factors. Under these conditions:

H(h)=1+∫_h^a L(x) dx/x,
F(h)=h^(3/2)H(h)^(1/(2s)),
G(h)=h^(1/2)H(h)^(1/(2s)),
Ω(w)≍G(F^(−1)(w))=w^(1/3)H(F^(−1)(w))^(1/(3s)).

B's conditions, scale exponents, inverse caution and all-small-distance lower-bound description agree. The proof includes both finite and divergent limiting H; it assumes neither monotonicity of L nor divergence of H. The supplement's **Corollary 3** gives family-specific equivalence between a pure one-third estimate, integrability ∫_0^a L(x)dx/x<∞, and global root Sobolev regularity. This is genuine necessity within that specified family and does not give general source necessity.

The supplement's **Remark 4**, lines 262–277, supplies an explicit allowed L=exp((log(1/x))^α), 1/2<α<1, for which replacing H(F^(−1)(w)) by H(w^(2/3)) loses comparability. B correctly retains the implicit inverse.

## 6. Scope, duplicate counting and novelty caveats

The following distinctions in B are supported by the pinned sources:

- The bounded-overlap/root **sufficient** direction in 001v5 and 008 is one shared result. Only the converse and rooted-L^s first-order refinement are additions relative to the cited repository statements; the ordinary difference-quotient proof does not itself establish literature novelty.
- The profile envelope is a direct rearrangement/layer-cake consequence of Lemma 3.1. It gives an upper bound, not a sharp source/target classification, maximizing-gradient construction or converse.
- The old L¹ limit on all W¹,¹ densities is not supplanted by the narrower rooted-L^s statement.
- BV finite-moment and tail rates in 001/007, and the Gaussian rates carried from 001v4 into v5, are recoveries rather than independent new counts.
- The Gaussian logarithmic-target-moment threshold β=1/2 differs from the boundary-source threshold b=s−1. The Fisher q=4 threshold is a sufficient-condition threshold for a whole source class; individual better sources can work below four.
- The smooth-source optimal power with zero endpoint ratios differs from a two-sided all-small-distance envelope. The hard-boundary stretched-exponential supplement, **Theorem 1**, lines 68–91, really does have a positive matching endpoint ratio for the uniform cube and cube-truncated Gaussian.
- Dimension one is isometric for atomless sources, so the multidimensional sharpness obstructions cannot be claimed there.

B expressly disclaims novelty, priority, human peer review and formal verification, and says the full literature comparison is incomplete. Those disclaimers are accurate and should remain. This model import audit does not remove them.

## 7. Applied precision corrections and retained explanations

No correction to a principal imported constant or to the new theorem statement was required. The complete 11-operation exposition/status record is in [CORRECTION_RECORD.md](CORRECTION_RECORD.md). The mathematically substantive corrections are the following.

### Exact compact source and extension

The corrected compact-source sentence reads:

> For a full-dimensional log-concave probability density supported on a compact convex body $K\subset B_R$, $R>0$, its Theorem 1.4 instead supplies $A_\rho=(1+\sqrt{162})R$. Its centered potentials are in $L^2(\rho)$ and finite and convex on $\operatorname{int}K$; their proper convex extensions to $\R^d$ supply the domain convention of Lemma 3.1.

Neither arbitrary BV regularity nor the root condition implies (P). The accompanying review records the same source-domain hypotheses.

### Critical marginal and its extension

The corrected source description reads:

> For sufficiently small $a>0$, the first marginal is $f(x)=c x^{s-1}L(x)e^{-x^2/2}$ on $0<x<a$, with the same transverse factors $g$ as above. It is extended with a $C^2$, $1$-strongly convex potential and quadratic tail.

The conditions $x\ell'(x)\to0$ and $x^2\ell''(x)\to0$, where $\ell=\log L$, remain in force. This states the defining relationship between L and the source density without weakening the derivative conditions.

### Exact proof inputs

The corrected terminal list includes:

> 001 v5, Lemma 3.1, Propositions 4.1–4.2 and 5.1, and Theorem 6.1; its root sufficient condition overlaps 008 and is counted once.

> 008 v1, Lemmas 2.1 and 4.1, Theorem 2.2, Corollary 2.3 and Theorems 1.1–1.2; its later critical slowly-varying supplement, Theorem 1, Corollary 3 and Remark 4, supplies the implicit modulus, the criterion within that family, and the inverse-substitution limitation.

### Distinct endpoint conclusions

The corrected endpoint paragraph reads:

> The fixed smooth steep-layer construction in 007 has the optimal finite-moment power and a vanishing endpoint ratio. The strengthened construction in 001 v5 also has a vanishing endpoint ratio for its stretched-exponential obstruction, while its logarithmic-second-moment lower comparison has a positive ratio along a sequence. These conclusions differ from 008's two-sided all-small-distance envelope.

Thus 001v5's positive logarithmic-second-moment sequence ratio is not grouped with its vanishing finite-q and stretched-exponential ratios.

### Transport-scope signpost

The original audit offered a repeated (P) signpost as an optional readability safeguard, rather than a missing mathematical premise or a required change. Throughout the transport recoveries, all hypotheses of the synthesis's envelope theorem remain in force, including the separate potential estimate (P). This explanation is retained here and is not counted as an additional applied manuscript correction.

## 8. Completed review status and limits

The proof and its imported statements have undergone an independent model-based audit. This does not constitute external human peer review, Lean or other proof-assistant verification, or a literature-novelty certification. No external human reviewer participated. No authorship, license, novelty, priority or journal-tier assertion is supplied by this audit.

Historical sources, the synthesis's Section 1, and all 10 theorem, lemma, corollary and proof environments are unchanged by the 11 exposition/status corrections. Those changes update source precision, attribution and review reporting; they do not strengthen the mathematical verdict or certify publication readiness.

The audit proves no general transport-necessity theorem. The overlap/root equivalence characterizes the stated density-overlap method under its exact hypotheses; the critical slowly-varying supplement provides necessity only within its specified family. The all-P₂ potential foundation and every historical lower construction were not independently reproved here. No source reading or model review is treated as an exhaustive literature search.
