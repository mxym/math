# Independent mathematical review of synthesis B

7 October 2026

## Verdict

**PASS for the internal mathematics of the stated synthesis, subject to its exact hypotheses and explicitly imported results.** The new overlap/root equivalence and rooted strong first-order limit need no mathematical correction. The rearrangement envelope follows from the imported minimum-density interpolation lemma. The recovery exponents and constants checked against the pinned sources agree.

The accompanying corrected synthesis applies all 11 exposition and review-status edits recorded in [CORRECTION_RECORD.md](CORRECTION_RECORD.md). Section 1 and all 10 theorem, lemma, corollary and proof environments are unchanged. The independent audit supports their mathematical validity under the stated hypotheses; it does not constitute human peer review, formal verification, or a publication, authorship or licensing certification.

This is an independent model-based audit. No external professional mathematician or human peer reviewer participated. The proof reconstruction is reviewable in the accompanying audit. This is not Lean or other proof-assistant verification and does not establish literature novelty or priority. It proves no general transport-necessity theorem.

## The exact theorem that passed

Let 1<s<infinity and let r be a finite measurable nonnegative probability density on all of R^d. Supported densities are extended by zero globally. Set sigma=r^(1/s). Define d_plus and d_minus by the positive density-ratio losses in the synthesis where r>0, and set both to zero where r=0. Let W=6|d_plus-d_minus|+2d_plus for h>0 in each coordinate.

Then sigma belongs to global W^(1,s) if and only if every directional overlap norm ||W||Ls(r dx) is O(h). A finite liminf of the norm divided by h, for each coordinate separately, already suffices. No common sequence across the coordinates is required.

With b_j=partial_j sigma, the exact strong limit in Ls(dx) is

sigma W_(j,h)/h -> s[6|b_j|+2(-b_j)_+].

The associated norm limit and weighted Ls(r dx) version follow. The increasing-root side has coefficient 6s; the decreasing-root side has coefficient 8s. The limits are one-sided as h decreases to zero through positive values.

For finite target moment order 2<q<infinity, s=q/(q-2). Neither q=infinity/s=1 nor q=2/s=infinity is included. At s=1 a unit-interval indicator gives ||W||L1=14h while its derivative has boundary atoms; the overlap criterion therefore does not imply W1,1.

## Proof reconstructed independently

The complete reconstruction, including every zero-set and subsequence detail, is in [CORE_PROOF_REVIEW.md](CORE_PROOF_REVIEW.md). Its main steps are:

1. The scalar inequality 1-t <= 1-t^s <= s(1-t), for 0<=t<=1, sandwiches each rooted loss between a positive root increment and s times that increment. Splitting a full increment into its positive and negative parts, then translating the upward part, retains support-boundary terms.
2. With B(h)=||sigma(.+h e_j)-sigma||Ls and Xi the larger loss norm, the exact valid comparisons are 2 Xi <= ||W||Ls(r dx) <= 14 Xi, B(h) <= 2^(1/s-1)||W||Ls(r dx), and ||W||Ls(r dx) <= 14s B(h). The proof is valid for every h>0, including zero-density gaps.
3. A bounded subsequence of directional root difference quotients has a weak Ls limit because 1<s<infinity. Testing against a compactly supported smooth function identifies this limit as the distributional derivative. Repeating coordinatewise proves global Sobolev membership.
4. Sobolev translation estimates give the converse and strong convergence of both oriented difference quotients. The derivative vanishes on the zero set: there the forward negative and backward positive quotient parts vanish identically, and their strong limits force both signs of the derivative to vanish.
5. The divided-power multiplier c_s(t)=(1-t^s)/(1-t) lies between 1 and s and tends to s at t=1. Along a subsequence of any sequence of h, translations converge almost everywhere. Multiplying a strongly convergent quotient by this bounded multiplier is justified by splitting the error against the fixed limit, then dominated convergence. This yields a subsequence limit for every sequence and hence the full strong limit. No unsupported pointwise-in-all-h convergence is assumed.
6. The Lipschitz map (a,b) -> 6|a-b|+2a gives the stated constant and sign. Truncated chain rules and Holder show r belongs to W1,1, so multiplying by sigma^(s-1) recovers the earlier density-level L1 formula on this subclass.

Section 2 was also checked: the rearrangement pairing is the Tonelli layer-cake inequality with intersection probability bounded by the minimum of the two marginal probabilities. It holds with atoms and without independence. F_h=max_j W_(j,h) is at most 8, so all target-energy pairings are finite for P2 targets. The coordinate energy sum is dominated by F_h times the full squared gradient. Applying the separate (P) bound and then infimizing in h yields precisely the displayed upper envelope. This is no converse or sharpness theorem.

## Imported hypotheses and attribution

[IMPORT_REVIEW.md](IMPORT_REVIEW.md) gives exact source links, theorem numbers, constants, line locations and the mathematical scope of the applied corrections.

- 001 v5 Lemma 3.1 supplies the arbitrary-density proper-convex interpolation inequality with coefficient 12d/h^2 and weight 6A+2B. Potentials are proper convex, may take +infinity outside their effective domains, are finite rho-almost everywhere, have L2 gradients, and their difference is L2 up to a constant.
- 001 v5 Proposition 4.1 supplies the sharp weight-mean coefficient 7. Its BV tail consequence uses coefficient 8 on the actual target energy tail. 007's separate common-good-interval/coarea proof has coefficient 4 and must not be discarded as duplicate proof text.
- 001 v5 Proposition 5.1 already gives the L1 limit for every global W1,1 density. The new rooted-Ls limit refines first-order information on a narrower subclass; its recovered L1 corollary is not new.
- 001 v5 Theorem 6.1 and 008's root criterion already give the sufficient direction. Only the converse/finite-liminf characterization and rooted strong limit are additions relative to the cited repository statements. No literature-priority conclusion follows.
- Transport applications retain source P2, target P2 (and finite q moments where used), proper convex representatives, L2 requirements and the independent all-P2 potential bound (P). 001 v3 supplies A=sqrt(2/kappa) for its full-dimensional strongly log-concave sources, and A=(1+sqrt(162))R for its compact full-dimensional log-concave sources. Density-root regularity alone proves none of (P).
- The critical source-boundary condition b=s-1, the Gaussian target-logarithm threshold beta=1/2, and the universal finite-Fisher q=4 threshold are distinct statements. The particular critical slowly-varying family's exact inverse cannot be replaced in general by w^(2/3).

The inherited all-P2 finite-cell foundation and every historical lower construction were not independently reproved in this audit. They are explicit frozen inputs, not hidden assumptions. This is a complete review of B's own proof and its claimed transfers, not a recertification of the entire 001/007/008 archive.

## Applied exposition and review-status corrections

The 11 applied edits are recorded individually in [CORRECTION_RECORD.md](CORRECTION_RECORD.md). Their mathematical content is:

1. The critical marginal is explicit: f(x)=c x^(s-1)L(x)exp(-x^2/2) for 0<x<a, with the same transverse g factors, followed by its strongly-convex quadratic-tail extension.
2. The compact-source class is a full-dimensional log-concave density supported on a compact convex body K contained in B_R, R>0. Potentials are finite on int K and use proper convex extensions.
3. The proof-input list includes 001 v5 Proposition 5.1/Theorem 6.1, 008 Lemma 4.1, and the critical supplement's Theorem 1, Corollary 3 and Remark 4.
4. Endpoint attribution is separated: 007's finite-q endpoint ratio vanishes; 001 v5's stretched-exponential endpoint ratio also vanishes; its logarithmic-second-moment lower comparison has a positive ratio along a sequence. These differ from 008's two-sided all-small-distance envelope.
5. Review status reports the completed independent model audit and explicitly retains the no-human-peer-review, no-formal-verification and no-novelty-certification boundaries. The proof-PDF label no longer asserts an earlier page count.

The original audit also offered optional explanations of the zero-set multiplier, the s=1 endpoint and the repeated (P) signpost. Those explanations are retained in the accompanying reviews; they are not additional changes to the unchanged Section 1 or its theorem/proof environments. The old PDF-build checks below concern the pre-correction version and do not certify any newly rebuilt PDF.

## Reproducible checks and limitations

- The completed audit verified all 57 source inputs against their declared Git blob and SHA-256 at c897a556e12e460380c7cf521e88f84286994915. Those inputs were also unchanged at the comparison commit 769b82dc432869476f5666d824f93de0f11482e9. These are historical source-pin checks, not assertions about later repository state.
- A no-shell-escape rebuild of the pre-correction TeX agreed with the audited PDF in extracted text and rendered page pixels at 1,350-pixel resolution; every audited page was visually inspected. This historical rendering check is distinct from verification of the corrected release PDF.
- Existing exact checks replayed: 007 interpolation has 6,000 inequalities plus 15 ramps and six exponent cases; 007 steep-source checks have 220 parameter cases and 936 coupling identities; 008 has 1,920 root inequalities, 960 signed-square identities, 320 interpolation inequalities and six exact mass-matched multiscale constructions.
- New independent checks have 1,920 rational zero-extended profile cases, 25 numerical strong-limit cases on asymmetric compact tents, and 12 boundary/endpoint controls. The numerical tests use two Gauss-Legendre resolutions on a boundary-refined mesh; they are diagnostics, not certified integration or proofs. Normal and optimized Python runs both pass.

Finite tests do not prove the Sobolev theorem, an infinite source construction, or an all-small-distance statement. The analytic reconstruction, not these checks, supports the theorem verdict. The audit does not certify publication readiness.
