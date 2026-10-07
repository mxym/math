# Dependency map and reading order

All repository inputs below are frozen at c897a556e12e460380c7cf521e88f84286994915. DEPENDENCIES.json supplies exact public URLs, SHA-256 hashes, canonical Git blob identities and local copies. Historical inputs are preserved verbatim, including their own stated review limits.

## 1. Standalone method characterization

**Inputs:** a finite nonnegative probability-density representative r on all of R^d, d >= 1; its global zero extension if originally supported; 1 < s < infinity; sigma = r^(1/s). No positivity, smoothness, connectedness, log-concavity or source second moment is needed here.

**Construction:** for each coordinate j and h > 0, define the two positive density-ratio losses on {r > 0}, set both losses to zero on {r = 0}, and form W = 6|d_plus - d_minus| + 2d_plus. This is the exact minimum-density weight in 001 v5 Lemma 3.1.

**Proof chain:** elementary divided-power inequalities -> quantitative comparison with full root translations -> coordinatewise weak compactness and distributional identification -> global W^(1,s) membership. The reverse direction uses Sobolev translation estimates. Strong difference quotients, the zero-level-set derivative property and bounded divided-power multipliers -> the exact rooted-Ls limit with coefficients 6s for positive root derivative and 8s for negative root derivative. Every coordinate can choose its own finite-liminf sequence.

Theorem 1.2 and its proof in synthesis.tex are complete for this chain. audit/CORE_PROOF_REVIEW.md expands representative invariance, all zero-set and subsequence details, the fixed-limit dominated-convergence step, the truncated chain rule, and endpoint examples. Standard analytic inputs are Holder, Minkowski, Ls reflexivity for 1 < s < infinity, translation continuity, mollification/ACL and the Lipschitz Sobolev chain rule.

**Boundary:** global zero extension retains support jumps. At s = 1, the interval indicator has overlap mean 14h but a singular derivative, so the equivalence with W1,1 fails. The strong L1 formula holds under a separately imposed W1,1 assumption. No s = infinity claim is made. In the transport parameterization, 2 < q < infinity and s = q/(q-2); neither q endpoint is obtained by substitution.

**Attribution:** 001 v5 Theorem 6.1 and 008 Lemma 2.1/Theorem 1.2 already supply the sufficient root direction. The converse, finite-liminf characterization and rooted-Ls limit are additions relative to those repository statements, with no literature-priority claim. 001 v5 Proposition 5.1 already supplies the density-level L1 formula for the broader W1,1 class. Corollary 1.4 recovers it only on the root-Sobolev subclass.

## 2. Conditional transport envelope

001 v5 Lemma 3.1 -> convex-gradient interpolation with coefficient 12d/h^2 and weight 6A + 2B. Its functions are proper convex, finite rho-almost everywhere, have L2 gradients and a difference in L2 up to a constant. Their effective domains may require +infinity extensions.

Elementary layer-cake rearrangement -> pair the source profile F_h = max_j W_(j,h) with the actual target energy profiles. Atoms are permitted; independence is not assumed. F_h <= 8 makes all pairings finite for P2 targets.

**Separate input (P):** the fixed absolutely continuous source is in P2 and its centered Brenier potentials satisfy the all-P2 potential estimate with constant A_rho. This is not a consequence of the root theorem. Applying (P), followed by an infimum over h, gives Theorem 2.2. This rearrangement envelope is a derived consequence, not new sharpness or a converse.

001 v3 Theorem 1.1 supplies A_rho = sqrt(2/kappa) for its full-dimensional strongly log-concave sources. Theorem 1.4 supplies A_rho = (1 + sqrt(162))R for a full-dimensional log-concave density supported on a compact convex body K contained in B_R, R > 0. Centered potentials are L2 and finite convex on int K; proper convex extensions provide the interpolation domain convention. The inherited finite-cell/all-P2 foundation is an explicit input, not independently reproved by this audit.

## 3. Existing recoveries and lower constructions

- 001 v5 Proposition 4.1 gives the weight-mean coefficient 7; its BV tail bound has target-tail coefficient 8. The finite-q BV exponent is (q-2)/(3q-2).
- 007 Theorem 1.1 retains a distinct common-good-interval/coarea proof with the better target-tail coefficient 4. Its smooth steep-layer finite-q construction has a vanishing endpoint ratio. Its superquadratic product-source estimates and separate sharpness construction remain separate inputs.
- 008 Lemma 4.1 gives the boundary root-translation regimes below, at and above b = s-1; Theorems 1.1-1.2 use separately constructed globally convex potentials with exact mass matching. The critical lower construction has growing atom count and supports an all-small-distance envelope.
- The critical slowly-varying supplement, Theorem 1/Corollary 3/Remark 4, uses f(x) = c x^(s-1)L(x) exp(-x^2/2) for 0 < x < a with 008's transverse factors, then a strongly convex quadratic-tail extension. Its positive C2 L obeys the two log-derivative limits. H(h) = 1 + integral_h^a L(x)/x dx gives an implicit inverse; replacing it by w^(2/3) is not generally justified.
- 001 v5's stretched-exponential lower comparison has a vanishing endpoint ratio; its logarithmic-second-moment comparison has a positive ratio along a sequence. The hard-boundary stretched-exponential supplement gives positive matching endpoint ratios for its displayed sources. These are distinct quantifiers.
- The source boundary threshold b = s-1, Gaussian target-logarithm threshold beta = 1/2 and universal finite-Fisher sufficient threshold q = 4 concern different hypotheses. None is a complete classification of stable sources. One-dimensional transport from atomless sources is isometric; the lower obstructions require d >= 2.

For exact theorem numbers, constants, source locations and scope limits, read audit/IMPORT_REVIEW.md. Historical lower constructions and the all-P2 foundation are linked and copied, not represented as freshly certified proofs.
