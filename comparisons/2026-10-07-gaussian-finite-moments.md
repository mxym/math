# Gaussian finite-moment Brenier stability: focused literature comparison

7 October 2026. This note compares a full-support finite-moment stability theorem with directly inspected primary literature. It does not certify priority or independently certify the proof.

## Result under comparison

For the standard Gaussian source γ_d and any fixed finite q>2, the proposed estimate is

‖T_μ−T_ν‖L²(γ_d) ≤ C(d,q) M_q^(2/3) W₂(μ,ν)^(1/3),

where M_q=(∫|y|^q dμ)^(1/q)+(∫|y|^q dν)^(1/q). Targets may be unbounded, atomic, or singular. The same exponent holds for full-support densities proportional to exp(−V), with V κ-strongly convex and ∇V globally L-Lipschitz, with constants uniform for fixed d,κ,L,q. The sharpness statement concerns each fixed Gaussian in d≥2. The second-moment endpoint has no uniform modulus even on targets with second moment exactly one. In d=1 the map distance equals W₂.

The additional analytic input is a translation-ratio interpolation lemma. If p=q/(q−2) and

‖r(·±he_j)/r−1‖Lᵖ(ρ) ≤ C_j h,

then convex functions with L^q gradients satisfy a squared-gradient estimate consisting of an h^(−2)L²-potential term and an hL^q-gradient term. Optimization gives the one-third exponent when combined with the manuscript's radius-free all-P₂ potential estimate. Full support and translation control exclude hard-boundary conditioned Gaussians.

## Closest finite-moment predecessor

**Delalande–Mérigot (2023), Corollary 4.4.** For a compact convex source with density bounded positively below and above, target moments of order p≥4 and p>d give a W₁ map exponent p/(6p+16d). Remark 4.2 allows other moments, but retains an independent Hölder assumption on the potentials; it does not give the Gaussian theorem for every q>2. Their Proposition 4.1 already provides the one-third potential-to-gradient interpolation exponent for bounded-gradient convex functions on compact domains, with boundary measure in the constant. The present argument replaces that compact-domain/bounded-gradient input with full-support translation ratios and finite-q gradients. Neither result's source class contains the other's. [Primary text, §§4–5](https://arxiv.org/html/2103.05934v2#S4).

**Letrouit–Mérigot, version 3, Theorem 1.4 and Remark 1.5.** Their strongly log-concave-source result allows bounded logarithmic perturbations, but the targets are compactly supported. With κI≤D²U≤κ′I, the stated W₁ map exponent is κ/(2κ′+7κ); the accompanying discussion permits exponents below κ/(2κ′+6κ). Remark 1.5 expressly leaves unbounded targets untreated and points to the compact-source finite-moment work above. Thus it is not an equivalent all-q>2 theorem. The present theorem, conversely, does not encompass arbitrary non-log-concave bounded perturbations. [Primary text, §1.1](https://arxiv.org/html/2411.04908v3#S1.SS1).

**Mischler–Trevisan, version 3.** Their map estimates use compact source and target supports and two-sided source-density bounds. Section 1.4 separately discusses finite-moment extensions and identifies weighted convex-gradient interpolation as an issue for general log-concave sources. Proposition 4.2 restates the compact-domain, bounded-gradient reverse-Poincaré estimate. These are relevant antecedents and motivation, not the asserted translation-ratio theorem. [Primary text, §1.4 and §4.1](https://arxiv.org/html/2407.19337v3).

## Same exponent does not mean the same theorem

**Divol–Niles-Weed–Pooladian, Theorem 4.3.** This already gives W₂^(1/3), but for regular compact sources and finite targets whose constants depend on positive atom-mass bounds, separation, count, and angular geometry. It does not imply uniformity over unbounded q-moment targets. [Primary text, §4](https://arxiv.org/html/2404.02855#S4).

**OpenAI, Sharp One-Third Stability of Brenier Maps.** The inherited source result is uniform over all targets in a fixed compact set for a uniform compact-convex source. The present finite-q statement retains its exponent and proof strategy but changes both the source and target scope. Its Gaussian bounded-target sharpness construction adapts the source's three-plane example. [Pinned primary manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-One-Third-Stability-of-Brenier-Maps-September-25-2026/article.pdf).

**Mérigot's 2026 sharp-stability preprint remains incompletely compared.** The HAL full text was unavailable for this comparison. Han–Zhu Proposition 2.7 reproduces its Theorem 2.2 for compact bounded-density sources: the fourth power of map distance is controlled by the dual pairing, yielding W₁^(1/4). That statement does not supply the full-Gaussian, unbounded-target result. It also cannot establish that the inaccessible paper contains no relevant additional theorem. [Primary paper reproducing the estimate](https://arxiv.org/html/2606.23037#S2.SS5); [bibliographic record](https://hal.science/hal-05616391).

A W₁ exponent must not be compared numerically with a W₂ exponent as though the metrics were identical. The inequality W₁≤W₂ transfers a W₁ bound with the same exponent, not a better one. Finite-moment interpolation between metrics introduces additional moment-dependent powers.

## Translation interpolation and older weighted inequalities

Weighted derivative comparison is not a new subject. Hussain–Pečarić–Shashiashvili's Theorem 3.1 treats convex functions on an infinite interval with growth and weight conditions, but explicitly assumes their difference is uniformly bounded. It is not the displayed L²-potential/L^q-gradient translation-ratio estimate. [Primary paper, §3](https://link.springer.com/article/10.1155/2008/343024).

Likewise, the 2016 *Weighted reverse Poincaré-type estimates for the difference of two convex vectors*, Lemma 2.1, uses a smooth interval weight with vanishing endpoint value and derivative, a supremum norm of the function difference, and the weight's second derivative. It is a methodological predecessor, not a directly interchangeable finite-q Gaussian interpolation theorem. [Primary paper, §2](https://link.springer.com/article/10.1186/s13660-016-1133-x).

The Gaussian exponential density-ratio formula itself is elementary and should not be presented as new. The specific point requiring attribution comparison is the common-minimum endpoint weight combined with monotonicity of convex derivatives, translation-ratio control, and L^q rather than bounded gradients. No equivalent statement was established in this focused inspection; that is not proof of novelty.

## Endpoint interpretation

Qualitative continuity of the Brenier-map assignment on P₂ is classical, as recalled in the introduction of Letrouit's *Unstable optimal transport maps*. Its counterexamples instead concern singular source-density behavior or nonconvex bounded source geometry. They do not identify the fixed full-Gaussian, exactly bounded-second-moment obstruction stated here. [Primary published article](https://comptes-rendus.academie-sciences.fr/mathematique/articles/10.5802/crmath.834/).

An elementary compactness observation clarifies the distinction: the closed class of probability measures with q-th moment at most a fixed constant, for q>2, is compact in W₂, so qualitative continuity already gives some uniform modulus for a fixed absolutely continuous source. The quantitative one-third rate and its sharpness are the substantive claims. Bounded second moments alone do not give W₂ compactness. Thus failure of a uniform modulus at q=2 does not contradict pointwise continuity on P₂.

**Conclusion.** The checked papers contain finite-moment stability, one-third interpolation, and weighted derivative comparison separately. None of the inspected statements establishes the complete combination of full Gaussian source, every q>2, arbitrary q-moment-bounded targets, and a sharp W₂^(1/3) rate. Attribution to those antecedents remains necessary, and the inaccessible-source uncertainty remains explicit.
