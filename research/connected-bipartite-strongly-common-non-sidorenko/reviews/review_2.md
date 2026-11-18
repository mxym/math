# Second adversarial check: connected bridge-and-squares separator

Internal AI-assisted review, 18 November 2026. Reviewed frozen mathematical draft SHA-256 b5a6be21205238268afa9c6cdfc106632ff6c6263b7bc091c42c5d7a3c20ef30. The credited input is the fixed OpenAI PDF on commit adc7f1241b42e322a6451854ab7e4b4c146bf78a; I compared its served Git blob identity 4855f35e8c778b8b591db993546d0607d62b5cdb and size 639874 to a downloaded copy of the original PDF, SHA-256 0c0d7b5eb1ed43c00ed2f60d2347b7d5511bad2218efe12c28fd9968ee549b0f. This is a re-derivation, not independent certification of the full finite-field counting proof.

**Decision:** no mathematical gap found in the stated connected, two-color, strong-common/non-Sidorenko separation. M=2^3850 is a finite, valid sufficient, not necessary, choice. The simple bipartite graph has a bridge and cut vertex, so does not address 2-connectivity. Do not infer that the unmodified 35-vertex H is common, strongly common, or uncommon.

### Where circular near-constant arguments could have gone wrong

The proof only bounds fluctuations for the fixed rooted graphs H, C4, H with a pendant edge, and H with a bridge and one square (and the doubled second-moment graphs). It never needs a neighborhood in which the enormous graph B_M is already Sidorenko. Thus the threshold for the defect is uniform in M. If selected edge subgraphs in the centered expansion contain extra edges between the chosen cycle vertices, the trace argument fails, but a *shortest cycle in the selected graph* is induced. External factors are then indeed separated into bounded one-vertex multipliers. For forests, two leaves in a nontrivial component are distinct nonadjacent leaves, with either one shared neighbor or two independent integration variables after absolute bounding. The constant-kernel expansion's one-edge term is zero. Comparing the two Hilbert–Schmidt norms of the squared block operators gives R≤(1+2/p²)Δ, hence η≤(33Δ)^{1/4}. This remains true if Δ=0, and only the dense color needs the density floor for that bound.

### Independent calculation of the bridge main term

Define c(x)=∫K(x,y)²dy, r(x)=∫(K(x,y)−p²)²dy≥0, d=p+z and L=T_{W-p}. Row integrals of K=T_W² are T_W d=p²+pz+Lz. Integrate (c−p⁴)d directly, obtaining the **exact positive-remainder identity**

    B = 4p³ s + 2p² <z,Lz> + ∫ d(x)r(x) dx .

Here ∫Lz=s by selfadjointness. Thus B≥2p³s whenever η≤p. Separately the rooted square second moment gives B≥pΔ−sqrt(C₈ sΔ), C₈=8448. Splitting now at s=p²Δ/(4C₈) gives a common lower bound

    B ≥ min(p/2, p⁵/(2 C₈)) Δ > 2^{-25} Δ,  p≥1/4.

This variant does not use the original draft's arbitrary 2^{-20} splitting threshold. With ∆≤2^{-2706}, ||L||op≤2^{-675}; ||h−∫h||≤2^70√Δ, ||c−p⁴||≤2^7√Δ. The remainder arising from b=T h is at most 2^{-598}Δ; m≥(1/4)^286=2^{-572}, so the original lower bound I≥2^{-598}Δ holds, with no assumption of a correlation sign for h and c. Constants are such that Mκ≥2C₆₇.

### Global and very sparse colors

Color density bounded below and Δ≥δ: to check the rooted completion bound, integrate the 22 unmarked vertices on the size-23 side of K_{23,13}. Draw the 13 opposite vertices with tilted row measure W(x,y)dy/d(x), Jensen first on the 22nd power, then on K² to exponent 13/2. The resulting power d^{13(2−23)}≥1 when d>0 permits discarding it; at zero degree both sides vanish. This establishes b≥c^143. The far-case factor is at least 2^{-1144}(1+2^{3850−2706})>1. For a color of density p>3/4, q=1−p, this yields enough even for the strong right side, because p^{4M}−p^{67+4M}−q^{67+4M}≥p^{4M}(1−p^67−q^67)≥0.

In the remaining sparse case the unnormalized centered kernel flips sign; s and Tr L^4 are exactly unchanged, not just comparable. The difference I_Q uses one fixed square rather than the enormous bouquet: writing t(H^{bridge}+one square,Q)−q⁴ t(H^{bridge},Q) cancels the constant terms. Consequently no factor grows exponentially with M other than q^{4M−4}, which is suppressed by (q/p)^{4M−4}. The elementary tangent inequality uses convexity at q^4, not a Taylor expansion requiring closeness pointwise, and the argument permits q=0. The stated small-color error coefficient bound follows from 2^81 M (1/3)^{4M−4} ≤ 2^{-599}M. No denominator q is needed.

### Decorated OpenAI witness

The exact row and column means of the finite rectangular kernel follow by averaging over one freely uniform matrix tuple in (3.6) conditional on both types. Exact translation invariance jointly in *every* root matrix coordinate permits averaging the root matrix too, conditional on its type. Taking four template incidences only from U_{0,1}, the full-square factor of (3.4) is unique. Conditional on four independent edge packages, the coordinate models factor. When averaged, nonempty coordinate subsets yield products of four vanishing first moments by (3.7); dilution and thinning preserve this together with the fixed size of the coordinate and type sets. Thus the rootwise square integrals approach one uniformly in the growing finite spaces; it would be insufficient simply to invoke a globally averaged square density. The crossed-product rooted square factors into the X-root and Y-root rectangular squares because their remaining random tuple coordinates are independent. The product kernel is nonnegative and exactly row stochastic, so if c^{M} is uniformly 1+o(1), the accumulated bridge/bouquet error is ≤o(1) ∫h. The latter has a strict limiting deficit by (3.24)–(3.25); choose M, fix ε before prime→∞, then select a finite prime. No uniform bound on the mean-one kernels or at the rare root labels is presumed. Finite-host sampling for the positive scaled gap includes collisions and Jensen in the correct direction.

### Literature and scope

The [GLLV converse](https://doi.org/10.1017/S0963548322000074) does not require connectivity; connectedness strengthens an earlier [disconnected result](https://github.com/mxym/math/blob/0deb2d848775ea6a76b5aee6da61374e9129286c/research/bipartite-strongly-common-non-sidorenko/README.md). [Král'–Volec–Wei](https://arxiv.org/abs/2206.05800) already bridge a core and padding; [Ko–Lee](https://arxiv.org/abs/2207.09427) obtain highly connected common graphs with large chromatic number, without showing a connected strongly common *bipartite non-Sidorenko* graph. [Lee–Noel](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v33i2p1/pdf/) discuss disconnected commonness and the strong definition. [Král' et al.](https://arxiv.org/abs/2006.09422) quantify over all color counts for equivalence with Sidorenko. I found no paper stating the current separation in targeted web and recent announcement searches, which is not a priority certificate. The public manuscript links to the disconnected result and retains the limitations regarding the external rank-layer input, non-2-connectivity and absence of external human review.

### Separate numerical controls

Independent [controls_2.py](controls_2.py), Python standard library, optimized-mode pass: 64 symmetric Boolean graphons with three unequal atom probabilities, checking the alternative exact positive-remainder identity and all 192 complete rooted K_{23,13} ≥ c^143 inequalities by multinomial enumeration. A nonconstant rectangular 2×3 positive Markov kernel with unequal part weights checks all six crossed-product rooted square factorizations exactly. These diagnostics do not themselves establish the graphon theorem or the finite-field limit.

**Version binding.** The review concerns the mathematical draft with the hash recorded above. The [public manuscript](../README.md), SHA-256 7221bd11baa5117c0ddf6500744d75eba734a7cfa6054b2edc677730e5018c0a, retains the construction, hypotheses, bounds, equation numbering and proofs; the presentation adds a summary, scope and source links, and instructions for the finite checks. This report is an internal review and not an outside referee's endorsement.
