# Independent hostile audit: critical covering gauge

Audit date: 7 October 2026. Public report adapted from the frozen independent audit.

## Verdict

**PASS, full stated mathematical scope.** For every nondecreasing finite-valued h:[1,∞)→[1,∞) with h(t)→∞ and every infinite-dimensional real Banach space B, the construction proves the existence of the stated countable compact K⊂B, with upper box dimension zero, Assouad dimension exactly two, the universal doubling bound 1+5·76800^8, no bi-Lipschitz embedding into any finite-dimensional real normed space, the all-scale bound with C=350000, and unbounded normalized critical exponent-two covering numbers.

No theorem-level correction was found. This is an independent ordinary mathematical proof audit, not a formal verification, a computational certificate of the existential witnesses, or a novelty/optimality determination. The frozen subject is preserved; the public note adds only the optional exposition clarifications recorded below.

## Frozen inputs and primary sources

- Frozen gauge subject: `../avoidance-covering-provenance/audited-subjects/critical-gauge-audited-subject.md`, SHA-256 `f1da669946c4cb43fc2d694201af9e3845a374f944740735f86b672e53ce85eb`.
- Entry 003 source: `../avoidance-covering-provenance/sources/mxym-003/assouad_two_zero_box.tex`, SHA-256 `3b202f7c835107f21a08b5f69b78dfdf8ea06cc14d9df8837be27c5097ee7623`.
- Pinned OpenAI family-098 source: `../avoidance-covering-provenance/sources/openai-098/main.tex`, SHA-256 `3eac74d00462787aec0f48599cdf51d6b14599c53fdbb247f16539d8cfdd06c7`, Git blob SHA-1 `4c45439184128f24b1bde5cbcf3dc56d8f95afe3`.

Exact immutable repository bindings are recorded in the shared public provenance manifest. The original audit report SHA-256 is `c4630ccee7f70d8ea0f1399174da15b21e712709f57f58b5db564ab3166885e0`.

Verified primary sources:

- [Pinned family-098 source](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-doubling-Hilbert-subset-with-no-finite-dimensional-bi-Lipschitz-embedding-September-25-2026/build/main.tex), sections 2–5 and 7.
- [Catrina–Ostrovska–Ostrovskii, publisher PDF](https://aif.centre-mersenne.org/item/10.5802/aif.3672.pdf), Theorem 1.1: the classical almost-Euclidean finite-dimensional subspace statement needed for each T_j.
- [Naor–Neiman, author-hosted PDF](https://web.math.princeton.edu/~naor/homepage%20files/assouad-N(K).pdf), Theorems 1.1 and 1.2: doubling spaces have finite-dimensional bi-Lipschitz embeddings after snowflaking; this does not assert an embedding of the original metric.

## 1. Quantifiers, scale choice, and rounding

The quantifier order is ∀h ∀B ∃K, with C and the doubling bound independent of both h and B. The sheet schedule and finite source witnesses can depend on h. Dvoretzky maps and cluster placements can additionally depend on B. No prospective target dimension or distortion enters the choice of K.

Because h tends to infinity, each threshold T_(n+1)≥1 with h(T_(n+1))≥5^(n+1) exists and is finite; continuity or strict monotonicity is unnecessary. A precise admissible rounding is to set Q_0=1 and choose Q_n as the least power of two no smaller than max{Q_(n−1),1024,2^n,128T_(n+1)}. Then Q_n are nondecreasing dyadic integers and ρ_1=2^−10, ρ_(n+1)=ρ_n/Q_n are positive reciprocal dyadic integers. In particular ρ_(n+1)≤ρ_n/1024<ρ_n/1000 and Q_n→∞.

For an active interval a,…,a+m−1 with m≥2, the endpoints give t=R/r>ρ_a/(16ρ_(a+m−1))=(Q_a⋯Q_(a+m−2))/16. Its final factor has index a+m−2≥m−1, so monotonicity of Q makes the product at least Q_(m−1). Hence t/8>Q_(m−1)/128≥T_m and h(t/8)≥5^m. For m=0 or 1, 5^m≤5h(max{1,t/8}). This proves equation (2), including t close to one and all endpoint cases.

## 2. Refined source covering estimate, at every scale

Entry 003's equation (1) is valid for the new schedule, not only its particular 1000^−j² schedule. Coordinates with ρ_j>R are fixed in a closed radius-R ball. At active levels r/16<ρ_j≤R, a cell of side at most r/16 meets at most two strips in each direction because its side is strictly smaller than both strip widths ρ_j and W_jρ_j. Thus at most four nonzero labels, plus zero, occur per cell per active level; the number is independent of the color count and aspect ratio.

The number of base cells is ceil(32R/r)^2≤1089(R/r)^2. Fine-level squared distance is at most 2∑_(ρ_j≤r/16)ρ_j²≤2(r/16)²/(1−10^−6); adding the base squared diameter 2(r/16)² remains strictly below r². Choosing a point of S in each nonempty group produces intrinsic centers. Boundary assignments, empty groups, an empty active interval, and finite-support versus infinite tail bounds cause no omission. The resulting estimate is 1089t²5^m, hence 5445t²h(max{1,t/8}).

The source also remains 76800-doubling: the interval (R/64,R] has at most one sheet level, at most 129 strip labels per direction are possible, and fewer than 300 labels times 16² base cells suffice. This argument needs only adjacent ratio at least 1000.

## 3. Inherited nonembedding: the schedule change is legitimate

I checked entry 003's appendix against the pinned family-098 source. The extremal derivative set, lexicographic compactness lemma, horizontal and vertical energy estimates, common-sheet crossings, and finite-dimensional volume contradiction survive unchanged. Their only absolute sheet-level choice is: after fixing a finite-support sheet, a square side l>0, N, and n, choose an unused recurring level with (N_j,W_j)=(N,n) and Nnρ_j<l n^−8/100. Every pair recurs infinitely often and the new ρ_j→0, so this choice exists.

No lower bound on adjacent sheet ratios is used by the analytic obstruction. The stronger decay does not replace or remove W_j=n; the anisotropic recurring aspect ratios are retained. The horizontal mean-square error is multiplied by n² and still tends to zero; the vertical first-column deficit is O(1/n), permitting the lexicographic lemma to control the second column. The line selections are from full-measure sets, and oscillation estimates hold at every crossing without requiring differentiability there. The same added-sheet map is used on its horizontal and vertical portions.

Consequently S(ρ) admits no finite-distortion embedding into any Euclidean R^k. Product compactness then yields, for each j, a finite X_j⊂S(ρ) with no distortion-≤j embedding into R^j. The compactness proof uses compact Euclidean coordinate balls and finitely many pair constraints; it does not require S(ρ) itself to be compact. Here “the witnesses in entry 003” must mean applying its witness lemma to this new S(ρ), not literally reusing point coordinates from the old fixed schedule. This is the natural reading of the candidate's preceding instruction to use S(ρ).

## 4. Exact packing witnesses and critical content

The rational grid points p_(k,l)=((k+1/3)ρ_j,(l+1/3)ρ_j), 0≤k,l<q_j=1/ρ_j, are distinct and lie in [0,1]². For v≤j, ρ_v/ρ_j is an integer, so (l+1/3)/(ρ_v/ρ_j) cannot be an integer; each y-coordinate belongs to an open horizontal strip at every such level. Independently choosing zero or its permitted horizontal label at all j levels gives exactly q_j²2^j distinct finite-support points of S(ρ).

Their squared distance from o is less than 2+∑_vρ_v²<3<4. Distinct base points are at least ρ_j apart; points over one base point differing in a sheet coordinate are at least ρ_v≥ρ_j apart. Thus equation (3) is valid, including all color counts. The specification is exact and compressed, but enormous; it is a packing certificate, not a computable certificate of the nonembedding witnesses.

Adjoining P_j and o preserves the witness obstruction. A linear Dvoretzky map normalized by ||u||₂≤||T_ju||≤2||u||₂ gives a radius-four cluster packing with separation at least ρ_j. After translation and scaling, the K-ball centered at the image x_j of o with R_j=4τ_j contains every packing point. At r_j=τ_jρ_j/3, any radius-r_j ball in the ambient Banach metric has diameter 2r_j<τ_jρ_j, regardless of its center, and therefore covers at most one packing point. The ratio R_j/r_j=12q_j yields normalized critical content at least 2^j/144. Additional clusters and centers do not weaken this lower bound.

This alone rules out every exponent s<2: an exponent-s estimate would imply N_r/t²≤C t^(s−2)≤C for t>1, contrary to the unbounded critical content. There is no need to infer the lower dimension from global cluster spacings.

## 5. Banach transfer and sparse assembly

Each span X_j is finite-dimensional Hilbert space. The classical Dvoretzky statement supplies a linear almost-Euclidean realization in every infinite-dimensional real Banach space; normalization gives the stated lower constant one and upper constant two. It is not an isometric-transfer claim. No compatibility between the different T_j is needed.

For an intrinsic Y_j-ball, its source preimage lies in a source radius-R ball. Cover that source ball at radius r/4 and recenter only the balls meeting the preimage at preimage points. The twofold image expansion and twofold recentering loss give radius r. Applying equation (2) with source ratio 4R/r gives A_0=5445·16=87120 and the gauge h(max{1,R/(2r)}), exactly equation (5). T_j need not be defined at the original source cover centers. The same intrinsic argument gives uniform doubling at most 76800^4 after any finite enlargement of X_j.

After the enlargements, recompute M_j=∑_(i≤j)|X_i| and then choose positive a_j with a_(j+1)≤a_j/2, a_j≤e^−j², and a_j≤M_j^−j. These inequalities are simultaneously feasible. Translation and sufficiently small τ_j put C_j inside B(a_jv,a_j/100); finite sets impose no obstruction to this placement. For i<j, the separation is at least 97a_i/200, and ||p||≤101a_j/100 for p∈C_j.

Countability is immediate. Any sequence with cluster indices tending to infinity converges to zero; a sequence in a finite union of clusters has a constant subsequence. Thus K is compact. At 2a_(j+1)≤r<2a_j, the later clusters fit in the radius-r ball at zero and the first j require at most M_j point balls. Therefore log N_r(K)/log(1/r)≤log(M_j+1)/(j log M_j−log 2)→0. Enlarging by P_j changes only M_j and does not invalidate this proof.

For doubling, after one tail ball there are at most five relevant scales in (R/4,400R/97] whenever two or more clusters meet the observation ball; one isolated larger cluster is handled separately. Two intrinsic cluster doublings cover each intersection at radius R/2, yielding 1+5·76800^8. No assertion that doubling constants are hereditary to arbitrary subsets without recentering is used.

## 6. All-scale upper gauge constants and exact Assouad dimension

Let t=R/r>1. If an intersected cluster has a_i>5R, the separation estimate precludes every other cluster, and ||p||≥99a_i/100 precludes zero. Its intersection lies in an intrinsic cluster ball of radius 2R, and equation (5) costs at most 4A_0t²h(t)=348480t²h(t).

Otherwise all intersected clusters have a_j≤5R. The a_j≤r/4 tail fits in one radius-r ball at zero. For a remaining cluster, diameter≤a_j/50. If diameter≤r, one intrinsic ball suffices and 1≤16(a_j/r)²h(t). If diameter>r, use equation (5) with enclosing radius a_j/50; its cost is (A_0/2500)(a_j/r)²h(max{1,a_j/(100r)}). The last gauge argument is at most t because t>1 and a_j≤5R.

Geometric decrease gives ∑_(r/4<a_j≤5R)(a_j/r)²≤(100/3)t², even when several indices are skipped. Adding both harmless cost bounds and the tail gives coefficient

1+(16+87120/2500)·100/3 = 25439/15 = 1695.933333… <1696.

Thus C=350000 covers both cases, with no missing R, r, center, or scale range. The gauge inequality alone must not be used to deduce dimension ≤2 for an arbitrary h, which may be superpolynomial. Instead Q_j→∞ yields the entry-003 5^m≤C_εt^ε estimate for every ε>0; recentering and the same sparse assembly then give all exponents 2+ε. Combined with the packing lower bound, this proves Assouad dimension exactly two.

Finally, if K embedded into any finite-dimensional normed target, composing with an equivalent Euclidean norm gives finite distortion D into R^k. Choose j≥k and j≥2D. Restriction to C_j and precomposition with its source placement would embed X_j into R^j with distortion at most 2D≤j, contradicting its witness property.

## Scope and optional exposition clarifications

No mathematical repair is required. For a standalone presentation, explicitly say that the finite witnesses are chosen anew for S(ρ) using entry 003's witness lemma, and include the concrete dyadic rounding above. The phrase “diverge arbitrarily slowly” is accurately formalized by the nondecreasing excess profile F_K(T)=sup{N_r^K(B_K(x,R))/(R/r)²: 1<R/r≤T}: it is finite for finite T, satisfies F_K(T)≤350000h(T), and tends to infinity by the packing witnesses. It need not mean that every individual ball's normalized covering count tends to infinity.

The argument gives an h-controlled existential refinement of entry 003. It does not show that Assouad dimension two is optimal among nonembedding obstructions, does not rule out another construction with a genuine exponent-two bound, and does not supply an exhaustive novelty claim. The family-098 analytic obstruction, qualitative finite-witness selection, and qualitative Dvoretzky transfer remain external/classical dependencies; the new ingredients audited here are the tailored schedule, quantitative gauge transfer, and exact finite packing lower bound.
