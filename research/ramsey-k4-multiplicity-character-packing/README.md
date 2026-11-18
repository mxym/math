# An exact step-graphon upper bound and a support condition for K₄ Ramsey multiplicity

18 November 2026. AI-assisted research note for review; not externally peer-reviewed and not a claim of historical priority. No standalone release, submission, or DOI is asserted here. The problem of determining the Ramsey multiplicity constant $c_4$ remains open.

## A small concrete improvement

For $M(W)=t(K_4,W)+t(K_4,1-W)$ and $c_4=\inf M(W)$, an equal-weight finite graphon gives
$$
 c_4\le \frac{17013023763767619940673353171840153525115959621}
 {564487612837806398270122868776411650620129280000}
 = 0.03013887882896015\ldots.
$$
The exact value beats the smallest fully specified numerical upper bound in [the Tao optimization-problems catalog, item 89](https://teorth.github.io/optimizationproblems/constants/89a.html), not necessarily every announced or unpublished construction. The [SK base](https://github.com/JeetuSK0808/tao-constants-certificates/tree/3d9431a/c89-k4-ramsey-multiplicity) has exact value
$$
 B= 27220838459434583306277336063848530765605851167/
 903180180540490237232196590042258640992206848000.
$$
The new witness changes it by exactly
$$
 -729010652335333284981507141875700526289/
 1505300300900817062053660983403764401653678080000
 \simeq -4.84296\cdot10^{-10}.
$$
The improvement is small; the structural support obstruction is a separate conclusion and **does not** imply that this refined witness is optimal.

## Exact finite construction and proof

Let $R/D$ be the pinned SK matrix on $n=3840$ classes with $D=2^{20}$ and all diagonal entries of $R$ zero. Each line of triangles.tsv.gz is $i,j,k,A_{ij},A_{ik},A_{jk}$, zero-based indices, integer signed amplitudes in this order. No unordered edge occurs in two listed triangles; all $|A_{uv}|\le\min(R_{uv},D-R_{uv})$. For each base vertex $v$, maintain a set of used triangle colors, initially empty. In file order greedily color each triangle by the least nonnegative integer unused at any of its three vertices, then mark it used there. The file uses colors $c=0,\ldots,22$; triangles of the same color have disjoint vertex sets.

The refined classes are $(v,z)$ with $z\in\mathbb F_2^6$, all equal weight (245760 total). For color $c$ put $\lambda_c=(1,\operatorname{bits}_5(c))$ and $\chi_c(z)=(-1)^{\lambda_c\cdot z}$. An edge in a listed triangle of color $c$ gets
$$
 W'((v,z),(w,z'))=(R_{vw}+ A_{vw}\chi_c(z)\chi_c(z'))/D .
$$
All unlisted pairs retain $R_{vw}/D$. This is symmetric and takes values in [0,1]. The signs are exact finite characters, not independent-edge simulations or rounded probabilities.

Expanding each homogeneous $K_4$ product, a set of perturbed edges contributes only if the incident labels sum to zero at each of its four sampled vertices. Their first coordinate is one, so degrees are even. Nonempty possibilities are exactly a triangle or a 4-cycle; at each vertex of degree two the two labels must match, hence the cycle uses a single label. Among same-color supporting triangles, a connected walk belongs to just one (they are vertex-disjoint). Thus the total perturbation is a sum of independent contributions from the listed triangles *even though some triangles of distinct colors share vertices*.

Write $r_e=R_e/D, u_e=A_e/D$, and for one triangle of base indices $T=\{i,j,k\}$
$$
 H_T=\sum_{l=0}^{n-1}\big[r_{il}r_{jl}r_{kl}-(1-r_{il})(1-r_{jl})(1-r_{kl})\big].
$$
Its contribution to $n^4(M(W')-M(W))$ is
$$
 24H_T u_{ij}u_{ik}u_{jk}
 +6\sum_{e\in E(T)}u_e^4
 +12\sum_{e\in E(T)}(1-r_e)\prod_{f\in E(T)\setminus\{e\}}u_f^2 .
$$
For the triangle term choose one of four missing vertices and one of six assignments of the three indices; the color difference follows from the odd number of perturbations. For each of the three labeled 4-cycles, a closed walk using the selected base triangle either alternates the endpoints of one edge (two choices of initial endpoint), or repeats one vertex and uses both other vertices (four orders per repeated vertex). In the former case both unperturbed diagonals have red probability zero. In the latter one diagonal is a loop and the other the opposite edge $e$, giving factor $1-r_e$. These counts yield the formula including collisions of base indices.

The verifier asserts the exact input value, the displayed decrement, and the final rational bound (including consistency with the displayed fractions in this file). Do not use Python optimization flags. The deterministic certificate checks that all 8320 terms are strictly negative *after* rounding and that their sum equals the exact change. Selection used a floating-point ranking among 409460 triangles of the fractional support, followed by greedy edge-disjoint packing; optimality of that heuristic is irrelevant.

## Independent base recount

The upstream base is required by pinned SHA-256 but not redistributed. Run with Python 3.10+, NumPy, GNU C++17, GMP and GMP C++ headers/libraries, and a little-endian Linux 64-bit machine:
```
sha256sum -c SHA256SUMS
python kernel_check.py
python verify.py /path/to/c89_stepgraphon_D20.json.gz
python check_walks.py /path/to/c89_stepgraphon_D20.json.gz
```
Fetch the input from the [pinned upstream directory](https://github.com/JeetuSK0808/tao-constants-certificates/tree/3d9431a/c89-k4-ramsey-multiplicity). SHA-256 for the gzip bytes: 82c28f7761f8392df6ed1728b5eefdc4ef388b266fc2beb1a2f0a54f7dd2631a. The triangle file hash is checked inside verify.py. The program parses the raw JSON, verifies weights/denominator and matrix, recomputes the upstream rational independently, then checks feasibility, labels, and each contribution with exact integer arithmetic. The 8320-triangle summation uses no floating point. It also cross-checks the whole signed-triangle formula on a separate small graphon with two triangles meeting at a vertex by enumerating every labeled quadruple of the refined kernel.

Rather than replay the upstream nine-prime matrix products, base_recount.cpp groups 3840 consecutive classes into 192 groups of 20. It checks symmetry, bounds, and simultaneous translation invariance of every within/between-group 20×20 block under $(\mathbb Z/5)\times(\mathbb Z/2)^2$ with local index $4a+b$. Each constant block is checked to be monochromatic; all other blocks have row and column sums independent of the internal vertex. Enumerate all unordered coarse 4-tuples **with repetitions** and weight by the exact number of distinct permutations. In either target color, reject tuples having a deterministic opposite edge. The nonconstant edges define a subgraph on the four labeled positions. If it is a forest with $s$ edges, sum leaves first, giving $20^{4-s}$ times the product of the relevant integer row sums and $D^{6-s}$ from the constant edges. If it is a triangle plus isolated vertex, integrate the free vertex and fix one triangle root by translations; explicitly sum over the other two. In any remaining case, transitivity fixes one root and 8000 possibilities for the other three are evaluated directly. This is exact, not a row-signature assumption. The largest inner sum is at most $20D^6<2^{125}$, so 128-bit inner accumulators suffice. Larger totals use GMP. The exact result matches the published fraction. This check is specialized to this input structure, not a purported universal verifier.

## Independently implemented perturbation check

[check_walks.py](check_walks.py) builds [independent_walks.cpp](independent_walks.cpp) with GNU C++17 and GMP. It reconstructs the integer base from the pinned JSON and recomputes the perturbation through direct weighted maps, without using the quartic simplification in the main checker. For each of the 8,320 selected triangles it loops over all six ordered embeddings and the possible fourth base vertex, and over all 81 maps from a labeled cycle to its three support vertices (including all collisions). This yields 8,320 strictly negative increments, 24,960 distinct edges, 23 labels and raw change numerator `-139970045248383990716449371240134501047488` with common denominator `3840^4 * (2^20)^6`. This extra check corroborates the perturbation, not the base count; the latter is checked by the preceding program. It does not establish optimality of any graphon or any historical priority.

## Prior work and scope of comparison

* A. Thomason disproved Erdős's proposal that $1/32$ was optimal in 1989. The open question is the **value** of $c_4$, not whether random is optimal.
* [Grzesik, Lee, Lidický, Volec, On tripartite common graphs](https://doi.org/10.1017/S0963548322000074) and [Parczyk, Pokutta, Spiegel, Szabó, New Ramsey multiplicity bounds and search heuristics](https://doi.org/10.1007/s10208-024-09675-6) provide the published context. The catalog cites a lower bound $1/33.77$; we do not improve it.
* [Van Seters–Jothimani](https://github.com/lukevs/k4-ramsey/tree/2cf216b) gave the balanced-sign cubic-plus-quartic refinement identity and a 3840-class witness. [Koshta](https://github.com/DennisKoshta/c89-k4-ramsey-multiplicity-certificate/tree/4fdbe0cecbb2519a17b90468a592c789a818f744) applies another sign refinement to that earlier witness. [Jeetu SK](https://github.com/JeetuSK0808/tao-constants-certificates/tree/3d9431a/c89-k4-ramsey-multiplicity) further optimized the 3840-block probabilities, giving the starting point here. We do not claim the sign-refinement identity as new. The disjoint colored character packing separates the contributions.
* The [catalog](https://teorth.github.io/optimizationproblems/constants/89a.html) reports Feinstein's seminar announcement of a bound below 0.030139 without a more precise value or disclosed certificate. That inequality is compatible with a value strictly smaller than ours. We found no better precisely specified public value in the catalog, its cited primary sources, or targeted scholarly/web searches; this is not an exhaustive novelty search.
* See STRUCTURE.md for a separate arbitrary-background support theorem and precise relation to the tensor-kernel method of [Csóka–Hubai–L. Lovász](https://arxiv.org/abs/1912.02926).

AI assistance: this research packet was developed by an OpenAI assistant, including candidate generation, derivations, source searches and independent checker implementation. “Independent” refers to an independently implemented count, not a mathematician's or referee's verification. The authors of the source constructions are not being represented as endorsing this work.

No copy of the upstream base dataset, no new license, and no change to existing rights are included.
