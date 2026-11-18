# The unweighted Braverman–Efremenko–Kol–Saxena–Zhang MaxCut inequality in all sizes

Research draft; independently checked in an internal AI review, not externally refereed. Bibliographic priority is unconfirmed. The theorem covers arbitrary finite **simple unweighted** graphs (equivalently, all present edges have one common positive weight). It does not settle the conjecture for arbitrary nonnegative edge weights, parallel edges of differing multiplicities, or the one-round channel resilience.

**Prior result.** The [authors’ full version, §11](https://eccc.weizmann.ac.il/report/2022/179/revision/1/download/) establishes the conjecture for all unweighted complete graphs (§11.1) and all unweighted graphs with at least 10⁹ edges (Theorem 11.1, §11.2); K₃ and K₅ are known equality examples. The claim here is removal of the size condition, together with completeness of those equality examples up to isolated vertices.

Let G have m edges, degrees d_i, and maximum cut C. Let the signs e_i be independent and uniform in {−1,1}, and K(d)=E|Σd_i e_i|. The claim is

    C ≥ 2m/5+(4/15)K(d).                                    (1)

Indeed, place the positive vertices in S; the difference between the numbers of internal edges of S and its complement is (1/2)Σd_i e_i. The expected sum of the two internal counts is m/2. Substituting min(u,v)=(u+v−|u−v|)/2 in [BEKSZ, ITCS 2025, Conjecture 3](https://doi.org/10.4230/LIPIcs.ITCS.2025.22) yields (1) after multiplying by m. The zero-edge instance of (1) is trivial. The maximum cut and m add over components; K is at most the sum of the component K's by the triangle inequality. It suffices to handle a connected graph on n≥2 vertices. Throughout we use the [classical Edwards–Erdős estimate](https://doi.org/10.4153/CJM-1973-048-X)

    C ≥ m/2+(n−1)/4.                                         (2)

## 1. All n≥17

By Cauchy–Schwarz and independence, K(d)²≤Σd_i². For a simple graph, [de Caen's bound](https://doi.org/10.1016/S0012-365X(97)00213-6) gives

    Σd_i² ≤ m(n−2)+2m²/(n−1).                                (3)

For completeness, take the unoriented vertex-by-edge incidence matrix B of the *complete* graph K_n, let N=n(n−1)/2, and let w be the 0–1 indicator vector of the m actual edges. Then d=Bw. Removing the means from both sides gives d−(2m/n)1=B(w−(m/N)1). The output lies orthogonal to 1, on which BBᵀ=(n−2)I+J has norm n−2. Consequently the squared norm of the centered output is ≤(n−2)(m−m²/N). Adding back 4m²/n gives (3). For example, the operator bound follows directly by taking the supremum of ⟨Bᵀv,w−(m/N)1⟩ over unit v⊥1; ||Bᵀv||²=n−2.

Let t=m/(n−1)≥1. By (2),(3), it suffices to check

    (t/10+1/4)² − (16/225)t(1+(2t−1)/(n−1)) ≥ 0.

For n≥17 the LHS is at least its value at n=17 evaluated at the same t. This value is exactly (t/30−1/4)². Squaring does not change the order, since both compared sides before squaring are nonnegative. This proves (1).

## 2. All 2≤n≤16: an exact 575-cell inequality

In a connected simple graph all d_i lie between 1 and n−1 and sum to 2m. K is convex and symmetric as a function of its coordinate vector. Maximize it on the box [1,n−1]^n intersected with the hyperplane of that sum. All vertices of this section have at most one coordinate strictly between the box bounds: two such coordinates could be perturbed in opposite directions along a nontrivial segment. Conversely, the maximum of a convex function on this nonempty compact polytope is attained at some vertex. All its vertices are permutations of the same packed vector x, obtained by filling n entries initially equal to 1, from left to right, with a total of 2m−n extra units up to capacity n−2 per entry. Thus K(d)≤K(x); graphic realizability of x is neither required nor assumed. For n=2 the section is just the singleton with both entries 1.

We use (2) rounded up, L=ceil((2m+n−1)/4). For each fixed n,m let

    P(X)=∏_{j=1}^n(1+X^{x_j})=Σ_s c_s X^s,    A=Σ_s c_s |2s−2m|.

Then 2^n K(x)=A exactly. The finite assertion is

    (15L−6m)2^n−4A ≥ 0                                       (4)

over n=2,...,16 and m=n−1,...,n(n−1)/2. Here are the row minima of the left side in increasing n:

    20, 0, 96, 0, 288, 192, 1856, 1536, 7680, 11264,
    43008, 49152, 172032, 294912, 884736.

These are small, completely specified integer calculations. Their recurrence takes c[0]=1 and replaces c[s] by c[s]+c[s−x_j] for each factor, with absent entries zero and all updates in that factor based on the old values. The exact standard-library script verify.py checks all 575 cases separately, terminating with a nonzero exit if any inequality fails, if a row has a malformed vector/count, if the total is wrong, or if the equality cases differ. CHECKS.txt additionally gives a minimizing m in each row. This verifies (4), hence (1).

## Equality in the unweighted assertion

For a connected graph in the finite range, (4) is strict except (n,m)=(3,3),(5,10). At these two pairs G is respectively K_3,K_5, and the packed vector and the bound L are realized, giving equality (as already observed by BEKSZ). In the large range, K(d)<||d||_2 because |Σd_i e_i| takes different values with positive probability, as is seen by comparing all signs positive to reversing just one sign. In a graph with at least two edge-containing components the triangle step is strict: with positive probability one component has all positive signs and another all negative signs. Hence apart from the zero-edge case, equality is exactly K_3 or K_5 together with any number of isolated vertices.
