# Sharp spherical caps for E₇ and E₈ at every aperture

How many roots fit in a cap of radius θ, and how few can it contain? The tables below give both sharp extrema for the 126 roots of E₇ and the 240 roots of E₈, for every θ, with open or closed boundary and optionally with root centers excluded. As a consequence their normalized spherical cap discrepancies are **2/7** and **21/80**, respectively. Equality occurs only on the 28 E₆ equators of E₇ and the 120 E₇ equators of E₈. These are results about the two fixed point configurations, not about arbitrary kissing configurations.

## How to read the answer

Use roots r and center x of length √2, and put h=2 cos θ. For h>0 set t=2/h².

| Extremum | Open (x·r>h) | Closed (x·r≥h) |
|:--|:--|:--|
| Largest count | largest k with Aₖ<t | largest k with Aₖ≤t |
| Smallest count | least k with Bₖ≥t | least k with Bₖ>t |

If centers at roots are excluded, drop the following *equality* cases only: in the closed maximum test drop k=1 and 28–33 in E₇, and k=1 and 37–57 in E₈. In the open minimum test drop k=1–5 in E₇ and k=1–7 in E₈. The strict tests are unchanged.

At h=0, among all centers the sharp open minimum/maximum are 27/63 in E₇ and 57/120 in E₈. Excluding roots leaves E₇ unchanged; E₈ then has open minimum **78** (maximum still 120). Closed hemisphere counts follow by subtracting open counts from the total. For h<0 take complements at −h, interchanging open and closed. We give extrema, not a claim that every intermediate integer is realized.

### E7 lower envelope A

|k | value | k | value | k | value|
|:-- | --: | :-- | --: | :-- | --:|
|0 | 0 | 13–17 | 4/3 | 55 | 18|
|1 | 1/2 | 18–27 | 3/2 | 56 | 39/2|
|2 | 2/3 | 28–33 | 2 | 57 | 28|
|3 | 3/4 | 34–42 | 7/2 | 58 | 63/2|
|4 | 4/5 | 43 | 11/2 | 59 | 42|
|5 | 5/6 | 44–47 | 6 | 60 | 111/2|
|6 | 6/7 | 48–50 | 15/2 | 61 | 159/2|
|7 | 7/8 | 51–52 | 23/2 | 62 | 231/2|
|8–10 | 1 | 53 | 12 | 63 | 399/2|
|11–12 | 5/4 | 54 | 31/2 |  | |

### E7 upper envelope B

|k | value | k | value | k | value|
|:-- | --: | :-- | --: | :-- | --:|
|0 | 3/2 | 10–16 | 4 | 22–25 | 8|
|1–6 | 2 | 17–19 | 6 | 26 | 10|
|7–9 | 7/2 | 20–21 | 15/2 | 27–63 | ∞|

### E8 lower envelope A

|k | value | k | value | k | value|
|:-- | --: | :-- | --: | :-- | --:|
|0 | 0 | 30–57 | 2 | 109–110 | 44|
|1 | 1/2 | 58–78 | 4 | 111 | 56|
|2 | 2/3 | 79–83 | 6 | 112 | 60|
|3 | 3/4 | 84–92 | 8 | 113 | 80|
|4 | 4/5 | 93–97 | 12 | 114 | 92|
|5 | 5/6 | 98 | 14 | 115 | 116|
|6 | 6/7 | 99 | 16 | 116 | 140|
|7 | 7/8 | 100–104 | 20 | 117 | 200|
|8 | 8/9 | 105 | 28 | 118 | 260|
|9–14 | 1 | 106 | 30 | 119 | 380|
|15–19 | 4/3 | 107 | 32 | 120 | 620|
|20–29 | 3/2 | 108 | 36 |  | |

### E8 upper envelope B

|k | value | k | value | k | value|
|:-- | --: | :-- | --: | :-- | --:|
|0 | 1 | 29–35 | 6 | 56 | 14|
|1–12 | 2 | 36–45 | 8 | 57–120 | ∞|
|13 | 5/2 | 46–48 | 10 |  | |
|14–28 | 4 | 49–55 | 12 |  | |

## Proof and exact replay

Write G for the Gram matrix of the simple roots (diagonal 2, edge entries −1) and move the center to the closed dominant chamber. In simple-product coordinates wᵢ=αᵢ·(x/h), positive roots r are vectors of nonnegative simple coefficients, the threshold is rᵀw=1, and the squared norm is wᵀG⁻¹w=t. Roots above threshold form an upper ideal for the positive-root order. An upper ideal may grow or shrink one element at a time; thus testing containment of a k-element ideal, or containment *in* one, gives the exact two extremal problems.

For each k-element upper ideal C minimize wᵀG⁻¹w over w≥0, rᵀw≥1 for minimal r∈C; take the least answer over C for Aₖ. For a candidate set of independent active rows J of the inequality system Lw≥b, solve (Lⱼ G Lⱼᵀ)v=bⱼ. The verifier checks v≥0 and w=GLⱼᵀv satisfies the full system; the normal-cone identity proves optimality. The strictly convex objective has a unique minimizing point. At most n independent supporting normals suffice by conic Carathéodory. Floating point only proposes candidate active rows; acceptance uses exact integer determinants and feasibility checks, with exhaustive fallback.

For Bₖ impose w≥0 and rᵀw≤1 for maximal r outside C (no constraint on roots in C), maximize the squared norm, and then maximize over C. A missing upper-bound coordinate gives an unbounded ray. Otherwise all coordinates are bounded. A strictly convex quadratic has no nonvertex maximum on this polytope, so enumerating all feasible independent n-row vertex bases is exact. Scaling the lower minimizers or upper witnesses gives the strict inequalities in the reading rule. In the interior of a norm threshold the strict witness can be perturbed away from a root center. At a finite equality the verifier tests the unique minimizer, or every maximizing vertex, against the dominant highest-root ray. The unbounded case admits unbounded nonroot witnesses since the upper polyhedron has interior.

The program enumerates all 4,160 E₇ ideals and 25,080 E₈ ideals. To audit hemisphere extrema separately, the counts of positive roots using each simple node (chain nodes in order, final node attached to the third chain node) are
```
E7  33 47 53 50 42 27 42
E8  78 98 106 104 97 83 57 92
```
The strictly positive products are the union of the support lists for the nonzero coordinates of w. Thus only the unique minimum ray can attain each minimum. The E₇ ray deletes a node leaving E₆ and has 56 signed chamber-orbit directions; the E₈ ray deletes a node leaving E₇ and has 240, all roots. Reflection closure counts these directions exactly. Any other E₈ direction has a nonroot simple coordinate in its support; the best such ray gives 78. Generic interior chamber vectors see half the roots.

## Why hemispheres give the precise discrepancy

For a unit-sphere cap with cosine c=h/2≥0 and ambient dimension n, its normalized area is F(c)=1/2−Cₙ∫₀ᶜ(1−s²)^((n−3)/2)ds. For n=7,8 the constants are 15/16 and 16/(5π). Let N be the cardinality and M the minimum open hemisphere count. The hemisphere exhibits discrepancy D=1/2−M/N. It suffices to exclude equality or larger discrepancies at c>0, by complementation.

If a k-point cap has k/N>D, then c≤1/√(2Aₖ). The replay verifies F(1/√(2Aₖ))>k/N−D for every such k. For k/N≤D the excess cannot exceed D, with strictness since a zero-area cap contains at most one point. If k<M, then c≥1/√(2Bₖ); the replay verifies F(1/√(2Bₖ))<k/N+D. For k≥M this deficit is strictly smaller than D because F(c)<1/2. These bounds apply to either choice of boundary. They prove the asserted discrepancy and identify all maximizing equators.

The numerical integrals in that argument are **certified by rational inequalities**, not accepted from a floating-point integrator: with 2,048 equal bins on [0,1], enclose the radical threshold by adjacent grid points using an integer square comparison. Use right/left rectangle sums for the decreasing density. Round each ordinate outward on the same grid by comparing squares as integers; enclose π by 333/106<π<355/113. The strict comparisons include the accumulated error.

Run [the standalone verifier](verify-kissing-e7-e8-all-cap-angles.js) with Node.js:
```sh
node verify-kissing-e7-e8-all-cap-angles.js 7
node verify-kissing-e7-e8-all-cap-angles.js 8
```
It prints each rational endpoint and its nonroot flag before verifying the discrepancy. The [E₆ computation](KissingE6AllCapAngles.md) is the smaller-rank antecedent. For background on the discrepancy definition and a general finite characterization, see [Heitsch & Henrion](https://www.wias-berlin.de/people/henrion/spher-cap-disc-online.pdf). No priority or general optimal-design claim is intended.
