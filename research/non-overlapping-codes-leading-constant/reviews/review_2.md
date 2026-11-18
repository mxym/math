# Second independent audit: the fixed-alphabet non-overlapping-code limit

**Verdict: PASS (internal AI review, not external peer review).** I independently rederived the upper and lower arguments, consulted the primary sources, and wrote a separate exact checker without importing or executing the author's checker. This report does not assert priority. The object reviewed was the 18 November 2026 draft “The leading constant for fixed-alphabet non-overlapping codes”, prose version before typesetting, SHA-256 `f2d221f7430c69a7a9c182e838dc11e54fc99074e65c5627a779cc4d3b41bc77`. The result is about fixed-length words: for each fixed integer q ≥ 2, the maximum S(q,n) satisfies nS(q,n)/qⁿ → (q−1)/(qe). No finite-length maximum formula or infinite exact optimality of a one-marker code follows.

## Upper bound: independent checks

1. [Stanovnik–Moškon–Mraz, Proposition 10](https://doi.org/10.1007/s10623-023-01344-z) has exactly the required domain: positive integer initial parts summing to q, subsequent nonnegative integer parts adding to the earlier left–right convolution, and the terminal convolution as objective. The code condition forbids self-overlap as well as pairwise overlap. Dividing the parts of degree i by qⁱ gives precisely the manuscript's arrays; only initial-part integrality is needed later to bound γ = max(a₁,b₁) ≤ 1−1/q.

2. For a cutoff h, coefficients below h in the polynomial product cancel except degrees 0 and 1. The remaining tail G has nonnegative coefficients and a positive degree-h coefficient. For h=2 this is a₁b₁; for h≥3 at least one of a₁bₕ₋₁,b₁aₕ₋₁ is positive by induction. At the first factor root σ the other factor is nonnegative, so G(σ)=σ−1>0 and G′(σ)≤1, including coincident roots. Hence h(σ−1)≤σ, and the degree-h coefficient is bounded by max(x−1)/xʰ = (1−1/h)^(h−1)/h for x>1. Both factor sums at 1 are strictly below 1. This cutoff argument is the normalized analogue of [Blackburn, Lemma 8](https://arxiv.org/html/2611.21913v1).

3. At 1, the cutoff product gives aₕ ≤ G(1) ≤ γ(1−sum_{1<=i<h} a_i), meaning γ times one minus the sum of aᵢ for 1 ≤ i < h. The analogous statement holds for b, and directly at h=1. Thus, given a terminal value 1 and all shorter positive-lag values bounded by γ, the new lag-h renewal value for either row is at most aₕ+γsum_{1<=i<h} a_i ≤ γ, and likewise for b. Convex mixtures preserve the bound. This is why the factor is γ, not γ per step, and why zero lag must retain full mass 1.

4. Take n/2<N<n. In a term with degree t≤n the two indices cannot both be at least N. Exactly one of three cases occurs: both indices below N (seed gₜ); long left index u and short right index t−u; or short left index t−u and long right index u. Substituting aᵤ=θᵤsᵤ and bᵤ=(1−θᵤ)sᵤ produces the stated triangular recursion without removing or repeating any term. The one-to-one expansion into a source followed by a strictly increasing path shows sₙ=ΣgᵤKᵤ. Each positive-lag kernel is bounded by γ via step 3; Kₙ=1. When multiplication by σⁿ is introduced, each positive-lag source gains at most σ^(n−N) relative to its original tilt. The uncontrolled direct seed gₙ must still be bounded separately.

5. Put k=n−N. For each contributing pair (i,n−i), the smaller index is at least k+1. Split the degree-n diagonal according to i≤n/2 or i>n/2; this counts a possible midpoint only once. On the first half use Uᵢ=aᵢσⁱ, Vᵢ=bᵢσⁱ and xᵢ=UᵢVₙ₋ᵢ. The corresponding total half-diagonal is X. The bounds Uⱼ,Vⱼ≤e/j for 2≤j<N give UⱼVₙ₋ᵢ≤M=2e²/[n(k+1)] for any two indices in this half. For i>j we have xᵢxⱼ=(UᵢVₙ₋ⱼ)(UⱼVₙ₋ᵢ). Charge the first ordered pair to the cutoff tail F=G(σ): both indices are below N, its degree exceeds n, and its two coordinates uniquely recover i,j even if degrees coincide. Because these charges are disjoint from the degree-n diagonal, X² ≤ M(X+2Σcharged terms) ≤ 2MF. The manuscript's weaker 3MF is therefore valid. Swapping U,V gives the same result on the other half with the strict midpoint rule. A tail can be used to bound each half separately; the proof never adds the two halves' charges and asserts they are disjoint.

6. Since F=σ−1≤1/(N−1), the direct seed is bounded after tilting by 4e/√[n(k+1)(N−1)]. Together with σᵏ≤exp(k/(N−1)) and max over x>1 of (x−1)/xⁿ, this yields the explicit uniform bound

       s_n ≤ γ exp(k/(N−1)) (1−1/n)^(n−1)/n
             + 4e / sqrt(n(k+1)(N−1)).

   With k=ceil(n^(2/3)) this yields the manuscript's one-sided absolute O(n^(−1/3)) after normalization by n. No constant in this upper estimate depends on the array or q. No uniform-in-q lower bound is inferred.

## Lower bound: conditioning, counting and uniform truncation

Choose the manuscript's k=floor(log_q n)−2, t=floor(sqrt(k)), L=k+t+2, and M=floor(qᴸ/n). The qᵗ markers 0ᵏ1v1 (|v|=t) are mutually non-overlapping including with themselves: suffixes of length at most k end nonzero; longer proper matching suffixes require a second full zero run, impossible because t<k and the separators are 1. The bounds q^(t−1)<qᴸ/n≤qᵗ imply the family fits and np→1 for p=M/qᴸ, all n→∞ at fixed q. The endpoint symbol 1 exists for every q≥2; no field or divisibility requirement enters.

Condition on a first marker and a nonzero final symbol. They involve disjoint sets of coordinates for large n and have joint probability p(1−1/q). No start in one-based positions 2,…,L can be a marker. The n−2L truly interior starts L+1,…,n−L use only unconditioned letters. Among j candidate starts, distances below L give impossible intersections; otherwise disjoint letter blocks yield pʲ. Subtracting (r−1)(L−1) from the r-th sorted start gives the exact j-fold intersection sum

    B(n,j) = binom(n−2L−(j−1)(L−1),j) p^j,

with zero for too few positions. For fixed j it tends to 1/j! because L=O(log n), np→1. The cutoff is uniform: 0≤B(n,j)≤(np)ʲ/j!≤1/j! for every j≥1 since M was rounded down. Include B(n,0)=1 and extend by zeros; exact inclusion–exclusion and dominated convergence give probability e⁻¹ of no interior marker. This also justifies the manuscript's separate odd/even Bonferroni limits.

The remaining start n−L+1 touches the nonzero terminal symbol. Its conditional marginal is p/(1−1/q), because all markers end in 1. For the extra suffix tests k<d<L, the k letters at the beginning of that suffix avoid both conditioned endpoints, so the conditional union probability is at most Lq⁻ᵏ=o(1). No independence from interior avoidance is required. The terminal nonzero symbol rules out overlaps of lengths at most k, these suffix tests rule out lengths strictly between k and L, and an overlap of length at least L but below n would force a forbidden second full marker. This checks every proper length and both distinct and identical words. The resulting lower bound is for every sufficiently large n, not a selected subsequence.

## Checks and literature scope

The accompanying standard-library Python checker [controls_2.py](controls_2.py) (SHA-256 `2686942eacab32e4ad0bdcde33fe3cf5d2b57ce3746977e373bc1e6579694e6b`) passes under `python -B -O controls_2.py`; checks are explicit and remain enabled under optimization.

* 3,831 array cases, 8,006 (array, cutoff) cases. All integer splits were enumerated for (q,n)=(2,8),(3,6),(4,5), supplemented by twelve deterministic length-15 cases at q=2,7,997. The checker propagates each single source **forward**, verifies terminal reassembly against the direct convolution and bounds each positive-lag gain. It checks the cross-pair bound at an independent exact rational tilt rather than numerically approximating a root. These are checks of identities, not a computational proof of the asymptotic statement.
* 57,900 conditioned-word cases across four experiments, with all j-fold intersection sums, last-start marginal and absence of collisions at every proper suffix length checked by enumeration:

| q | n | M | Conditioned words | Accepted |
|---|---|---|---:|---:|
| 2 | 18 | 1 | 4,096 | 1,607 |
| 2 | 18 | 2 | 8,192 | 1,528 |
| 3 | 13 | 2 | 8,748 | 6,812 |
| 4 | 12 | 3 | 36,864 | 32,472 |

The experiments use small k=2, t=1 to make exhaustive enumeration feasible. Counts are per experiment, not claims of distinct inputs across different marker families.

[Blackburn's 2026 introduction and Theorem 1](https://arxiv.org/html/2611.21913v1) explicitly ask for the binary asymptotic upper constant and prove 5/(6e). The binary value from this draft is 1/(2e); the distinct question whether the classical one-run code is exactly optimal for infinitely many lengths remains open here. The [Blackburn–Nasr Esfahani–Kreher–Stinson preprint, Theorem 35](https://arxiv.org/pdf/2211.10309) proves the classical binary subsequential lower bound. [Blackburn 2015, §3](https://arxiv.org/pdf/1303.1026) describes the fixed-q Gilbert–Levenshtein lower construction along a subsequence and gives a distinct subset-of-marker-words construction. [Chee–Kiah–Purkayastha–Wang, Theorem 4.2](https://arxiv.org/pdf/1209.0236) states a liminf but its displayed proof chooses n=ceil(cα(k)^k). A subsequence calculation alone is not sufficient for every n; the present draft gives its own all-length argument and does not rely on that implication. The bounded literature search located no matching sharp upper theorem as of the review date; that is not proof of global priority.
