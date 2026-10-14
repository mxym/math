# Full Minc sixth conjecture: complete-domain obligations

Prepared before mathematical work,14 October2026. This is Conjecture6
in Minc's permanent catalogue, not a differently numbered PSD dominance
problem. For n>=2 and1<=k<=n define Lambda(n,k) as all actual binary
n-by-n matrices with every row and column sum k, and
m(n,k)=min_{A in Lambda(n,k)} per A.

The original whole domain is every fixed integer n and all degrees1..n.
The cited original wording does not specify weak versus strict decrease.
For positive complete acceptance this stage therefore targets the stronger
strict statement m(n,k+1)/(k+1)^n < m(n,k)/k^n for every n>=2,1<=k<n.
A strict reverse comparison disproves even the weak original reading;
an equality alone is not accepted as a disproof of the unambiguous weak form.

| Obligation | Full scope | Acceptance boundary |
| --- | --- | --- |
| Complete positive target | Every n>=2 and every1<=k<n, strict decrease of the global normalized minima | No selected order, sparse/dense regime, circulant class or fixed degree substitutes for all degrees. |
| Complete negative route | One n,k with a proven global next-degree lower bound exceeding a legal current-degree upper bound after normalization | Comparing two arbitrary matrices is insufficient; full exact minima or a valid universal separating lower certificate is needed. |
| Minimizer-extension sufficient route | For every actual global k-minimizer, construct one actual binary(k+1)-regular B with the normalized strict bound | An arbitrary fractional regular matrix is inadmissible. Every-extension monotonicity is already false in the2007 primary paper. |
| Possible complement averaging | Average per(A+P) over actual perfect matchings P of E-A | Exact all-order expression needs a rigorous bound; neither a uniform unrestricted permutation nor an unproved sign can replace the actual complement distribution. |
| Prior range bridge | Wanless2007 and current source list only previously solved finite/sparse/dense degree lines | Already established ranges are inputs/exclusions, not new major credit. Bregman's upper bound is a different already proved Minc statement. |
| No old route reuse | This complete binary-degree minimum sequence differs from subgroup Lieb/Marcus, Chollet and Lih-Wang | Old PSD rank/order results and permanent-on-top/Bapat-Sunder counterexamples cannot settle this object. |

Primary statement, exact reading/access limits and old-route screening are
saved in MINC_SIXTH_SOURCES.json. No full1965-paper, priority, Lean,
external peer-review or publication claim is made.
