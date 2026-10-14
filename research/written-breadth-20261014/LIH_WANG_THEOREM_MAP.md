# Full Lih-Wang conjecture: complete-domain proof obligations

Original domain: all integers n>=3, all real nonnegative doubly stochastic
n-by-n A, and every real alpha in [1/2,1]. J_n has entries 1/n.
This is the original parameter interval in the 1982 formulation as
reproduced by the 2024 published introduction, equation (3), and the
2005 primary author survey, Conjecture 34/page332; it is not a chosen band.

| Obligation | Exact full scope | Boundary |
| --- | --- | --- |
| Positive complete target | per(alpha J+(1-alpha)A)<=alpha n!/n^n+(1-alpha)per A for every original n,A,alpha | No restriction to alpha=1/2, finite orders, normality, rank, sparse mixtures or root-free polynomials. |
| Known-dimension bridge | n=3 original result and n=4 published Theorem2.1; n=1,2 are elementary if included | These are credited prior inputs, not new solved-major counts. Published Theorem2.2 does not close unrestricted n=6. |
| Whole-interval reduction | t=1-alpha in [0,1/2]; exact G=t(1-t) sum_m c_m sum_(j=0)^(m-2)t^j | Sign remains unproved on the full matrix/size domain. A midpoint proof requires a separate full-interval bridge. |
| Complete negative witness | One actual rational doubly stochastic A and rational alpha in the original interval with exact G<0 | Exact nonnegativity/margins plus independently structured matching DP and inclusion-exclusion. A single legal strict witness disproves the universal conjecture. |
| Discovery limits | Only complete proofs or legal exact negative witnesses settle L1 | Finite nonviolations and examples with alpha<1/2 do not settle it; no Lean/publication/priority claim. |

Primary statement and published restricted-result scopes are bound in
LIH_WANG_SOURCES.json. The original 1982 full text was not retrieved; no
complete original-source or historical-priority audit is claimed.
