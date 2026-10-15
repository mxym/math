# All-order APPT variational profile: proof obligations

Prepared before the manuscript, 14 October 2026. This continues the same
APPT entropy problem. It does not count another independent conjecture.

| Statement | Necessary bridge | Actual verification scope |
| --- | --- | --- |
| V1: every alpha>=epsilon*m and n>=m, without an upper order bound | Keep the exact finite physical peak/width coupling L7. Use an exact finite scalar profile with u_D^alpha/D as the calibrated peak. Split at peak mass comparable to the crude middle bound. In the comparable range, D is exponentially large in alpha, making all mean, trace and rank-rounding errors uniformly negligible. In the peak-dominant range use the exact u_D witness, including alpha much larger than D. | New ordinary proof only; no Lean, no added audit root. |
| V2: every alpha>0 and every n>=m, uniformly as m grows | V1 for alpha/m bounded below; uniform scalar moment-excess expansion plus G1 for diverging alpha=o(m); U2 below sqrt(m). Retain positive logarithms at vanishing excess. | New ordinary complete asymptotic profile, not an exact finite optimization theorem. |
| Finite scalar-to-physical lower bridge | For every width and mixing parameter construct I+kappa P+d vv*, with integer rank and d=2-kappa-eta_m(kappa)>=0. Apply the actual Schmidt SOS G26. Bound the omitted baseline slot and all trace errors before exponentiation. | Existing finite family reused with its full written proof; no extra claim about old formalizations. |

The proof must distinguish multiplicative moment accuracy from moment-excess
accuracy. The former suffices only when alpha/m is bounded below, where the
scalar moment is uniformly separated from one. The sublinear range requires
the latter and is handled independently. No fixed-m limit, finite exact
maximum, absolute-separability result or complete formalization is claimed.
