# Linear-order APPT profile: proof obligations

Prepared before the manuscript, 14 October 2026. This is one continuation of
the APPT entropy direction. The objects are the actual all-unitary APPT
densities; no surrogate spectral set is substituted.

| Statement | Necessary physical/analytic bridge | Formalization status |
| --- | --- | --- |
| L1: sharp moment and entropy equivalent for every aspect and c_-m<=alpha<=c_+m | A physical clique rearrangement couples the largest paired gap to the smallest gap. The actual middle interval and its mean give a convex secant bound. Bounded critical peak mass forces exponentially large D, so the exceptional spectrum and trace error vanish. Exact finite projection/spike states attain every scalar competitor. The unbounded peak-mass range is treated separately with the exact endpoint. | New ordinary proof only; no new Lean module or audit root. |
| L2: positive orders up to Cm, uniformly over all n>=m | L1 on positive compact alpha/m intervals; the small-c limit of its scalar profile; G1 for diverging sublinear orders; U2 for the remaining orders. | New ordinary uniform-limit proof only. |
| Scalar maximization reduction and pure-bulk endpoint | Explicit derivative in the mixing parameter; compact optimization and a mean-zero two-point exponential moment. | Scalar written calculation, not a numerical optimizer certificate. |
| Finite lower family | The exact Schmidt SOS G26, with the full protection coefficient, and the elementary projection-only endpoint. | The existing finite inputs retain their stated coverage; the new optimization and limits are not certified by their old receipts. |

The written proof must retain the exact u_D endpoint in the unbounded peak-mass
estimate and may replace it by 3 only after alpha<=Cm makes alpha/D uniformly
small. It must handle zero width, the width-two boundary, integer projection
rank, r=0 limits and unbounded r separately. No unrestricted-aspect relative
theorem for alpha/m tending to infinity is claimed by this map.
