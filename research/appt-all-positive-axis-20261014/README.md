# Full positive-order entropy envelope for actual fixed-local APPT states

Yongxian Zhang / South China University of Technology,14 October2026.
Ordinary written mathematics in the same APPT programme.
[Complete proof](PAPER.md), [full obligations](THEOREM_MAP.md),
[ordinary read record](MANUSCRIPT_REVIEW.json) and
[primary-source boundary](LITERATURE.md).

For every fixed actual m>=3, D=mn with n growing, the minimum Renyi entropy
on the complete actual APPT set has a single approximation uniform over
every extended real order0<=alpha<=infinity, including orders depending
on n and approaching0, crossing1, or diverging at any rate:

    |logD-min_(actual APPT)S_alpha
               -max{optimized bulk deficit B_m(alpha),exact pole deficit p_D(alpha)}|
                                            <=c_m D^(-chi_m), chi_m>0.

The manuscript gives an explicit sufficient positive exponent. It is not
asserted optimal, and no finite dimension threshold is certified. For each
fixed finite A, the stronger bounded-order result is uniform on0<=alpha<=A:

    logD-min_(actual APPT)S_alpha=B_m(alpha)+O_(m,A)(1/D).

Atalpha=1, put q=(m+1)/(m-1), t=q-1, z=q logq/t. The actual von Neumann
minimum is logD-[z-1-logz]+O_m(1/D). The scalar bulk optimization is a
credited known input; the proof supplies the full physical-set error bound.
Atalpha=0 the exact minimum is log(D-1), attained precisely at
(I-P)/(D-1), rankP=1. Atalpha=infinity the exact minimum is
log(D+2)-log3, attained precisely at(I+2P)/(D+2), rankP=1.

The central bounded-order argument uses a convex defect continuous at1,
controls multiplicative normalization even through zeros and alpha tending
to0, and transfers that bound with a uniformly bounded logarithmic derivative.
Integer-rank actual APPT projections attain the bulk to the declared error.
For unbounded orders the proof exhausts all physical spectra across complete
continuous bands, then uses the credited all-higher-order pole theorem.

The model bulk is APPT-only. No ASEP bulk envelope, growing-m uniformity,
exact finite transition optimizer, or full finite-dimensional entropy
conjecture resolution is asserted. This refinement adds no independent
major-conjecture count and does not extend any previous Lean certificate.

PAPER345 and the prewritten map21 have their own complete366-line ordinary
internal read and final literal-source binding. Earlier critical300,
sharp240 and related read scopes retain their exact boundaries. This is
AI-assisted internal scrutiny, not external human peer review or priority
certification. Source correspondence checks verify bytes/read scope/links.

Supporting finite checks retain their limited scope:

- 200 exact normalized convex-chord identities and5 known scalar purity specializations;
- 20 actual PSD rank-endpoint controls with a negative partial-transpose expectation;
- 10 sensitive cross-one continuity controls;
- 270 actual dimension/order cases and1620 evaluations of actual APPT
  mixtures of pole, projection and missing-projector families.

Orders include0, tiny positive values,1 plus or minus10^(-90),1 exactly,
finite orders, logarithmic/critical/very-high orders and infinity. They
do not exhaust all states or orders; the manuscript proves those quantifiers.
Windows standard, optimized Windows and WSL use the same260-digit implementation,
not three independent mathematical proofs. No finite threshold is inferred.

```text
python3 check_axes.py --out DIAGNOSTIC.wsl.json
python3 check_sources.py --out SOURCE_CHECK.json
```

[Source bindings](SOURCE_HASHES.json), [source check](SOURCE_CHECK.json),
[Windows](DIAGNOSTIC.windows.json), [optimized Windows](DIAGNOSTIC.windows-opt.json),
[WSL](DIAGNOSTIC.wsl.json) and [semantic comparison](DIAGNOSTIC_COMPARISON.json).

All rights reserved for original material; retain third-party notices.
No external funding. OpenAI AI assistants supported research and review;
author responsibility remains. [Author record](../../AUTHOR.md).
No new Lean execution/audit roots, external message, aiXiv submission,
Release, DOI or historical first-solution claim.
