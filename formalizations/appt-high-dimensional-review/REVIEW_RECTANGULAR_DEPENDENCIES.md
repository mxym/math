# Rectangular optimization dependencies: verified checkpoint

This checkpoint is partial verification of the unrestricted rectangular maximum. It does not claim that the complete rectangular upper bound or its equality classification has been established.

## Closed mathematical dependencies

`plateauScaledPurity_ceiling_unique` proves that ceil((m-1)n/2) is the unique integer maximizing rank of the projection-plateau objective, including odd parity. `exists_projection_family_unique_rank_max` states actual density, all-unitary APPT, attainment, and equality exactly at that rank for the entire physical projection family. It is not an upper bound on arbitrary APPT states.

`convex_mem_of_signed_balance` gives an explicit finite mass-transport decomposition of a simplex intersected with one halfspace. `ordered_prefix_expansion` proves the exact gap-coordinate expansion of any ordered spectrum. `ordered_spectrum_cut_bound` combines them into an unrestricted reduction to surviving prefixes and crossing edges, without enumerating a bounded number of dimensions or assuming a low-level spectral ansatz. Its vertex-bound premises remain explicit mathematical obligations.

`cutEdgePurity_quadratic` uses x=s/[hL+(h+i)s] to turn the rational crossing-edge purity into 1/L-(h/L)x+[i(L-h-i)/L]x^2. With h+i<=L, convexity yields the endpoint bound for every possible shortened support. The denominators, signs and cardinalities are proved rather than delegated to numerical tests.

The regression roots reject dropping the linear cut, dropping convexity, and choosing the floor in an odd case. For m=4,n=5, the exact scaled improvement of rank eight over rank seven is 5/494209.

## Local audit and exact source binding

A fresh WSL review-package Lake build completed 2,851 tasks. The empty kernel at trust level zero replayed 42,585 transitive declarations and 229 explicit roots; its only axioms were propext, Classical.choice, and Quot.sound. The main proof-corruption control targeted the actual projection-family maximum theorem. A separate control checked 6,292 type/proof dependencies and rejected a forged proof of the arbitrary-spectrum cut reduction. Earlier physical corruption controls remain present.

All 90 input files are bound by SOURCE_HASHES.json, SHA-256 f4208a1fb95ea716665a0d29b80efac60a22c0f30ca3219973ee34433482f73f. The Windows-to-VPS transport payload was checked against SHA-256 fe93b978e2316f65bccdbef80244d1f5261a3dcd08787e0dc2406bf402d4a8ef; the reconstructed complete source manifest matches the locally audited manifest exactly. Independent run 38211631460 now passed the same complete build and trust-zero replay. Its actual root list contains 229 entries; these metadata counts are taken from the retained files rather than the earlier working-note transcription. Source-bound evidence is in verification/ci-8a0ec9ba/.

## Remaining scope

The final closed-form upper bound must still be assembled for the actual APPT cut, compared against the integer plateau at the stated dimension cutoff, and combined with equality analysis. Growing-dimension multiscale lower limits, complete entropy extrema, and outlier/phase rigidity remain separate obligations. No existing release or publication tree is changed by this checkpoint.
