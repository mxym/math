# Full von Neumann upper bound and saturation rigidity

## Exact verified statements

For arbitrary actual APPT density matrices on C^m tensor C^n along m->infinity, n/m->gamma<infinity, put D=mn and K=max(8,4+gamma). The physical von Neumann deficit is log D plus the sum of lambda log lambda over the canonical ordered spectrum, with zero eigenvalues included through 0 log 0=0.

`appt_vonNeumann_fixed_aspect_upper` proves the unrestricted eventual bound D(log D-S(A))<=K/2+epsilon for every epsilon>0. No flatness or supplied spectral constraint occurs in this final hypothesis.

`appt_full_entropy_head_saturation` connects saturation of the FULL entropy coefficient to the actual entropy-head deficit tending to zero. `appt_full_entropy_saturation_flat` consequently controls every normalized eigenvalue D lambda_i uniformly. The final `appt_entropy_saturation_iff_flat_purity` proves the equivalence between full entropy coefficient saturation and simultaneous purity coefficient saturation plus uniform spectral flatness. This is a characterization of saturation, NOT an existence proof of a saturating family or a complete evaluation of the minimum entropy.

## Independent mathematical reading

The retained triangular graph budget leaves the first-row energy intact. Ordered graph ranks compare that row with the largest actual paired gaps; no arbitrary incompatible eigenvalue labels or low-level spectrum ansatz are assumed. The physical cut/witness and original quantum purity are connected internally. After division by the exact positive paper pivot, the head's quadratic correction combines with the true logarithm estimate; the extra negative square is dropped only with its proved favorable sign.

The entire ordered spectrum is split into the first m-1, last m, and all remaining coordinates. The Taylor estimate is applied ONLY to the remaining coordinates and the scalar normalization error; zero and fixed-height outliers stay in the nonlinear head. Exact entropy and quadratic centering identities retain both the reference-pivot error and the subtracted trace-centering remainder. A two-sided quantile estimate controls the pivot in both directions. In this recovered checkpoint its bound has aspect-ratio dependence, so the final upper theorem only asserts fixed finite aspect ratio.

The parameter-dependent radii and error converge without referring to an optimizing spectrum. Saturation of the full objective then forces the head deficit to zero, invoking the already verified physical stability theorem. Finally, a separate local quadratic entropy/purity comparison proves the converse on uniformly flat spectra. Actual matrix dimensions may vary; no false common ambient Hilbert space is required.

## Verification and recovery

The 17 added mathematical modules were read from the exact source on the unmerged branch. The successful committed source d2a9ff63afb0e3134233d7df345baa9013f5c4ed was independently rebuilt in run 38536151448: 2864 build tasks, 41806 transitive declarations and 53 roots at trust level zero, only propext/Classical.choice/Quot.sound. All 75 input hashes and uploaded sources were checked against the commit. The downloaded complete kernel log agrees byte-for-byte with the existing local successful log (SHA-256 6ded78d608ce0fbeade7c808f4947507a9b7cceb269245100f4cb47474ac3b3c). Seven unchanged-type forged-proof controls were rejected after the original closure passed.

The earlier runs 38533187373 and 38534123326 failed at the multiline run_cmd audit wrapper. Their mathematical builds passed, but the primary replay did not run; later individual rejection controls did not validate those failed workflows. The explicit parenthesized application fixes the parsing error. Both original failure records are retained separately, not relabeled as success. This continuation recovered, checked and integrated existing verified work rather than claiming all recovered lemmas were newly authored this round.

Run `python3 reproduce_entropy_global.py --check-only` and `python3 reproduce_entropy_global.py --fresh` with the pinned Lean 4.34.1 and Mathlib checkout. The selected closure is independent of the older purity audit: no original quantum definition, old proof, source manifest or immutable Release is changed. Full entropy attainment, fixed-m/all-total-dimension entropy laws and the other Renyi orders remain separate obligations.
