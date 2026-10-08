# Scoped editorial revision of the frozen candidate series, 8 October 2026

The original candidate snapshots remain unchanged. This directory contains only the two scoped wording corrections requested after the independent report; the corrected wording awaits limited recheck, and no publication has been performed. All constructions use exact integer digit positions for rational parameters.

1. `../round8_pinned_traintrack_repair_20261008/TRAINTRACK_POSITIVE_REPAIR.md`
   Fixed positive repair of the exact old nested counterexample; all-pin attained critical L^q index for 1<alpha<4/3; weighted nonuniform-template sufficient condition. SHA-256 aa85b4e46f8752754ce187d8413d200763d87639997f73b0782f874eefb79f81.

2. `../round8_pinned_phase_diagram_20261008/FULL_PHASE_DIAGRAM_AND_INTERVALS.md`
   Full rational-alpha range (1,2), L^2 endpoint at alpha=4/3, continuous bounded original density at alpha=3/2, and actual uniformly positive-length distance intervals at every pin for every alpha>1. SHA-256 d6276d83c9d228bf6baabf160a20493440f7e6e3e72f6db9081053bf558fe4b9.

3. `../round8_pinned_fixed_ratio_20261008/FIXED_RATIO_ENDPOINT_SWITCH.md`
   Real fixed-ratio stage growth; exact packing dimension; shifted finite critical L^q exponent with endpoint failure; continuous bounded regime above its shifted threshold. SHA-256 4ab70460deb7c4cce215ab442b2590017001dfbb3ffc4952c5ab81787eef3505.

4. `EXACT_PIN_STRATA_AND_BOUNDARY.md`
   Exact original-law exceptional pin sets inside the separated rectangle, their Hausdorff/packing dimensions, noncontinuity at the fixed-ratio D_K=0 boundary, and O(log q) moment-norm upper bounds (with no matching lower bound) and double-exponential upper tails there. SHA-256 6aa50a1fea9b49fa1b9e9471f261b1fa996b37c6061e9a2f2bedcc3c097a6f05.

The remaining sharp question identified by this series is L-infinity membership at D_K=0 on the horizontal Cantor curtain. The present proofs give an O(log q) upper bound for every finite L^q norm, with no matching lower bound, and exclude a continuous density, but do not decide boundedness.

The sharpness statements concern the natural distance probability's density, not failure of positive-measure distance sets. Every pin in the studied rectangle has an interval in its actual distance set.

`check_phase_identities.py` and `phase_identity_checks.json` corroborate exact rational exponents, real finite digit counts, and the three earlier frozen hashes. They are not an independent analytical audit.
