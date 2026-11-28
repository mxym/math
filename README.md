# Sharp Smale mean value bound for real sextics at real basepoints

Sharp bound 5/6 with equality classification for real sextics at real noncritical basepoints, with no restriction on the locations of critical points. The general complex sextic problem is not covered.

Read FactorSmaleRealSexticSharp.md and its supporting FactorSmaleSexticLocalExclusion.md. Run `python3 verify_smale_sextic_local.py`, then run `node verify_smale_real_sextic.js Infinity j` separately for j=0,1,2,3. The independent symbolic and rational verification is `python3 verify_smale_real_sextic_independent.py` (requires SymPy and Node.js). The largest shard may take over ten minutes.

Pinned research commit: 0b0c0574bd610acc3b78b5427fee3391b1ecfe31.
