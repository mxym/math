# At rank 36, three pairs of types must separately cover the no-U026, no-U127 case

Suppose a rank-36 graph has neither unit U026 nor unit U127. Then **each** of the three pairs {U125,U230}, {U228,U337}, {U230,U337} must meet its support. No restriction is placed on the remaining types. Equivalently these give three necessary four-term support constraints after restoring U026 and U127 to each pair. They remove three seven-type containments but do not exclude rank 36.

Indeed the [norm-16 injection](exclusion.md) gives N16=0 from U127=0. The [nonstar transfer and exact root packing](norm18-dot8-nonstar.md) then give N18≤48,004, counting both orientations of the actual neutral vectors and without assuming N20 absent. Compare the following independently derived lower bounds for the same count, if the indicated pair is also absent:

| Extra absent pair | Exact oriented lower bound |
| --- | ---: |
| U125, U230 | 51,068 |
| U228, U337 | 50,120 |
| U230, U337 | 52,212 |

The [native checker](norm18_rank36_dot8_nonstar.py) replays three exact rational identities in the same 205 original/extension marked coordinates as the [previous comparison](norm18-rank36-dot8-star.md). In each case it proves `B(N18−48004)≥L` after the stated zero substitutions, with (B,L) respectively (36,110260), (1671996,3535285356), (27328116,114947163360). The constant 48,004 here is simply a convenient baseline in the identities; they do not take any graph upper bound on N18 as an input. The positive remainders are displayed completely in the checker. Rounding up to the next even actual count gives the table.

The first row uses the [actual paired-square cap](active-square-eight-all.md) and [U121≤29,372](u226-global-pressure.md). The last two use nonnegative raw populations, compatible-minus-original counts and original edge marks, the norm-16 lift, and the independently proved [absence of all rank-36 Fano fields](../rank36-no-fano.md), so −G014=0. These last rows do not assume corresponding Fano absence at any other rank. All selected unit populations are nonisotropic with p=2402; in particular the hot entries in the checker are normalized V, whereas its `N((0,18))` is the actual oriented population. Run `python norm18_rank36_dot8_nonstar.py` alongside the public native chart files.
