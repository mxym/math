# Which sites change in an optimal binomial count basis?

**Yongxian Zhang.** AI-assisted research note; independent internal AI review, not external peer review. No assertion of worldwide priority.

When the common mean of k-wise independent bits varies, an optimal support for their count can change at particular parameter values. Knowing that each adjacent pair moves by at most one does **not** say which individual sites leave: neighboring pairs might cancel each other's changes.

For even 2≤k≤n−2, **every departing site t is replaced by t+2**, with no such cancellation. This includes simultaneous moves (Berend–Ernst–Kontorovich–Kumar, Conjecture 5.5). The number of positive-length phases is one plus k(n−k)/2, minus the sum of the excess multiplicities of simultaneous transitions. At the boundary k=n−1, a single site instead moves from 0 to n−1 at p=1/2. We make no statement about the frequency or general rationality of exceptional parameters.

[Proof and boundary case](MOVES.md) · [Original problem and related work](SOURCES.md) · [Independent internal review](REVIEW.md).

The [previous phase-order result](../k-wise-binomial-optimal-bases/PROOF.md) supplies chronology and the local tilings. The new ingredient is a real-rooted polynomial from the finite-difference moment nullspace. Between its roots, the logarithm of its modulus minus a linear function is strictly concave; this rules out long or contiguous contacts.

To reproduce the finite checks, run `sha256sum -c SHA256SUMS` and `python3 -I -B -O check.py` and compare to [CHECKS.txt](CHECKS.txt). All 312 transitions for n≤13 in the proper range are checked by exact integer/rational arithmetic. Completeness of the finite replay uses the previously proved strict increase of the integer sum of pair starts and connectedness, *not* the new +2 rule. Separate checks cover boundary cases and three larger simultaneous moves. The general proof is analytic.
