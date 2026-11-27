# Noisy forward control for equal-dimension stabilizer helper recovery

A blind stabilizer helper normally sends a classical measurement outcome to a
target shareholder. This note asks what remains recoverable when that one
forward message crosses one use of a known noisy classical channel.

For the prime-p, equal secret/target-dimension setting of the
[exact noiseless theorem](../stabilizer-helper-fidelity/), let m ≥ 1 be the
number of secret and target qudits, let d = p^m, and let 2r be the rank of the
target symplectic defect. Put

    N = p^(2m-r).

For a finite channel W(z|x), define

    C(W)   = sum_z max_x W(z|x),
    C_N(W) = max over S subset X, |S| ≤ N, of
             sum_z max over x in S of W(z|x).

The optimal entanglement fidelity F*_W obeys the computable sandwich

    C_N(W)/d^2 ≤ F*_W ≤ min(C(W),N)/d^2.

Both sides coincide whenever C_N(W) = min(C(W),N). In particular:

* if the defect vanishes (r = 0), the exact value for every finite channel is
  F*_W = C_N(W)/N;
* an N-ary erasure channel with erasure probability eta has
  F*_W = (1-eta)p^(-r) + eta/d^2;
* for N ≥ 2 and 0 ≤ eta ≤ 1, an N-ary symmetric channel has
  F*_W = p^(-r) max(1-eta, eta/(N-1));
* a noiseless alphabet of size L gives
  F*_W = min(p^(-r), L/d^2), recovering the earlier theorem.

The coefficient C(W) is the exponential of the channel's maximal leakage.
Here it is used only as a one-shot reliability quantity, not as a claim about
the secrecy of a noisy link.

The result assumes one use of a finite memoryless classical channel, exact
single-region erasure correction, a prime qudit dimension, a target of exactly
the secret dimension, no feedback, no access to the unavailable shares, and no
additional shared entanglement. For nonzero defect and a completely arbitrary
channel the displayed bounds are not asserted equal.

See [proof](PROOF.md), [sources](SOURCES.md), and the deterministic
[replay log](RESULTS.txt).
