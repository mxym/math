# Randomness bounds for perfect XOR without helper parties

In the standard private-channel, static semi-honest model, n players each hold one bit and all learn their XOR. This note separates three statements about that model from one exact-privacy encoding lemma:

| Quantity | Result |
|---|---|
| Worst-case fair coins, nonexplicit protocol | At most t(5t+⌈log₂n⌉+3), hence O(t²+t log n). In particular Θ(t²) is the unrestricted order when log n = O(t), using the existing Goyal–Ishai–Song lower bound. |
| Worst-case fair coins, deterministic polynomial-time protocol description | At most t min(n−1,t⌈log₂n⌉), hence O(t² log n), by endpoint masks on the Kushilevitz–Mansour chain and classical BCH columns. |
| Total Shannon entropy of input-independent independent private tapes | At least Σ from k=1 to s of max{1,(log₂(k+1)−1)/2}, where s=min(t,n−2) and n≥3. In particular Ω(t log(t+1)). The same lower bound applies to the maximum, over inputs, of expected total adaptive fair coin tosses. |
| One-bit, t-coordinate-private encoding with an arbitrary-distribution tape | Over unrestricted codeword length, the infimal tape entropy is Θ(log(t+1)); this is not a low-entropy MPC protocol. |

A further lower bound of Ω(t log n) for the specific first-t-dealer sequential template proves that the first upper bound is order-optimal **within that template** for fair coins when t≥2. The unrestricted regime where t grows but t=o(log n) is not settled here. Neither the full O(t² log(n/t)) deterministic explicit benchmark nor the full arbitrary-tape Ω(t²) question is claimed. Static perfect privacy is essential to the guarantees as stated. Neither active faults nor a real implementation is studied.

Read [PROOF.md](PROOF.md) for definitions and analytic proofs, and [SOURCES.md](SOURCES.md) for the source comparison. With Python 3 and a standard POSIX shell, run `sh replay.sh`. The checkers are finite consistency checks, not the arbitrary-parameter proof.
