# Two exact results on quantum randomness from informationally complete measurements

- [State-weighted attainment](state-weighted-attainment/PROOF.md): For every nonzero positive semidefinite state weight in dimension d, an explicit extremal rank-one informationally complete measurement with d² outcomes makes all weighted probabilities equal. This attains the fixed-state Rényi randomness optimum characterized by [Gutierrez Anco, Nemoz, and Brown, Theorem 4.6](https://arxiv.org/html/2410.16447v2). 
- [Qutrit SIC minimax counterexample](qutrit-sic-minimax/PROOF.md): A non-SIC unbiased qutrit MIC has a strictly smaller maximum over input states of the intrinsic conditional min-entropy than any qutrit SIC in [Curran's model, Section 7](https://arxiv.org/html/2605.18291v1#S7). This does not identify the global qutrit minimizer.

These are different optimizations: the first fixes the state and varies the measurement; the second compares measurements by optimizing over states. Each proof includes separately reproducible checks and source notes.

Run `(cd state-weighted-attainment && sh replay.sh)` and `(cd qutrit-sic-minimax && sh replay.sh)` from this archive. The SHA-256 manifest covers the 14 source files.
