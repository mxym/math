# Source problem, known case, and nearby boundaries

1. Himanshu Badhani and Siddhartha Das,
   *Conditional channel entropy sets fundamental limits on
   thermodynamic quantum information processing*,
   [arXiv:2604.01217v2](https://arxiv.org/html/2604.01217v2).
   Eqs. (66)–(70) give the normalized and unnormalized
   Choi optimizations; Proposition 1, Eq. (71), gives
   the upper bound compared here. The pure unitary Choi
   state entropy and its square-root optimizer are known
   in Eqs. (150) and (167)–(168). Proposition 10 proves
   equality for a **unitary** with \(|B'|=|B|=2\);
   Appendix D Lemma 9 supplies the Bell-diagonal
   argument. The conjecture immediately after Proposition
   10 asks for the extension to a unitary mixed with
   global white noise in the conditioning-qubit setting.
   The random-channel example accompanying Figure 3
   already records numerical failure for general
   channels. Proposition 9 discusses closely related
   controlled unitaries with the other specified control
   convention. We supply a criterion for global white
   noise in arbitrary conditioning dimension, and novel
   results only beyond the known white-noisy qubit family.
2. TrureTuring's
   [Badhani–Das noisy-unitary problem dossier](https://www.trureturing.org/research/badhani-das-2026-noisy-unitary-conditional-min-entropy/),
   section “What the settlement shows,” records Lean
   theorem
   \(\texttt{D5.S3.Quantum.Information.BadhaniDasNoisyUnitary.result}\)
   for **all** \(d\ge1\), \(m=2\), unitaries and global
   white-noise proportions \(p\in[0,1]\). It links a
   [pinned proof snapshot](https://github.com/the-omega-institute/trureturing/blob/687878cf845802aba2692eeb304cb960d1306431/D5/S3/Quantum/Information/BadhaniDasNoisyUnitary.result.lean).
   We do not claim first proof of this known scope, and
   our plain derivation does not rely on Lean or on
   assertions about its audit status. The same dossier
   distinguishes its numerical evidence from exact
   results for nonwhite noise. Its 60:40 mixtures entry
   references reported failures and says the pin-tested
   script did not reproduce that case. The exact two-gate
   family here addresses that distinct extension.
   The dossier also lists B-only depolarization.
   Our local-noise result is explicitly for composition
   on the conditioning input or output, and does not
   identify this with every possible interpretation of
   the dossier's short label.
3. Gilad Gour and Mark M. Wilde,
   *Entropy of a quantum channel*,
   [arXiv:1808.06980](https://arxiv.org/abs/1808.06980),
   for the underlying normalized Choi/channel entropy
   framework; the precise bipartite condition used here
   is that of Badhani–Das. Gilad Gour,
   *Comparison of Quantum Channels by Superchannels*,
   [arXiv:1808.02607](https://arxiv.org/abs/1808.02607),
   is the work cited by Badhani–Das for channel
   max-divergence/Choi dominance.

A bounded duplicate search on 27 November 2026 checked
the current source arXiv version, the TrureTuring scope
and its follow-ups, and combinations of “Badhani–Das”,
“conditional channel min-entropy”, “mixed unitary”,
“controlled Z”, “white noise”, and “Choi marginal”.
It did not locate the same two-unitary analytic family
or the local-composition proof. The qubit global-white
noise theorem is explicitly **not new**. The results do
not establish a classification of all mixed-unitary
channels or replace the source's operational framework.
