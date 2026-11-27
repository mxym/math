# Sources and claim boundaries

1. **Question addressed.** M. Ishihara, C. Roch i Carceller,
   K. N. Wilkinson, C. A. Breum, T. Gehring, J. B. Brask,
   [Quantum randomness certification with untrusted measurements
   and few probe states, arXiv:2210.13608v3](https://arxiv.org/html/2210.13608v3);
   [Phys. Rev. A 114, 052413 (2026)](https://doi.org/10.1103/d7pg-hjgs).
   Their Appendix A.1 Eq. (13) starts with a general tripartite state;
   Eq. (14) specializes to trusted *pure* probes so that the signal
   factors out of the other two systems. Their Appendix B Eq. (41)
   bounds single-round guessing in that pure-probe model.
   §V proposes allowing Eve-correlated mixed preparations. The
   supplement gives a single-round solution for *independent*
   calibrated signals and untrusted detectors (plus the declared
   approximate-product bound). It is not a solution for all mixed
   states in their general Eq. (13), their many-outcome experimental
   rate, or sequential entropy accumulation.

2. **Known product-state modeling and neighboring entropies.**
   H. Dai, B. Chen, X. Zhang and X. Ma,
   [Intrinsic randomness under general quantum measurements](https://arxiv.org/html/2203.08624),
   [Phys. Rev. Research 5, 033081 (2023)](https://doi.org/10.1103/PhysRevResearch.5.033081),
   Eqs. (1)--(3) use a generalized Naimark dilation with a product
   state and Eve holding the purifying systems. Their quantum
   relative-entropy formulation and the local-measurement convex
   roof are distinct; the latter is not used to upper-bound joint
   reference guessing here. The product model and dilation are
   established, not new. F. Bischof, H. Kampermann and
   D. Bruß, [Measurement-device-independent randomness generation
   with arbitrary quantum states](https://arxiv.org/abs/1703.03330),
   [Phys. Rev. A 95, 062305 (2017)](https://doi.org/10.1103/PhysRevA.95.062305),
   treat a trusted source and hidden detector strategies; arbitrary signal
   dimension alone does not establish a certificate for joint quantum
   access to both purifications.

3. **Joint side information and more permissive source/device correlations.**
   G. Senno, T. Strohm and A. Acín,
   [Quantifying the intrinsic randomness of quantum measurements](https://arxiv.org/abs/2211.03581),
   [Phys. Rev. Lett. 131, 130202 (2023)](https://doi.org/10.1103/PhysRevLett.131.130202),
   distinguish classical decompositions from joint quantum side
   information; their Theorem 4 has this distinction even for a product
   marginal in the four-outcome example. Their Corollary 1 concerns
   restricting Eve to product measurement effects. The argument here keeps the entire purification and
   does not replace it by independent Eve measurements. 
   R. D'Avino, A. Mugnai, M. Navascués, A. Acín and G. Senno,
   [A semi-definite programming formulation of the device-dependent
   guessing probability, arXiv:2606.12079v1](https://arxiv.org/html/2606.12079v1),
   Theorem 1/Eq. (10) address the fully characterized model that
   permits correlated signal and detector systems. Their §IV.1 and
   §V, especially Eq. (11) and the text following Eq. (17), explicitly
   distinguish correlations of the devices from correlations to Eve.
   Their equally depolarized single-qubit scenario does not impose
   the product source/detector marginal of the present note.
   F. Curran, M. Moradi, G. Senno, M. Stobinska and A. Acín,
   [Maximal intrinsic randomness of noisy quantum measurements,
   arXiv:2506.22294v2](https://arxiv.org/html/2506.22294v2), Theorem 1
   and Appendix A, treat optimization over the input state, with a
   pure-state optimizer, and use a larger correlated model for their
   joint-noise comparison. Their unbiased qubit case overlaps the
   pure, transverse special case \(r=1\), not the independent mixed
   source data theorem. [Curran, arXiv:2601.16343v4](https://arxiv.org/html/2601.16343v4)
   mainly studies other guessing rules allowing an inconclusive outcome.

4. **Known mathematical ingredients.** C. W. Helstrom,
   [Quantum detection and estimation theory](https://doi.org/10.1016/0020-8817(69)90002-6)
   gives minimum-error binary quantum state discrimination.
   C. A. Fuchs and J. van de Graaf,
   [Cryptographic distinguishability measures for quantum-mechanical states](https://arxiv.org/abs/quant-ph/9712042)
   give the comparison \(D\le\sqrt{1-F^2}\) with root fidelity.
   R. König, R. Renner and C. Schaffner,
   [The operational meaning of min- and max-entropy](https://arxiv.org/abs/0807.1338)
   give the guessing interpretation of conditional min-entropy.
   S. Meng et al.,
   [Maximal intrinsic randomness of a quantum state,
   arXiv:2307.15708](https://arxiv.org/html/2307.15708), Theorem 1
   optimizes a trusted projective measurement for a fixed state; its
   dimension-two optimal-basis value agrees with the sharp boundary
   \(|t|=1\) here. The branch Helstrom calculation itself is
   standard; the issue is the worst-case upper bound with arbitrary
   independent detector memory consistent with only the probe data.

The bounded-effect commutator certificate, the exact two-probe mixed
qubit tradeoff/positive certification criterion, and their source-model
scope are the claims of this supplement. The fixed pure and projective limits
are not claimed new. No matching statement for the independent mixed probe tradeoff
was identified in the above primary sources. This is a limited prior-art
check, not a claim no equivalent implication exists elsewhere.
