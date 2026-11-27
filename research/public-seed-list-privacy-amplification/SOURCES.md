# Sources and scope of the comparison

1. Prateek P. Kulkarni, *One Key Good, L Keys Better: List Decoding
   Meets Quantum Privacy Amplification*, [arXiv:2603.18097](https://arxiv.org/abs/2603.18097),
   [v1 full text](https://arxiv.org/html/2603.18097v1), submitted 18 March
   2026. Definition 6 (§3, rendered lines 209–215) specifies independently
   uniform honest strings and off-list values disclosed to the adversary.
   Definition 8 (§3, 219–223) does not display a hash-seed register.
   Theorem 10 (§4, 230–268) imposes independent strongly two-universal
   seeds and an independently uniform index; its Hybrid 0 (238) averages
   the seeds without retaining their register. The public-seed
   interpretation used for the comparison is explicit in the proof of
   Theorem 12 (§5, 282–304, in particular 297). Remark 9 (§3, 224–226)
   and §6.3 describe communicating the chosen index by authentication.
   The seed-omitted joint state and the public-seed joint state are not
   the same ideal-state comparison. The quantitative counterexample
   tests the independently uniform honest-list marginal common to either
   reading of the off-list copy notation; the positive post-processing
   statement uses consistently copied keys. It makes no protocol-level
   claim.
2. Renato Renner and Robert König, *Universally Composable Privacy
   Amplification Against Quantum Adversaries*,
   [arXiv:quant-ph/0403133](https://arxiv.org/abs/quant-ph/0403133);
   Marco Tomamichel, Christian Schaffner, Adam Smith, and Renato Renner,
   *Leftover Hashing Against Quantum Side Information*,
   [arXiv:1002.2436](https://arxiv.org/pdf/1002.2436), in particular the
   fixed-side collision argument leading to the ordinary two-universal
   bound, and Eq. (8) for its familiar min-entropy form. Concatenation
   here is an application of ordinary quantum leftover hashing, not
   a new leftover-hash method.
3. Robert König, Renato Renner, and Christian Schaffner, *The Operational
   Meaning of Min- and Max-Entropy*,
   [arXiv:0807.1338](https://arxiv.org/abs/0807.1338), Theorem 1:
   classical-input conditional min-entropy is the negative base-two
   logarithm of optimal guessing probability.
4. Koenraad M. R. Audenaert, *Telescopic Relative Entropy*,
   [arXiv:1102.3040](https://arxiv.org/pdf/1102.3040), §4,
   Theorem 4, Eq. (19), and Corollary 1, Eq. (20): the telescopic
   relative entropy and its upper bound in terms of trace distance.
   The differentiated-log proof and its one-pair inequality are
   established results. Our use sets the comparison state to uniform
   key times the true side marginal, applies the bound to every
   selected-key conditional ideal, then couples them by the entropy
   chain rule and strong subadditivity.
5. Elliott H. Lieb and Mary Beth Ruskai, *Proof of the Strong Subadditivity
   of Quantum-Mechanical Entropy*, J. Math. Phys. 14, 1938–1941 (1973),
   [DOI 10.1063/1.1666274](https://doi.org/10.1063/1.1666274).
   Ueli Maurer and Renato Renner, *Abstract Cryptography*, ICS 2011,
   [primary text](https://crypto-test.ethz.ch/publications/files/MauRen11.pdf),
   and Christopher Portmann and Renato Renner, *Security in Quantum
   Cryptography*, [arXiv:2102.00021](https://arxiv.org/abs/2102.00021):
   an authenticated channel is not a confidentiality resource.
6. Ke Li, Yongsheng Yao, and Masahito Hayashi, *Tight Exponential
   Analysis for Smoothing the Max-Relative Entropy and for Quantum
   Privacy Amplification*, [arXiv:2111.01075](https://arxiv.org/abs/2111.01075),
   and Yu-Chen Shen, Li Gao, and Hao-Chung Cheng, *Strong Converse for
   Privacy Amplification against Quantum Side Information*,
   [arXiv:2202.10263](https://arxiv.org/abs/2202.10263): related
   single-output entropy guarantees/converses. They do not replace
   the three separate ideal-state comparisons made here.

## Bounded duplicate check

Checked 27 November 2026: the unversioned arXiv entry and full-text
version history return v1 only. Searches on the exact title,
arXiv ID, author plus "list privacy amplification", and combinations
including "public seed", "off-list", "entropy budget", "correction",
"entropy sharing", "conditional trace distance", and "telescopic
relative entropy" did not locate a superseding version or a published
matching result for the full disclosed-complement list model.
This is a bounded search, not a claim of absolute priority. The
ingredients (ordinary quantum leftover hashing, telescopic relative
entropy, the entropy chain rule and strong subadditivity) are
standard. The contribution is the exact model separation, the
sharp unequal-length entropy budget for this combination of
conditional ideal states, and its application to the cited proof
model. No claim is made about the physical protocol, a software
implementation, or unrelated notions of list-based extraction.

The self-contained proof does not depend on the reproducibility
scripts. Both scripts have no external inputs: the first
checks finite classical states with exact rational arithmetic
and the second implements independent real-symmetric qubit
block calculations. Neither reads paper data or performs
any network operations.
