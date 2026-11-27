# Sources, comparisons, and limits

1. Eyal Kushilevitz and Yishay Mansour, *Randomness in Private
   Computations*, SIAM J. Discrete Math. 10(4), 647–661 (1997),
   [DOI](https://doi.org/10.1137/S0895480196306130).
   Their nonexplicit \(O(t^2\log(n/t))\) one-bit bound and masked
   running-sum protocol are prior work. The present work changes
   the choice of the different sources' seed maps by placing the
   sources on a block and exploiting the number of honest sources
   and the coalition's exterior endpoints. Neither masking an XOR
   by an XOR-zero share vector nor using a running sum is new.
2. Vipul Goyal, Yuval Ishai and Yifan Song, *Tight Bounds on the
   Randomness Complexity of Secure Multiparty Computation*, CRYPTO
   2022, [ePrint 2022/799](https://eprint.iacr.org/2022/799),
   [PDF](https://eprint.iacr.org/2022/799.pdf).
   Their §2.3 gives the KM97 protocol and the fixed-tree access
   sets (Defs. 1–2); §5 and Cor. 2 give the layerwise zero-sharing
   generator; §6 Theorem 4 and Cor. 3 give the explicit addition
   protocol. Their Theorem 1 already uses the standard
   Reed–Solomon/Vandermonde construction of exact limited
   independence. The new explicit simplification is to change
   variables to prefix masks, which represent each fixed subtree
   interval with at most two endpoint variables and thus remove
   the separate seed per depth. Their §4.2 Theorem 2 is the
   quadratic lower bound, whose stated range is \(n\ge3\) and
   \(t\le n-2\); we use monotonicity at the remaining high endpoint.
3. Anna Gál and Adi Rosén, *\(\Omega(\log n)\) Lower Bounds on the
   Amount of Randomness in 2-Private Computation*, SIAM J. Comput.
   34(4), 946–959 (2005), [DOI](https://doi.org/10.1137/S0097539703432785),
   [author PDF](https://www.irif.fr/~adiro/publ/GR2.pdf).
   Theorem 1.1 applies to general protocols for \(t\ge2\);
   Definition 4.1 and Theorem 4.2 (§4, author PDF p. 12) give the stronger
   \(\Omega(t\log(n/t))\) bound for additive-message masking.
   This is the exact restricted model used in §5, not a lower bound
   for unrestricted protocols. These lower bounds and the known
   one-bit \(t=1\) protocol are not our results.
4. Geoffroy Couteau and Adi Rosén, *Random Sources in Private
   Computation*, ASIACRYPT 2022, [ePrint 2023/074](https://eprint.iacr.org/2023/074),
   [author PDF](https://www.irif.fr/~adiro/publ/CR.pdf).
   Their §5.1 states that KM already attains its upper bound with
   exactly \(t\) sources for XOR. Their analysis already distinguishes
   corrupting all sources from corrupting some deterministic
   parties (e.g. §4.2–4.3). The present novelty is the coin bound
   under that fixed source count; the fact that \(t\) sources are
   sufficient is known. We do not claim source-count optimality at
   the vacuous top-coalition boundary (e.g. a coalition of \(n-1\)
   can already infer all inputs from parity and its own inputs).
   Their nonlinear Conjecture 13, recorded as
   AICR c/0102, excludes XOR and is not addressed.
5. Hua Sun, *The Capacity of Interactive Secure Summation*,
   [arXiv:2610.29954v1](https://arxiv.org/html/2610.29954v1)
   (21 October 2026), §2, §6.1, Appendix A. The exact rate theorem
   there concerns joint coding of a long vector of sums over a
   finite field; it explicitly distinguishes the TCS count for
   one input bit per participant. No claim about that capacity
   theorem is made here. Hari Krishnan P. Anilkumar, Varun Narayanan,
   Manoj Prabhakaran and Vinod M. Prabhakaran, *Randomness in Private
   Sequential Stateless Protocols*, [ePrint 2024/1448](https://eprint.iacr.org/2024/1448),
   study a different communication/state restriction.
6. [AICR c/0087](https://aicr.info/c/0087/) gives a secondary
   transcription. Its literal question of whether there is some
   sublinear growing threshold with randomness \(\omega(t^2)\) is
   already answered by Gál–Rosén Theorem 1.1; our result is a
   different positive upper bound. It does not give the KM order
   \(O(t^2\log(n/t))\) via a polynomial-time explicit
   construction uniformly for all \(t\).

Bounded search on 2026-11-27 checked the listed original sources
and 2024–2026 follow-ups using the terms “randomness complexity,”
“t-private XOR,” “parity sharing generator,” “prefix,” “t sources,”
and the proposed \(t^2+t\log n\) rate. No matching one-bit bound
with the same quantifiers, or fixed-tree prefix construction in
this context, was located. This is not an absolute priority claim.
