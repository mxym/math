# Sources and scope

1. **[HIKR]** Shai Halevi, Yuval Ishai, Eyal Kushilevitz, and Tal
   Rabin, *Additive Randomized Encodings and Their Applications*,
   [ePrint 2023/870](https://eprint.iacr.org/2023/870),
   [full text](https://eprint.iacr.org/2023/870.pdf), CRYPTO 2023.
   Definition 3.1 (printed p. 10) requires PPT setup, encoding
   and decoding with negligible correctness error; public
   parameters include the group. Definition 3.4 (printed
   pp. 11–12) gives a simulator the entire residual-function
   oracle and asks for TV closeness to the public parameters
   with the sum of honest encodings. These are the definitions
   used here. The open question is §1.2 (p. 7). Section 4.1,
   especially Claim 4.6, Claim 4.10 and Example 4.11, gives
   known concrete capped-sum, payload and modular multiplication
   constructions; §1.1 notes these information-theoretic
   constructions are robust. Our §4.3 shows that correctly
   disclosing just a single one-sided capped sum or modular
   product cannot be postprocessed to majority while preserving
   full privacy. This does not rule out other protocol designs.
   Lemma 4.18 and the VMP necessity in §4.2 already exclude
   perfectly private AREs for majority, so our statistical
   guarantee is not subsumed by a known perfect-privacy result.
2. **[BEGI]** Nir Bitansky, Saroja Erabelli, Rachit Garg and Yuval
   Ishai, *Shuffling Is Universal: Statistical Additive
   Randomized Encodings for All Functions*, STOC 2026,
   [DOI](https://doi.org/10.1145/3798129.3800890),
   [ePrint 2025/1442](https://eprint.iacr.org/2025/1442),
   [2026-11-17 text](https://opencryptology.org/2025/1442/versions/20261117T152235Z.pdf).
   Theorem 1.1 is the finite nonrobust feasibility result.
   Theorem 4.1 (§4.1), the direct OT instantiation (§5.3), and
   Theorem 5.3 (DRE plus bit OT, §5.2) supply the ordinary ARE
   with polynomial resources for fixed finite functions.
   The ordinary groups can be taken in explicit product
   coordinates, from bit strings and finite cyclic groups.
   §1.4 expressly re-poses the robust question for finite
   functions. The November Appendix B removes correctness
   error for the ordinary construction; it does not give
   partial-sum residual privacy. Our compiler needs only the
   older statistical correctness and has its own small
   no-good-trial error.
3. **[BF]** Sapir Bekerman Freizeit and Nir Bitansky,
   *Robust Additive Randomized Encodings With Transparent Setup*,
   [ePrint 2026/1937](https://eprint.iacr.org/2026/1937),
   [2026-11-12 version record](https://opencryptology.org/2026/1937).
   General computational RARE under subexponential iO and LWE
   in the common random string model is not the same as
   statistical RARE. Their setupless result has an honest-majority
   restriction. Here the number of parties/domains is fixed,
   but the privacy guarantee is statistical for all subsets.
4. **[IKY]** Yuval Ishai, Eyal Kushilevitz, and Sahar Alon
   Yerushalmi, *On Perfect Additive Randomized Encodings*,
   [ePrint 2026/3070](https://eprint.iacr.org/2026/3070)
   (posted 2026-11-26), [TCC 2026 DOI](https://doi.org/10.1007/978-3-032-43588-0_4).
   Compares different perfect-vs-statistical correctness/privacy
   combinations, e.g. impossibility of simultaneously perfect
   correctness and privacy for Boolean OR. It does not give
   or preclude the all-subset statistical compiler here.
5. **[OP]** Emmanuela Orsini and Arpita Patra,
   *From Degree Three to Degree Two: Statistical Randomized
   Encodings for All Functions*, [ePrint 2026/2817](https://eprint.iacr.org/2026/2817),
   [full text](https://opencryptology.org/2026/2817.pdf).
   Their statistical quadratic multiparty randomized encodings
   (§6.1) tolerate all semi-honest coalitions. They address a
   neighboring motivation in [BEGI, §1.4]; a quadratic
   evaluator map does not give independent local encodings
   joined solely by addition with [HIKR, Def. 3.4]'s simulator.
6. **Related NIMPC.** Reo Eriguchi, Kazuma Ohara, Shota Yamada
   and Koji Nuida, *Non-interactive Secure Multiparty Computation
   for Symmetric Functions, Revisited: More Efficient
   Constructions and Extensions*, [CRYPTO 2021 DOI](https://doi.org/10.1007/978-3-030-84245-1_11).
   Its abstract and model start with correlated randomness and
   separately received messages. This note does not claim the
   first secure non-interactive computation of symmetric
   functions, only the additive independent-coins subclass
   compiler under the residual condition.
7. **Balanced ARE.** Yu Wei, Jaspal Singh, Adya Agrawal and
   Vassilis Zikas, *Balanced Additive Randomized Encodings for
   Shuffle Differential Privacy*, [ePrint 2026/1239](https://eprint.iacr.org/2026/1239).
   The source explicitly targets non-robust computational
   shuffle privacy, not the statistical partial-sum simulator.
8. **Problem index.** [AICR c/0083](https://aicr.info/c/0083/)
   records the finite robust question and distinguishes it from
   the nonrobust result. This note is positive on an explicit
   subclass, not a full resolution. Its comparison proofs
   concern only the listed deterministic disclosure maps.

**Bounded literature check, 2026-11-27.** Searched variations of
“robust additive randomized encoding”, “symmetric”, “majority”,
“histogram”, “finite”, “collision masking”, and “independent
randomness”, including 2026 updates above. We found prior
non-interactive computation of symmetric functions with
correlated randomness, nonrobust statistical ARE, and general
computational robust ARE. We did not find the same
residual-histogram subclass compiler in the inspected primary
sources. No priority claim is made beyond that check.
