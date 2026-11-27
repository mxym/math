# Sources and scope

1. **[BCGIKRS]** Elette Boyle, Geoffroy Couteau, Niv Gilboa, Yuval
   Ishai, Lisa Kohl, Nicolas Resch, Peter Scholl,
   *Correlated Pseudorandomness from Expand-Accumulate Codes*,
   [ePrint 2022/1014](https://eprint.iacr.org/2022/1014);
   [2023-03-31 manuscript](https://eprint.iacr.org/2022/1014.pdf)
   and CRYPTO 2022. Section 2.2 p. 8 defines the uniform-nonzero
   Bernoulli notation; Definition 3.2 pp. 14–15 is the independent
   Bernoulli row ensemble. Lemma 3.9 gives the binary walk upper
   bound. Theorem 3.10, printed pp. 18–20, gives the binary
   failure bound \(2\rho N^{-2C\beta^2+2}\) in (5). For the
   preceding union estimate we use the proof's (7), which
   explicitly includes the factor \(N\beta^2\), rather than
   the rendering of (2) in the theorem/problem-index summary. The
   arbitrary-rings discussion in §3.4 pp. 21–22 conjectures that
   the distance does not degrade; it does not explicitly fix a
   growing-ring asymptotic convention. Its earlier definitions
   use all nonzero elements, not only units. Our counterexample
   to the unchanged numerical failure bound is a fixed ring.
2. **[AICR c/0086]** [Minimum Distance of Expand-Accumulate Codes
   over Arbitrary Rings](https://aicr.info/c/0086/). The index makes
   the specific statement that the binary theorem should hold
   over an arbitrary ring under the same conditions and with at
   least the same probability. Section 5 of our proof refutes
   that quantitative statement, but also proves the qualitative
   constant-rate distance guarantee over every fixed finite
   commutative ring under those conditions. It addresses neither
   all noncommutative rings nor a rate formula for other ensembles.
3. **[Rin26]** Peter Rindal, *Expander-Based Codes at the
   Gilbert–Varshamov Bound*, [ePrint 2026/2315](https://eprint.iacr.org/2026/2315),
   [public CC BY manuscript](https://opencryptology.org/2026/2315.pdf).
   Lemma 4.2 and Theorem 4.3 already give the binary small-activation
   upper-bound exponent and strict high-probability regime.
   Lemma 7.3, especially (102)–(105), gives exactly the same
   sparse constant per nonzero increment:
   \(I_{q,\delta}=J_q(\delta)/(1-1/q)\). Theorem 7.4 already
   proves the fixed-field Bernoulli \(o(1)\) result when
   \(C I_{q,\delta}>1\) and below the \(q\)-ary GV cutoff.
   Theorem 7.5 and Corollary 7.6 give tunable inverse-polynomial
   and negligible upper failure bounds with a vanishing
   gap to GV. In particular neither the field upper threshold,
   the two-state transfer, nor a three-regime union are claimed
   new here. We keep a self-contained proof to obtain the
   matching probability exponent, the equality case of the
   sparse threshold, and the stated fixed-ring consequence.
4. **[BDW26]** Alexander R. Block, Himanshu Dongre, Hendrik Waldner,
   *Concrete Minimum Distance Bounds of Accumulate Codes over any
   Fixed Finite Field*, [ePrint 2026/2712](https://eprint.iacr.org/2026/2712),
   [public CC BY manuscript, November 11 revision](https://opencryptology.org/2026/2712/versions/20261111T064721Z.pdf).
   Theorem 1.4 gives finite-length bounds for the same Bernoulli
   expansion over fixed \(q\ge3\) fields. Corollary 1.5(3) and §4.3
   give the logarithmic-degree failure upper estimate
   \(N^{1-C(1-\Lambda_{q,\delta})+o(1)}\) in the stated
   \(\delta=O(q^{-\rho})\) regime, with
   \(\Lambda_{q,\delta}=2\sqrt{\delta/(q-1)}
       +(1-1/(q-1))\delta\).
   This is an upper bound, and does not give a matching exponent
   or the critical-line result. It differs from the exact
   field constant \(I_{q,\delta}\) by using
   \(\sqrt{\delta}\) in place of \(\sqrt{\delta(1-\delta)}\).
   No new practical finite-length bound or improvement over
   their numerical certificates is claimed.
5. **[Kha26]** Majid Khabbazian, *Linear Distance for
   Fixed-Row-Weight Expand--Accumulate Codes over Arbitrary Fields*,
   [ePrint 2026/1753](https://eprint.iacr.org/2026/1753).
   The fixed-row-weight field-uniform linear distance result
   and its terminal-boundary obstruction are for a different
   sampling ensemble. See also Chongrong Li et al., *EA Codes
   Approaching Singleton Bound*, [ePrint 2026/1782](https://eprint.iacr.org/2026/1782),
   for exact-weight field results, and Block et al.,
   *Field-Agnostic SNARKs from Expand-Accumulate Codes*,
   [ePrint 2024/1871](https://eprint.iacr.org/2024/1871),
   for the earlier field-agnostic coding analysis. We do not
   extend any fixed-row-weight or recursive multilayer ensemble.
6. **Algebraic and probabilistic tools.** The CRT minimum over
   local factors and the use of a code's socle for distance are
   classical. For examples, see Guenda and Gulliver,
   *MDS and self-dual codes over rings*, Finite Fields Appl.
   18 (2012), 1061–1075, [author preprint](https://arxiv.org/abs/1207.3384),
   Proposition 2.3 (chain rings) and
   Theorem 3.1(iii)–(iv) (CRT decomposition), and Martínez-Moro
   and Rúa, *Multivariable codes over finite chain rings:
   semisimple codes*, [arXiv:math/0505491](https://arxiv.org/abs/math/0505491),
   §3.3. The note proves the matrix-margin identity directly
   for clarity (including arbitrary finite commutative local
   rings and noninjective generators) and only claims the
   stochastic application and precise comparison. The critical
   CLT uses the classical mgf theorem of J. H. Curtiss,
   [*A Note on the Theory of Moment Generating Functions*](https://doi.org/10.1214/aoms/1177731541),
   Ann. Math. Statist. 13(4), 430–433 (1942). The exponential
   tilt and two-state occupation rate themselves are standard
   probabilistic techniques.

**Bounded literature check, 2026-11-27.** Search phrases included
“Bernoulli expand-accumulate Gilbert–Varshamov”, “Bernoulli EA
sharp failure exponent critical”, “expand-accumulate arbitrary
ring residue field Z4”, and the original ePrint number paired
with arbitrary rings and 2026. The fixed-field upper result
and its sparse constant are directly present in [Rin26]. No
inspected primary source gave the matching logarithmic failure
exponent and critical-line result for this Bernoulli ensemble,
or the fixed \(\mathbb Z/4\) refutation of the unchanged binary
probability. This is a targeted comparison, not a priority
claim beyond the inspected sources. No external data or code
is needed for the replay.
