# Primary sources, exact missing conditions, and scope

1. Kriss Gutierrez Anco, Tristan Nemoz, and Peter Brown,
   *How much secure randomness is in a quantum state?*
   [arXiv:2410.16447v2](https://arxiv.org/html/2410.16447v2).
   Theorem 4.6, Eqs. (45)–(48), and Appendix Theorem B.4,
   Eqs. (107)–(110), compute the supremal sandwiched Rényi
   values and characterize equality among extremal rank-one
   POVMs. For the up-arrow attainment we use Eq. (68), the
   comparison inequality only in (71), and the lower bound
   (73). The classical upper-bound entropy has order
   \(2-1/\alpha\) when (68) is applied at that order. This
   distinction disappears exactly at the uniform law used in
   the construction. The order comparison is also stated in
   Corollary 4 of Tomamichel, Berta and Hayashi,
   [arXiv:1311.3887](https://arxiv.org/abs/1311.3887).
   The paragraphs between Theorem 4.6 and Example 4.7
   say explicitly that the proof does not establish general
   attainment. Example 4.7 constructs exact qubit optimizers.
   Lemma 4.5/B.3 supplies the reduction from device-side
   extensions to the purifying-side calculation for extremal
   rank-one effects. We supply a POVM satisfying the
   prescribed equality weights in any dimension, not the
   entropy formulas or the dilation reduction themselves.
2. Fionnuala Curran, *Quantum randomness beyond projective
   measurements*, [arXiv:2605.18291v1](https://arxiv.org/html/2605.18291v1).
   See Eq. (5) for the fixed-state guessing bound, §3 Eq. (13)
   for weighted equality on an isotropically noisy state,
   and §7 for the existing SIC-dependent general-dimensional
   attainment. Our construction includes the pure and
   isotropically noisy cases without assuming any SIC. Its
   unbiased specialization approximates the pure maximum
   in all dimensions, the property of the low-dimensional
   families discussed in §6; no claim is made to their
   scissors geometry, SIC limit, or Zauner's conjecture.
3. Shubhayan Sarkar, Jakub J. Borkała, Chellasamy Jebarathinam,
   Owidiusz Makuta, Debashis Saha, and Remigiusz Augusiak,
   *Self-testing of any pure entangled state with minimal
   number of measurements and optimal randomness
   certification in one-sided device-independent scenario*,
   [arXiv:2110.15176v3](https://arxiv.org/html/2110.15176v3).
   Theorems 2–3 and Eqs. (12)–(14) already reduce the
   one-sided certification to a \(d^2\)-outcome rank-one
   extremal POVM unbiased with respect to the given reduced
   density operator. The condition is explicit; the
   outlook asks for such effects at arbitrary partial
   entanglement. The paper provides examples for maximally
   entangled states and some partially entangled \(d=3,\ldots,6\)
   cases, not the full spectrum. The scope here is **full
   Schmidt rank** by the discussion after its Eq. (5), and
   retains the trusted-side and exact-statistics assumptions
   of the original steering result. We do not claim a new
   test. The separate fully device-independent qutrit work
   [arXiv:2201.08649](https://arxiv.org/abs/2201.08649)
   is not required for this corollary.
4. Giacomo Mauro D'Ariano, Paoloplacido Lo Presti, and
   Paolo Perinotti, *Classical randomness in quantum
   measurements*,
   [arXiv:quant-ph/0408115](https://arxiv.org/abs/quant-ph/0408115).
   Rank-one informational completeness, extremality, and
   all-dimensional existence without a specified balance
   constraint are established prior results. Máté Farkas,
   Jurij Volčič, Sigurd A. L. Storgaard, Ranyiliu Chen, and
   Laura Mančinska, *Maximal device-independent randomness
   in every dimension*,
   [arXiv:2409.18916v2](https://arxiv.org/html/2409.18916v2),
   Appendix B and Appendix G.1, give equal-trace balanced
   IC-POVMs and a separate fully device-independent
   certification result. Those exist independently of SICs
   but do not, as a construction, balance the effects for
   any prescribed nonuniform state spectrum. This paper's
   certified randomness in an entangled Bell experiment
   is a different question from minimizing guessing with
   the source purification held by side information.

## Bounded duplicate search

On 27 November 2026, checked the current arXiv versions of
the cited works and searched their exact titles/IDs, recent
papers citing the fixed-state optimization, and combinations
of “extremal POVM”, “informationally complete”, “prescribed
state”, “uniform outcomes”, “Schmidt spectrum”, and
“attainment”. Closest primary results are those above; the
search did not locate the same explicit weighted construction
for arbitrary spectra or a result matching the fixed-state
attainment for all spectra and all dimensions. No absolute
priority claim is made. Modern SIC results, whether or not
they apply in a given dimension, are not an input to the
proof. The distinguishing condition is state-weighted
balance, not merely a rank-one IC measurement or the
balanced maximally mixed case.
