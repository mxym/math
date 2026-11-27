# Sources and bounded prior-art check

1. **[BHIRW]** Nir Bitansky, Prahladh Harsha, Yuval Ishai, Ron D.
   Rothblum, David J. Wu, *Dot-Product Proofs and Their Applications*,
   [FOCS 2024](https://doi.org/10.1109/FOCS61266.2024.00057),
   [SIAM J. Comput. 2026](https://epubs.siam.org/doi/10.1137/25M1751505),
   [ePrint 2024/1138](https://eprint.iacr.org/2024/1138),
   [ECCC TR24-114](https://eccc.weizmann.ac.il/report/2024/114/),
   [revision 2, 2025-12-30](https://eccc.weizmann.ac.il/report/2024/114/revision/2/download/).
   The detailed anchors below were cross-checked in that revision
   and the [public author manuscript](https://www.cs.utexas.edu/~dwu4/papers/DPP.pdf),
   not to an assumed identical typeset journal full text.
   - Theorem 1.3 on pp. 4–5 states \(\widetilde\Omega(S^9/\varepsilon^6)\)
     as a sufficient field-size regime and \(O(S\log(S/\varepsilon))\)
     length; the paragraph following it asks to improve the bound.
     Footnote 6 on p. 7 specifically conjectures improvement in \(S\).
   - Definition 3.1 and Remark 3.2 on pp. 14–15 give the fully linear
     randomized query/membership interface. Definitions 5.2, 5.4 and
     5.5 on pp. 33–34 distinguish boundedness, accepting-set
     evasiveness and query hyperplane evasiveness.
   - Claim 5.3 on p. 33 supplies honest binary proof encoding.
     Theorem 5.6 on p. 34 gives the bounded embedding, with answer
     bounds and \(P\ge\mu^2\gamma p^2/\eta^2\); its proof is §5.1.
     Corollary B.6 on p. 77 supplies the two-query proof of length \(2s\) and
     error \((2s+1)/p\), with the square graph as its acceptance predicate.
     Those three ingredients are used, not reproved as novel results.
   - Theorems 5.7–5.8 and Corollaries 5.10–5.11 are the closest
     in-paper packing bounds. Theorem 5.7 and §5.2 use coordinate
     coefficient ranges with a dominating previous-coordinate weight
     and integer no-wrap decoding. Theorem 5.8 uses the [BIOW20]
     two-query transformation and costs order
     \(b_{\rm large}b_{\rm small}^{\,2}/\eta\).
     The author manuscript's displayed sufficient condition in
     Corollary 5.11, with its displayed \(\gamma\) substituted,
     has order \(S^{10}\log^4(S/\varepsilon)/\varepsilon^6\);
     the introductory Theorem 1.3 instead states the exponent \(9\).
     We compare conservatively to the smaller stated exponent \(9\).
     The new proof uses neither formula as a hypothesis and makes
     no assertion about how that discrepancy arose.
2. **[AICR c/0070]** [Improving the Field Size of Large-Field Dot-Product
   Proofs](https://aicr.info/c/0070/). This independent problem index
   asks for a pair \((a,b)\) with \(a<9\), at the unchanged length
   \(O(S\log(S/\varepsilon))\). Its separate question about
   \(O(P^{-1/2})\) soundness is not answered here. The index records
   its own targeted prior-art check as of 2026-08-25; that is not a
   substitute for checking subsequent work.
3. **[DFGK14]** George Danezis, Cédric Fournet, Jens Groth, Markulf
   Kohlweiss, *Square Span Programs with Applications to Succinct
   NIZK Arguments*, ASIACRYPT 2014, LNCS 8873, pp. 532–550,
   [DOI](https://doi.org/10.1007/978-3-662-45611-8_28),
   [author manuscript](https://www.pure.ed.ac.uk/ws/files/55342185/Square_Span_Programs.pdf).
   §2 gives circuit satisfiability through square span programs,
   the underlying idea made into a two-query FLPCP by Corollary B.6.
4. **[BIOW20]** Ohad Barta, Yuval Ishai, Rafail Ostrovsky, David J.
   Wu, *On Succinct Arguments and Witness Encryption from Groups*,
   CRYPTO 2020, [DOI](https://doi.org/10.1007/978-3-030-56784-2_26),
   [author manuscript](https://www.cs.utexas.edu/~dwu4/papers/SNARKsWE.pdf).
   §3.1, Construction 3.4, chooses random sufficiently large
   mixed-radix digits from restricted intervals and reconstructs
   in the integers before reducing modulo the prime. §3.2 considers
   tail bounds for Hadamard-based answers and resulting verification
   tradeoffs. Neither the scalar mixing form nor bounded
   one-query packing originates here; the proposed difference is
   full-field slopes with ambiguity charged to soundness and
   polylogarithmic modular box decoding.
5. **[BCIOP22]** Nir Bitansky, Alessandro Chiesa, Yuval Ishai,
   Rafail Ostrovsky, Omer Paneth, *Succinct Non-Interactive Arguments
   via Linear Interactive Proofs*, J. Cryptol. 35, article 15,
   [DOI](https://doi.org/10.1007/s00145-022-09424-4).
   The bit-packing approach is prior work; see also [BHIRW, §2.2
   and §5.2] for the explicit relationship to bounded query packing.
6. **[Lenstra]** H. W. Lenstra, Jr., *Integer Programming with a
   Fixed Number of Variables*, Math. Oper. Res. 8(4), 538–548
   (1983), [DOI](https://doi.org/10.1287/moor.8.4.538),
   [author copy](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1983i/art.pdf).
   Classical fixed-dimensional substitute for the Euclidean decoder.
7. **[BEIRW26]** Nir Bitansky, Saroja Erabelli, Yuval Ishai, Ron
   D. Rothblum, William Wang, *Dot-Product Proofs of Powers and
   Applications*, TCC 2026, LNCS 17193, pp. 497–528,
   [DOI / public abstract](https://link.springer.com/chapter/10.1007/978-3-032-43624-5_16).
   The public abstract presents a field-agnostic arithmetic-circuit
   DPP with inverse-polynomial soundness using a proofless powers
   DPP, and states concrete improvements to related applications.
   As of 2026-11-27 the publisher's full chapter required access
   and no open full-text copy or official slides were located in
   the checked sources, including the authors' publication lists.
   The abstract does not
   specify the general \((S,\varepsilon)\) field-size exponents and
   proof length for the comparison here. We do not claim priority
   over unavailable portions of this paper, or that its result
   cannot match a specialization of ours. Our theorem proves the
   quantitative inequality against the stated old Theorem 1.3
   and gives an independent packing-only route.

The targeted check through 2026-11-27 used the original paper's
current public author manuscript, its ePrint/ECCC revision metadata,
the named fallback references, the author publications lists, and
queries for “dot-product proofs field size packing”, “fully linear
PCP modular random projection packing”, “dot-product proofs field
size S^6”, the original ePrint number with 2026, and the full title
of [BEIRW26]. No public source inspected gave this same full-field
slope decoder plus \((6,6)\) theorem under the unchanged proof
length. This is a bounded prior-art check, not a claim of exhaustive
priority. No source PDF or outside code is redistributed.
