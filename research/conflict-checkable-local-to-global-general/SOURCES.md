# Sources and range

1. Benny Applebaum and Eliran Kachlon, *Conflict Checkable and Decodable
   Codes and Their Applications*, [IACR ePrint 2023/627](https://eprint.iacr.org/2023/627),
   [full text](https://eprint.iacr.org/2023/627.pdf),
   [ECCC TR23-062](https://eccc.weizmann.ac.il/report/2023/062/), SODA 2024.
   Definition 1.1 and Claim 1.2 (p. 6) give the conflict-graph model;
   Lemma 1.6 (p. 9) states local-to-global consistency on any at least
   \(n-d+1\) coordinates; Theorem 1.8 and its following paragraph
   (p. 11) give the comparison-based ceiling, ask whether it can be
   surpassed with local-to-global consistency, and note the known
   \(d=n-1\) case. Theorem 1.3, §2, Lemma 2.2, and Claim 2.4 give
   their Euclidean Gram construction for almost-MDS conflict-checkable
   codes. The source leaves the local-to-global property of that
   construction undecided.
2. [AICR c/0096](https://aicr.info/c/0096/) records the non-endpoint
   conjecture. The prior length-four result in [this repository](https://github.com/mxym/math/tree/1dbd4af17c6db9cecff64019e80e020ca77b013e/research/conflict-checkable-local-to-global)
   already gives the non-endpoint existence witness \(n=4,d=2\).
   The present work extends the combined rate and consistency
   guarantee to the entire \(n,d\) range. It uses the same whole
   Gram-level and free-offset approach but a different interpolation
   step, over a suitable totally real order. It does not settle
   any claim about the source's own original family.
3. Alexander Borisov, *Locally Integer Polynomial Functions*,
   [Integers 25 (2025), A41](https://math.colgate.edu/~integers/z41/z41.pdf),
   [DOI](https://doi.org/10.5281/zenodo.15283731), §1 and Theorem 8,
   provides related context over the integers: integer two-point
   divided differences are necessary in general and do not suffice
   on arbitrary sets. The interpolation here is a special finite
   sufficiency condition under residue separation on an integer
   order; its CRT/localization proof is self-contained. No claim
   is made that CRT, Vandermonde interpolation, localizations, or
   Euclidean Gram polarization are new by themselves.
4. Bounded check on 2026-11-27 compared the ePrint record, ECCC and
   proceedings, the problem page, and 2024–2026 searches combining
   the exact paper title, “conflict checkable,” “local-to-global,”
   “Singleton,” “Gram,” “residue,” and “interpolation.” No matching
   all-parameter local-to-global near-Singleton construction was
   found. This is not an absolute priority assertion.

This is abstract finite coding theory. No claim is made about
deployment, secrecy, a malicious-party setting, or decoding
complexity beyond the combinatorial definitions stated in the proof.
