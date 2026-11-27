# Primary source comparison and scope

1. Benny Applebaum and Eliran Kachlon, *Conflict Checkable and Decodable
   Codes and Their Applications*, [IACR ePrint 2023/627](https://eprint.iacr.org/2023/627),
   [full text](https://eprint.iacr.org/2023/627.pdf),
   [ECCC TR23-062](https://eccc.weizmann.ac.il/report/2023/062/);
   SODA 2024. The ePrint p. 6 gives the pair projection/conflict graph
   definition and Claim 1.2's equivalent clique definition;
   Lemma 1.6 p. 9 states local-to-global consistency; p. 11 states
   Theorem 1.8, the conjecture and the already known \(d=n-1\) endpoint.
   These definitions use all applicable positions and code dimension
   \(k=\log_q|C|\).
2. Their Theorem 1.3 and restatement Theorem 2.1 give almost-MDS
   conflict-checkable codes. Their §2 constructs evaluations of
   integer polynomials with fixed Euclidean Gram matrices of digit
   vectors of the nonconstant coefficients; Lemma 2.2 and Claim 2.4
   use \(t+2\) points to prove degree-at-most-\(t\) interpolation.
   This note uses that existing Gram-level idea. The distinction here
   is a whole integral Gram level, a field offset, and four evaluation
   points with primitive triple gaps. These allow reconstruction
   after **three** observations and ensure the interpolant still
   belongs to the same level, giving local-to-global consistency.
   The p. 9 sentence preceding §1.2.1 explicitly leaves this
   property of the source's own construction undecided; we do not
   assert that its construction has it.
3. [AICR c/0096](https://aicr.info/c/0096/) is a secondary transcription,
   explicitly seeking a witness with \(1<d<n-1\); its posted status
   was open when checked on 2026-11-27. We also checked the ePrint
   revision/author record, ECCC report and SODA record and searched
   the paper title, the conjecture terms “conflict checkable” and
   “local-to-global,” and combinations with “near-Singleton,”
   “polynomial,” and “Gram” for 2024–2026 follow-ups. We did not
   find a matching construction or resolution in this scope. This
   bounded search is not a formal priority assertion.

The result here is exactly \((n,d)=(4,2)\), including dimensions
arbitrarily close to the Singleton upper bound 3 from below. We
make no claim about every other distance/length, all alphabet sizes,
efficient construction of the maximizing Gram class, or decode-time
performance.
