# Original question, prior work, and scope

- Amos Beimel, Yuval Ishai, Eyal Kushilevitz, Hanjun Li,
  [*Cryptography with Weak Privacy*, ePrint 2025/1978](https://eprint.iacr.org/2025/1978),
  [public PDF](https://opencryptology.org/2025/1978.pdf), also
  preserved as the [2026-04-28 mirror snapshot](https://opencryptology.org/2025/1978/versions/20260428T172000Z.pdf).
  The precise target is the final item of the “Open Problems”
  list on printed page 7: a WP \((n-1)\)-out-of-\(n\) threshold
  scheme with share size \(o(\log n)\). Definition 2.2 on
  printed pages 12–13 gives the pointwise likelihood-ratio
  condition, the alphabet-size measure, and perfect correctness
  for every dealer random choice. Section 1.1 specifies the
  one-bit setting. The [TCC 2025 proceedings chapter](https://doi.org/10.1007/978-3-032-12290-2_14)
  gives the publication record; the exact problem and definition
  locators above are to the publicly verifiable ePrint. The
  ePrint history indexed on 2026-11-27 lists one approved October
  2025 version; the public PDF still contains the exact question.
  [AICR c/0075](https://aicr.info/c/0075/) is a discovery pointer,
  not the primary source.
- Amos Beimel and Matthew Franklin,
  [*Weakly-Private Secret Sharing Schemes*, TCC 2007](https://iacr.org/archive/tcc2007/43920253/43920253.pdf),
  [author copy](https://www.cs.bgu.ac.il/~beimel/Papers/BFTCC.pdf).
  The threshold-two construction has two-bit shares,
  but only concerns unauthorized singletons at that threshold.
  Their §5.3 Theorem 4 high-threshold construction, for the
  relevant prime-power cases, still uses an alphabet of about
  \(3n/4\) at the \(n-1\) threshold; it gives no constant-size answer.
  The present ordered quadratic rule does not require anonymity.
- For the distinction from ordinary perfect-privacy lower bounds see
  [*Threshold Secret Sharing Requires a Linear-Size Alphabet*](https://theoryofcomputing.org/articles/v016a002/),
  especially its perfect-privacy hypotheses. Our \(1/3\)-WP
  construction does not meet those hypotheses or claim a result
  for arbitrary thresholds, longer secrets, general access
  structures, or stronger security notions.

The double-parity code and the two-bit quadratic truth-table
fact are standard. The result here is their use with a globally
balanced completion coloring and exact finite dealer randomness
for this precise threshold question. A bounded literature scan on
2026-11-27 used the paper title and ePrint number, “weakly private
\((n-1)\)-out-of-\(n\),” “constant share size,” “two-bit,” “parity,”
and “bilinear threshold.” No matching prior resolution was found
in the identified primary literature. No absolute priority or
minimum alphabet claim is made.
