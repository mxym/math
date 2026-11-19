# When deletion posteriors have no least element

**Yongxian Zhang.** AI-assisted research note, independently checked within the AI workflow. No external peer review or priority certification.

A uniform word has exactly $d$ uniformly chosen letters deleted. After observing the remaining $m$ letters, one can rank the posterior probabilities of all possible original words. A **least** posterior would be at least as spread out as every other posterior: for every $k$, its $k$ largest entries would have the smallest possible total. The known constant-output result answers the opposite question.

**Binary alphabet.** For every fixed $d\ge2$, no such least posterior exists for all sufficiently large $m$. The classical count of original words having exactly one embedding leaves only the alternating observation as a candidate. But the alternating word has a growing largest atom before normalization; a periodic observation of the same length has one bounded solely in terms of $d$. The proof also shows that the smallest achievable raw peak eventually stabilizes and that alternating observations eventually fail to maximize every *fixed* Rényi order $\alpha>2$. These assertions do **not** decide the Shannon maximizer for three or more deletions.

- [General proof](ALL-RADII.md): a periodic construction and a leftmost/rightmost embedding comparison.
- [Exactly two deletions](BINARY.md): a least posterior exists precisely at received lengths 1 through 5; the minimum raw peak is explicit and equals 9 from length 13 onward. Every fixed $\alpha>1$ eventually disagrees with the known Shannon maximizers. At length 20 a centered double run already beats alternation at order 2.
- [Larger alphabets](SPACED.md): local refinements of letter coincidences imply majorization. When $q\ge\min(m,d+1)$, the least distributions arise exactly from words without any repeated symbol within distance $d$. Their sharp largest atom is given by a balanced integer product. The one-deletion Shannon characterization is prior work.

[Sources and distinctions](SOURCES.md) include the earlier two-error embedding classes, exact Shannon theorem, prior length-12 obstruction proposal, fixed-word peak studies and the earlier repository result. [Internal review](REVIEW.md) covers the three mathematical proofs. The hashes in that review refer to the frozen source text before presentational changes and the inclusion of a direct derivation of the cited singleton formula; the manifest below covers the distributed files. Proofs use no numerical fits; only the five small lengths in the exact two-deletion division use finite enumeration.

Reproduce the three exact checks with standard-library Python 3.10 or later:

```sh
python3 -B -O binary_check.py
python3 -B -O local_check.py
python3 -B -O independent.py
sha256sum -c SHA256SUMS
```
