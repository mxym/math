# Three fixed-size log-concavity questions

This package addresses questions (i)–(iii) in §7 of [Baslingker, Krishnapur and Madiman](https://arxiv.org/abs/2412.15116v2). All results concern **fixed size**, not a Poissonized or asymptotic law.

| Question | Answer |
| --- | --- |
| (i) Largest particle in the squared-Vandermonde ensemble with fixed total, equation (31) | **Yes** for the full range asked (number of particles greater than partition size). In fact each ordered particle has a log-concave marginal. |
| (ii) Each individual row under ordinary Plancherel measure | **Yes**, and the marginal result holds for every positive Jack parameter. |
| (ii) Sums of the first few rows under ordinary Plancherel measure | **No**. The sum of just the first two rows fails for every size n≥9: at n=9 the three consecutive counts are 1, 64, and 5581, with 64²<5581. |
| (iii) A uniform word of fixed length over a finite ordered alphabet, equation (32) | **Yes** for the longest **weakly** increasing subsequence, for every alphabet size and word length. |

**Proofs.** [ROWS-AND-WORDS.md](ROWS-AND-WORDS.md) proves the coordinate-slice lemma, the Jack row marginals and the word result. [VANDERMONDE.md](VANDERMONDE.md) proves the separate transition comparison required for (i); its increasing prefactor prevents a direct application of the random-word comparison. [PREFIX-SUMS.md](PREFIX-SUMS.md) gives the finite counterexample and the all-n≥9 result. The first proof's statement about what it does not address refers to that document alone; the two companion notes address the remaining items. The three files retain their reviewed proof bytes.

**Verification.** Run each of `check_rows_words.py`, `check_vandermonde.py`, and `check_prefix_sums.py` with `python3 -B -O`. All are standard-library cross-checks. Outputs and mathematical reviews are included, and each file is covered by `SHA256SUMS` apart from the manifest itself.

The ordered-coupling strategy is due to Yupeng Li. The ordinary first-row permutation result is prior work, as is the [repository's Jack first-row/matching theorem](../jack-matching-logconcavity/PROOF.md). This package does not assert answers for arbitrary powers of the Vandermonde, nonuniform words, longest common subsequences, or §7(iv)–(vi). See [source and scope comparison](SOURCES.md). AI-assisted research and internal AI review; not external peer review, and no priority guarantee.
