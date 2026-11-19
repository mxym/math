# Locating the crossing of fixed-mean beta laws

**Yongxian Zhang (张永贤) · AI-assisted research draft · November 19, 2026.** Independently checked internally, not externally peer reviewed. No claim of worldwide priority.

For beta laws with a common mean, increasing the total shape moves probability mass toward that mean. But this alone does not say what happens to the probability of falling below the mean, or below one half. When the mean exceeds one half, the first probability strictly increases and the second strictly decreases, for every positive real total shape. Thus the unique interior crossing proved by Portnoy, Torrado and Veerman lies strictly between one half and the mean. Reflection handles means below one half. The first part of [the proof](PROOF.md) addresses Kochar’s question at one half as stated in their 2024 paper; its cited 1979 technical report could not be checked directly.

Two discrete consequences are distinguished from the continuous result:

- [Floored binomial tails](PROOF.md#3-the-floored-binomial-inequality): in the parameter range posed at the end of Fokkink–Meester–Pelekis (2023), the maximum is attained at the first index. This treats equal stakes, **not** Csóka’s question for arbitrary stakes. The proof also identifies how classical or already published results give the needed discrete endpoint comparisons.
- [Binomial left-loadedness](LEFT-LOADED.md): the classical Feldheim–Rényi reflected-mass calculation implies both conditions of Fokkink–Papavassiliou–Pelekis (2022), Conjecture 4.1, by summing tails. This is not a claim to have discovered that calculation or Simmons’ inequality.

See [sources and access limitations](SOURCES.md) and [independent internal mathematical review](REVIEW.md). Its hashes identify the originally audited mathematical drafts; the versions here differ editorially in headings, attribution, and bibliographic context, not in the proofs or statements. To replay the finite checks, run `python3 -O verify.py` and `python3 -O left_check.py` in this directory. They use standard-library integer and rational arithmetic; the proofs, not a finite computational search, give the unrestricted statements. The expected output is in [CHECKS.txt](CHECKS.txt).
