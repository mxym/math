# Independent audit: chromatic infinite log-concavity counterexamples

Audit date: 2026-10-08 (UTC).

## Verdict

**PASS for the mathematical disproof.** The absolute chromatic coefficient sequence of the simple connected cycle C17 has a negative entry in its third log-concavity transform. The proposed infinite family (all cycles C_n with n >= 17), endpoint-deleting variant, and full cycle classification all pass independent verification. No candidate code was imported or executed to obtain this audit's certificates.

**Novelty remains a bounded-search finding.** The official paper still states the conjecture. Independent targeted public searches did not locate an earlier cycle counterexample or correction. This is not a proof of priority or an exhaustive literature certification. In particular, the separate author updates page could not be read.

## 1. Exact target and conventions

The current official journal PDF, page 9, states Conjecture 21:

> The absolute values of the coefficients of any chromatic polynomial are infinitely log-concave.

Source: [Amdeberhan–Moll, official PDF](https://combinatorialpress.com/article/ojac/vol17/305.pdf).

The quantifier is universal. The preceding section introduces undirected graphs, includes cycles explicitly, and imposes no order bound, connectedness restriction, or special graph class. C17 is a simple connected undirected graph, so it is admissible even under several restrictions stronger than those actually printed.

The journal introduction defines the local transform as L(a)_k = a_k^2 - a_(k-1)a_(k+1). Its subsequent iterative-definition paragraph mixes the words concave and convex and does not spell out finite endpoints. This is an apparent typographical inconsistency; the conjecture's intended standard interpretation is corroborated by the earlier formulation below.

[Amdeberhan, arXiv:1207.4045v7](https://arxiv.org/pdf/1207.4045v7), page 14, Section 13, explicitly requires nonnegative iterates and explicitly sets a_(-1)=0. The corresponding chromatic claim is Conjecture 13.1. It too contains a concave/convex word slip, but its inequalities are unambiguous. The left boundary, the only potentially external boundary involved in the C17 certificate, is therefore directly specified in that formulation.

[Brändén, *Iterated sequences and the geometry of zeros*](https://arxiv.org/pdf/0909.1927), page 2, defines L on the same finite index set 0,...,n, with a_(-1)=a_(n+1)=0. It is reference [9] of the official paper. This supplies the standard zero-extension convention used throughout the main proof and classification.

The [live arXiv record](https://arxiv.org/abs/1207.4045) identifies v7, dated August 25, 2022, as the latest revision. Although that arXiv identifier was first created in 2012, the chromatic problem was newly added in the 2022 version. The conjecture is therefore not dated to 2012 merely from the identifier.

The [journal landing page](https://combinatorialpress.com/ojac-articles/issue-17-2022/infinite-log-convexity/) gives Issue 17 (2022), Paper 6, pages 1–10, DOI 10.61091/ojac-1706. The PDF's internal date is December 30, 2023. The audit records rather than resolves this bibliographic discrepancy.

## 2. Independent derivation of the coefficients

For a cycle C_n, apply edge-subset inclusion-exclusion to proper colorings:

    chi(C_n;q) = sum_(S subset E) (-1)^|S| q^c(S).

Every proper edge subset of a cycle is a forest, hence c(S)=n-|S|; the full set has c(E)=1. It follows that

    chi(C_n;q) = (q-1)^n + (-1)^n(q-1).

The constant coefficient cancels; the coefficient of q has absolute value n-1; and for 2 <= k <= n the absolute coefficient is binomial(n,k). Thus

    a = (0,n-1,binomial(n,2),...,binomial(n,n)).

The audit script also reconstructs C12 and C17 independently by enumerating all edge subsets, computing their components using a generic disjoint-set routine, and summing signed contributions. These exact polynomial coefficients agree with the formula. This is a check of the explicit graphs, not a basis for extrapolation to arbitrary graphs.

## 3. Short complete disproof

For C17:

    a_0,...,a_5 = 0,16,136,680,2380,6188.

With b=L(a), direct multiplication gives

    b_0,...,b_4 = 0,256,7616,138720,1456560.

For c=L(b):

    c_1 = 256^2 = 65536,
    c_2 = 7616^2 - 256*138720 = 22491136,
    c_3 = 138720^2 - 7616*1456560 = 8150077440.

Therefore

    (L^3(a))_2
      = 22491136^2 - 65536*8150077440
      = -28272276537344
      = -30464^3 < 0.

Infinite log-concavity requires every iterate to be entrywise nonnegative. This single negative integer disproves the universally quantified conjecture. No numerical approximation, finite-iteration extrapolation, real-root theorem, or unproved assertion is needed.

## 4. Infinite family checked symbolically

The audit's separate rational-polynomial implementation verified every intermediate b and c formula in the candidate, using sparse exact polynomials over Q rather than substituting a finite set of n values. It then verified the coefficientwise identity

    (L^3(a))_2 = -n^3(n-1)^8(n+4)Q(n)/103680,
    Q(n) = 2n^4 - 12n^3 - 327n^2 - 412n + 36.

It independently expands

    Q(u+17) = 2u^4 + 124u^3 + 2529u^2 + 17370u + 6615.

For every real u >= 0 this is strictly positive. For integer n >= 17, all the other displayed factors outside the minus sign are positive. Thus the proposed infinite family is rigorously proved, not inferred from sample values.

## 5. Endpoint-deleting alternative

If a nonstandard finite convention deletes both endpoints at each round, use G=C17 disjoint union K1 and its full degree-indexed coefficient sequence. Multiplication of the chromatic polynomial by q shifts the preceding sequence one position. The same negative value then appears at original degree 3 after three rounds. Only initial degrees 0 through 6 are involved, all within 0,...,18.

The independent trimmed-list implementation confirms this exact value. It also confirms C12 plus three isolated vertices at original degree 5 after five rounds. This alternative assumes the full polynomial coefficient sequence, including its zero coefficients; it is not a claim about deleting zero coefficients before defining a sequence.

## 6. Full cycle classification

Under standard zero extension, the claimed classification is correct:

    a(C_n) is infinitely log-concave if and only if 3 <= n <= 11.

The positive direction is supported by a sufficient invariant, not by testing only finitely many iterates and guessing the rest. If a is nonnegative and a_i^2 >= 3a_(i-1)a_(i+1), then for b=L(a):

    (2/3)a_i^2 <= b_i <= a_i^2,
    b_(i-1)b_(i+1) <= a_(i-1)^2 a_(i+1)^2 <= a_i^4/9,
    b_i^2 >= 4 b_(i-1)b_(i+1).

Hence b is nonnegative and again satisfies the factor-3 inequalities. Induction yields infinitely many nonnegative iterates once this region is reached, provided earlier iterates were nonnegative.

Independent exact checks confirm the following factor-3 certificates. The last quantity is the minimum slack over original degrees 2,...,n-1; omitted degrees have automatic nonnegative slack.

| n | certified iterate | minimum slack |
|---|---:|---:|
| 3 | 0 | 3 |
| 4 | 1 | 28 |
| 5 | 2 | 25825 |
| 6 | 2 | 90846 |
| 7 | 2 | 271656 |
| 8 | 3 | 711608924160 |
| 9 | 3 | 4029124698225 |
| 10 | 3 | 19225238518750 |
| 11 | 3 | 79738750726206 |

All preceding entries are nonnegative. For n=12 the exact negative fifth-iterate entry matches the candidate. For n=13,...,16 the exact fourth-iterate negative entries also match. The symbolic argument covers every n>=17. These three pieces cover all n>=3. No minimality claim among all graphs has been established or implied.

## 7. Public-status audit and limitations

Primary material independently inspected:

- Official current journal paper and journal record linked above.
- The author's [separate paper PDF](https://www.math.tulane.edu/~tamdeberhan/inf-lc.pdf), which retains the same conjecture as Conjecture 6.2.
- arXiv:1207.4045's revision history and v7 Sections 13–14. No resolution of Conjecture 13.1 is recorded there.
- [Author's publication list](https://www.math.tulane.edu/~tamdeberhan/publications.html) and [homepage](https://www.math.tulane.edu/~tamdeberhan/). The observed homepage says September 2026. No matching correction was located in the inspected list.
- Brändén's explicit finite-sequence convention linked above.

Independent queries included combinations of chromatic polynomial, infinite/infinitely log-concavity/log-concave, counterexample, disproof, solved, cycles, C12, C17, Amdeberhan, Moll, Conjecture 21, Conjecture 13.1, the exact article title, DOI, and erratum/correction. None retrieved an earlier matching refutation or an announced withdrawal.

Search results about ordinary log-concavity, chromatic symmetric or quasisymmetric functions, and Boros–Moll coefficients are different problems and do not establish prior resolution of this conjecture. General results on factor-r invariance are background, not a newly claimed contribution here.

The author-linked conjectures.html updates page failed to load via the web tool using HTTPS, HTTP, and the non-www hostname. The BIRS report could be found in search but a direct read failed in this audit; it is not used for the verdict. Citation indexes, searchable web pages, and author lists may be incomplete or stale. Therefore the proper public wording is: the mathematical refutation has passed independent checking, and the current bounded literature search found no previous resolution. Claims of first discovery, peer review, author confirmation, or exhaustive novelty clearance remain unsupported.

## 8. Reproducibility

- `independent_verify.py`: standalone standard-library checker written for this audit.
- `independent_exact_results.json`: independently generated coefficients, complete C12/C17 iterates, symbolic polynomial coefficients, shifted positivity polynomial, truncated-rule certificates, and classification certificates.
- `verification_output.txt`: successful run output.
- `SHA256SUMS.txt`: audit-artifact hashes.

Run with Python 3: `python independent_verify.py`.

No human peer review, formal Lean verification, or established first-priority claim is implied by this audit.
