# Sharp non-overlapping code size at every sufficiently large length

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review claimed.

Let \(S_n(q)\) be the largest size of a non-overlapping code of words of length \(n\) on a fixed alphabet of \(q\ge2\) symbols. No nonempty proper prefix of any word may be a suffix of any word, including itself. We show, uniformly as the integer \(n\to\infty\) at fixed \(q\), that a deterministic construction has size
\[
 |C_n|=\left(\frac{q-1}{qe}+O_q\!\left(\frac{\log n}{n}\right)\right)\frac{q^n}{n}.
\]
Combined with [Blackburn, Theorem 1, version 2](https://arxiv.org/html/2611.21913v2#S1), this proves
\[
 \lim_{n\to\infty} \frac{n S_n(q)}{q^n}=\frac{q-1}{qe}.
\]
Blackburn already proves the sharp upper coefficient, and his introduction attributes the matching lower coefficient **along an infinite subsequence** to the Gilbert–Levenshtein construction. Our contribution is to match it at every sufficiently large length, with a uniform quantitative error for the construction, not to reprove the upper bound or claim its priority. See also [Blackburn 2015, Section 3](https://arxiv.org/html/1303.1026v3) and [Blackburn–Nasr Esfahani–Kreher–Stinson, Section VI](https://arxiv.org/html/2211.10309v4#S6) for earlier lower constructions.

**Relationship to the prior liminf statement.** The uniform inequality was explicitly **stated** as a liminf in [Chee–Kiah–Purkayastha–Wang, Theorems 1.1 and 4.2](https://arxiv.org/html/1209.0236v2#S4.SS2). In the proof of Theorem 4.2, however, \(n\) is chosen as \(\lceil c\alpha(k,q)^k\rceil\) and the optimum fixed \(c\) is used. This proves the claimed coefficient along that subsequence; it does not justify the liminf over all integer \(n\). Blackburn 2015 §3 explicitly describes the earlier lower estimate as subsequential. The argument below supplies the missing uniform construction by adjusting the number of allowed continuations, not the block length.

## Construction

All positions are one-indexed. Let \(b=\lfloor\log_q n\rfloor\), \(m=2b\), and \(B=0^{b-1}1\), a fixed base word of length \(b\) (choose fixed distinct letters \(0,1\)). Let \(S\) consist of the first \(\lfloor q^{2b}/n\rfloor\) words of length \(b\) in lexicographic order. Write \(D=\{Bv:v\in S\}\) for the marker set of length \(m\). The density of markers in a uniform random length-\(m\) word is
\[
 p=|S|q^{-2b}=\frac1n+O_q(n^{-2}).
\]
Since \(q^b\le n<q^{b+1}\), \(S\) fits in the length-\(b\) words and its relative size \(\delta=|S|q^{-b}\) is at least \(1/(2q)\) for all sufficiently large \(n\).

Take all length-\(n\) words satisfying:
1. They begin with a marker, and end with a nonzero letter.
2. No marker starts at any other position where a full marker fits.
3. No suffix of a length in \([b,m-1]\) begins with \(B\).

Every prefix of length at least \(m\) begins with a full marker, so cannot match a proper suffix by rule 2. Prefixes of lengths \(b,\ldots,m-1\) begin with \(B\), so rule 3 applies. Prefixes of length less than \(b\) are all zero and cannot match a suffix by rule 1. This covers all cross-word and self overlaps.

## Counting without a limit along a subsequence

Begin with a uniform word and condition on rule 1, an event with probability \(p(q-1)/q\) for \(n>m\). The middle letters at \(m+1,\ldots,n-1\) remain independent uniform letters. Consider the \(N=n-2m\) starts \(m+1,\ldots,n-m\) for which a full marker lies entirely in the middle. For the indicator event \(A_i\) at each of these starts, the probability is \(p\). Each \(A_i\) is independent of the collection of all events with start distance at least \(m\), since they use disjoint letters from \(A_i\).

For distinct starts at distance less than \(b\), their copies of \(B\) cannot coexist: the final \(1\) of the first would occur within the initial zeros of the second. For starts at distance at least \(b\), the two base words require disjoint letters, so the joint marker probability is at most \(q^{-2b}=O_q(n^{-2})\). Thus every distinct pair of neighboring events (distance \(<m\)) has this joint bound.

For completeness, the needed elementary product approximation is as follows. Number the middle events in order. Let \(P_i=\Pr(\bigcap_{j\le i}\overline{A_j})\), and split the preceding absence event as \(E_i\cap H_i\), where \(E_i\) requires absence for \(j\le i-m\), and \(H_i\) requires absence for \(i-m<j<i\). Then \(\Pr(A_i\cap E_i)=p\Pr(E_i)\), hence
\[
 |P_i-(1-p)P_{i-1}|
 =|\Pr(A_i\cap E_i\cap H_i)-p\Pr(E_i\cap H_i)|
 \le \sum_{i-m<j<i}[\Pr(A_i\cap A_j)+p^2].
\]
Indeed after subtracting the independent term, both corrections are supported on \(H_i^c\); the union bound gives the inequality. Iterating and using \(1-p\le1\), the probability of no middle marker differs from \((1-p)^N\) by at most \(O_q(Nm/n^2)=O_q(\log n/n)\). Since \(Np=1+O_q(\log n/n)\) and \(Np^2=O_q(n^{-1})\), this is \(e^{-1}+O_q(\log n/n)\).

It remains to enforce the boundary starts from rules 2–3 that were not covered. There are \(O(m)\) of them. A start at position \(2,\ldots,b\) is impossible by the same conflicting copy of \(B\). For every other such position, the required occurrence of \(B\) uses letters disjoint from the already fixed initial \(B\). Before conditioning on the initial extension lying in \(S\) and the final letter being nonzero, that occurrence of \(B\) has probability \(q^{-b}\), even if it overlaps the extension or last letter. The combined additional conditioning has probability \(\delta(q-1)/q\), bounded below by a positive constant depending only on \(q\). Consequently each boundary start costs at most \(O_q(q^{-b})=O_q(1/n)\) under rule 1. A union bound changes the conditional acceptance probability by at most \(O_q(\log n/n)\), regardless of the middle tests.

Multiplying by \(\Pr(\text{rule 1})\) proves the stated count. No Poisson approximation theorem is needed. This same construction works if any set of the specified size is used for \(S\); the bound uses its density and no distributional property of the selected continuation words.

## Why rounding the older marker length is not enough

For the single-run Gilbert–Levenshtein construction with \(k\) leading zeroes, the basic marker is \(0^k J\), where \(J\) is the set of nonzero symbols. Its density is \(p_k=(q-1)q^{-k-1}\). Put \(\lambda=np_k\). Normalizing the number of codewords by \(q^n/n\), the leading term is \(((q-1)/q)\lambda e^{-\lambda}\), uniformly on compact subintervals \(0<\lambda<\infty\). Indeed \(k=O_q(\log n)\) there, marker starts less than \(k+1\) apart exclude one another, and the product approximation above applies to the free interior. Avoiding markers is the same as avoiding a run of at least \(k\) zeroes, except for a final all-zero suffix of at least \(k\) in the free interior; that event has probability at most \(q^{-k}\). Boundary effects from deleting the prefix and last letter are \(o(1)\).

For \(\lambda\to0\), the normalized size is at most \(((q-1)/q)\lambda\) by the initial and terminal conditions. For \(\lambda\to\infty\), split the free interior into disjoint blocks of length \(\lceil 1/p_k\rceil+k\). Each block has \(\lceil 1/p_k\rceil\) available marker starts, whose count \(Z\) has mean at least 1 and variance at most its mean (overlaps exclude, disjoint events are independent). Hence \(\Pr(Z>0)\ge (\mathbb{E} Z)^2/\mathbb{E}(Z^2)\ge1/2\) by Cauchy–Schwarz. For fixed \(q\), \(k p_k=O_q(1)\); the number of blocks is \(\Omega_q(\lambda)\) whenever \(\lambda\to\infty\). Thus the normalized size tends to zero on this end as well.

Choose lengths \(n_j\) nearest to \(q^{j+1/2}/((q-1)/q)\). Then the possible \(\lambda\)'s stay uniformly bounded away from 1 for all sufficiently large \(j\), because they lie in the geometric lattice \((1+o(1))q^{\mathbb Z+1/2}\). Since \(x e^{-x}\) has its strict maximum at 1, optimizing the old integer \(k\) cannot yield the sharp coefficient on this length subsequence. The fine density choice in our construction removes that lattice effect.

## Reproduce the finite checks

Run `python check.py`. The script enumerates the displayed construction for 11 small cases and checks disjointness of the prefix and suffix sets across all proper lengths. This is a finite sanity check, not a premise of the proof.
