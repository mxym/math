# One-run oscillations and an alphabet-uniform construction for non-overlapping codes

Let C(n,q) denote the unrestricted largest size on q≥2 symbols, under the rule that no nonempty proper prefix of a codeword equals a suffix of any codeword, including itself. Put a=1−1/q and let S(n,q) be the largest of the one-run codes in Chee–Kiah–Purkayastha–Wang, Eq. (5): for 2≤k≤n−2 the words have shape 0^k b w c, with b,c nonzero, and w of length n−k−2 containing no string 0^k. We use their C/S notation, not the alternative convention in some later papers. All logarithms not explicitly subscripted are natural.

**A (fixed alphabet).** Write r=n a/q^floor(log_q(n a)) and h(x)=x exp(−x). Then

    n S(n,q)/q^n = a max{h(r),h(r/q)} + O_q(log n/n).
    liminf n S(n,q)/q^n = (log q)/q^(q/(q−1)),
    limsup n S(n,q)/q^n = (q−1)/(qe).

The first constant is strictly smaller than the second. Thus the liminf assertion of the cited Theorem 4.2, Eq. (9), for S, does not hold; along an appropriate subsequence the value stated there is attained in the limit. The unrestricted liminf lower bound for C in their Theorem 1.1 is a different assertion and is **not** refuted.

**B (all alphabets).** There are absolute constants A and n₀ so that, simultaneously for every integer n≥n₀ and every integer q≥2,

    n C(n,q)/q^n ≥ (q−1)/(qe) − A (1+log_q n)/n.

In particular the weaker absolute O(n^−1/2) bound follows. Whenever n→∞ and q=q(n)→∞, the normalized optimum tends to 1/e by the classical Levenshtein upper bound. Together with the absolute upper error in the earlier fixed-alphabet manuscript this also gives uniform two-sided O(n^−1/3) error around (q−1)/(qe). The former growing-alphabet consequence does not need that manuscript.

## A finite estimate for non-overlapping markers

A family of length-L markers is non-overlapping if two occurrences in an iid uniform string with distinct starts at distance less than L are impossible. Let p be its total probability at one start, and use M consecutive starts on free independent letters. For j≥1 the sum of the j-fold intersection probabilities is precisely

    binom(M−(j−1)(L−1),j) p^j,

where binom(u,j)=0 when u<j. Indeed only starts separated by at least L can occur, and the j blocks are then independent. The count follows by subtracting (i−1)(L−1) from the i-th position in sorted order. The j=0 term is one. If Mp≤H for a fixed H, the probability of no marker equals exp(−Mp)+O_H(L/M). In detail the ratio of the displayed term to (Mp)^j/j! is a product of j factors 1−[(j−1)(L−1)+i]/M with 0≤i≤j−1 when the binomial is nonzero. The nonnegative deficit from 1 is at most j²L/M by the product bound. When the binomial vanishes the same bound applies since j²L≥M. Taking the absolutely summable sum of these differences against H^j/j! justifies comparison of finite inclusion–exclusion with the exponential series, including the tail.

## The one-run profile

For λ=na q^−k, independence of the two nonzero boundary letters gives exactly

    n |S_(k,q)(n)|/q^n = a λ Pr(w avoids 0^k).

In the free word w it suffices to exclude the non-overlapping markers b0^k (b nonzero), except for a zero run beginning at the first letter. That exceptional event has probability at most q^−k. If λ stays in a fixed compact interval of (0,∞), then k=O_q(log n), the number of full marker starts is M=n−2k−2, and their combined mean is M a q^−k=λ+O_q(log n/n), with constants also depending on the compact interval. The finite estimate gives the required approximation a h(λ)+O_q(log n/n) there.

For small λ the normalized size is ≤aλ. For large λ, independently subdivide w into whole blocks of q^k+k letters. Within each there are q^k starts for b0^k, with mean a. Overlapping indicators have nonpositive covariance, separated ones are independent, so the count X has E X²≤a+a². Cauchy–Schwarz yields Pr(X>0)≥a/(1+a). For λ≥1, k≤log_q n and the number of blocks is at least c λ−1 for all sufficiently large n with an absolute c>0 (use |w|≥n/2, q^k+k≤2q^k). Consequently the normalized size is at most C a λ exp(−c'λ), with absolute positive constants. These two bounds are uniform off compact intervals, not just statements about the longest-run limit along one subsequence.

For fixed q, the two grid values r and r/q are both eligible for large n and lie in [1/q,q]. Their maximum h-value is bounded away from zero. Choose one compact interval containing this range so that outside it the preceding tail upper bounds are strictly below half that minimum times a. The maximizing code therefore lies inside the compact interval for all large n. As h is increasing for arguments up to 1 and decreasing afterwards, its maximum over the multiplicative grid is attained at r or r/q. This proves the asserted O_q error in A. The phase function attains maximum 1/e at r=1 or q; minimum occurs at the unique crossing h(r)=h(r/q), r=ξ=q log(q)/(q−1) strictly between 1 and q. Each target r in (1,q) is achieved in the limit by rounding r q^j/a to integers, and the endpoint value by rounding q^j/a (the phase endpoints agree). Since aξ=log q and exp(−ξ)=q^(−q/(q−1)), A follows.

## A tunable short marker

This construction refines the many-marker principle from the earlier code manuscript; no novelty is claimed for prefix dictionaries or the basic occurrence method. The key is first to tune a non-overlapping *short cylinder* to mass comparable to 1/n without a factor q in the rounding, then to thin its length-L extensions to near-exact mass 1/n.

For n≥16 let r=floor(log_q(n/8)), s=min(q−1,ceil(8 q^(r+1)/n)), and pick any s-element subset I of the nonzero symbols. Let D be all words 0^r i with i∈I, of length R=r+1. When r=0 this is a one-letter set. The mass d=s/q^R obeys

    4/n ≤ d ≤ 16/n,

since 1<8q^R/n≤q, so taking the ceiling costs a factor at most 2, and the cap q−1 retains at least half of the unrounded target. D is a non-overlapping marker family: any positive proper suffix ends nonzero and the corresponding prefix is all zero. Take L=ceil(2 log_q n)+2, so R<L, q^L≥n² and L=O(1+log_q n) with absolute constants. Set E to be the set of nonzero terminal symbols when r≥1, and the complement of I when r=0. Its density b=a in the former case and b=1−d≥1−16/n in the latter. In particular b≥1/2 for large n; uniformly b≥a−16/n.

Use all L-letter candidate markers starting with an element of D, ending in E, and containing no other complete occurrence of D. Their total mass is at least d(b−Ld): conditioned on the starting cylinder, the last letter is free, starts overlapping D are impossible, and at each other start the probability of another D is d. For sufficiently large n independently of q this is >1/n, because d≥4/n, b≥1/2, and Ld=o(1) uniformly. These candidate markers are mutually non-overlapping. For a proper suffix of length ≤r the last letter precludes a prefix match (vacuous when r=0); for length ≥R the match would begin at a second complete D. Select arbitrarily floor(q^L/n) of the candidates, forming a dictionary P of probability p. Thus np∈[1−1/n,1], with no asymptotic step depending on fixed q.

Accept n-letter words starting with a selected marker, ending in E, having no other full selected marker, and having no suffix of length R,...,L−1 starting with D. They form a non-overlapping code: any positive overlap of length ≤r fails the endpoint restriction, any of length R,...,L−1 fails the suffix condition, and any of length ≥L would exhibit a second selected marker. This includes the overlap of a word with itself.

Condition on the first L letters lying in P and the last letter in E (probability pb, independent since n>2L). All full marker starts numbered 2 through L are impossible; the starts L+1 through n−L are on free letters. Their count M=n−2L satisfies Mp=1+O(L/n). The finite estimate gives avoidance probability exp(−1)+O(L/n) for these starts. The final possible start n−L+1 includes the last letter and has conditional probability p/b, since all P end in E. The ≤L other unwanted suffix starts each have conditional probability ≤d/b (their windows are disjoint from the first block, and conditioning on the final symbol costs at most 1/b). Union bounding, without conditioning further on avoidance, costs O(L/n) in total. The total accepted probability is at least pb(exp(−1)−O(L/n)); multiplying by n and using np≥1−1/n and b≥a−16/n proves B. For consequences use the Levenshtein inequality nC/q^n≤(1−1/n)^(n−1) and, only for the uniform two-sided refinement, the earlier manuscript’s absolute upper error.
