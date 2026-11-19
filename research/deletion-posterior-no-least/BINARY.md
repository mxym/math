# Binary posteriors after two deletions: exact extremal peak and failure of a universal entropy maximizer

All lengths below are *received* lengths; all hosts have length two larger. Let an input be uniform on binary words of length n=m+2, where m≥1, and independently retain a uniformly random increasing m-subset. For a received word y, K_y(x) is its number of embeddings in x. The posterior is p_y(x)=K_y(x)/D, D=4 binom(m+2,2): every retained mask contributes 4 hosts. Throughout write v≺w for weak inequalities on every descending prefix and equality on the full sum.

## 1. Sharp largest-atom minimum

Put M(y)=max_x K_y(x) and P(m)=min_y M(y). Then P(1)=3, and for m≥2,
```
P(m)=min { max(4,m+1), max(6,3+ceil((m−2)/2)), 9 }.
```
In particular P(m)=9 for all m≥13. The maximum order-infinity Rényi entropy is log(D/P(m)), with logs in any common base. The following test describes **all** equality cases, up to either choice of first bit (and without any limitation on adjacent double runs).

* If a run has length at least 3, there is no equality.
* With no double or longer runs, M(1-bit word)=3 and M(y)=max(4,m+1) for m≥2.
* If all runs have length one or two, with j≥1 double runs, let s_0,s_j be the numbers of singleton runs before and after them, and s_i the numbers of singleton runs in the j−1 intervening gaps. At j=1,
  M(y)=max(6,3+s_0,3+s_1).
  At j≥2,
  M(y)=max(9,3+s_0,3+s_j,max_{1≤i<j}(5+s_i)).
  Such a word attains the optimum if and only if the displayed M(y) is P(m).

**Proof.** We use the positive embedding multiplicities, not just the Shannon formula, in Singhvi, Sabary, Bar-Lev and Yaakobi, *Conditional Entropies of k-Deletion/Insertion Channels*, Lemma 4 and the five host classes in the proof of Theorem 3 ([arXiv v2](https://arxiv.org/html/2407.10026v2), [TIT](https://doi.org/10.1109/TIT.2025.3581849)). The equivalent previous run/alternating-segment work is discussed there; their Lemma 4 treats neighboring singleton runs and their Theorem 3 corrects an edge case. For R runs of lengths r_i, these classes have:

1. one entry binom(r_i+2,2) per i;
2. one entry (r_i+1)(r_k+1) per i<k;
3. m+3−R−r_i entries equal to r_i+1 per i;
4. one entry per maximal alternating segment, obtained by increasing its length by two;
5. remaining positive entries equal to one.

The classes count distinct hosts even if their numerical multiplicities coincide. To evaluate class 4, split a binary word at every equal-adjacent bond into consecutive alternating segments of lengths a_0,...,a_j. Here j is the number of such bonds (hence equals the number of double runs when all run lengths are one or two). For a fixed segment i, let b_i be the nearest earlier segment of length at least 2, default 0; let f_i be the nearest later such segment, default j. Lemma 4 writes its weight as 1 plus the sum of a from b_i through f_i, minus (a_{b_i}−1) if b_i differs from i, and minus (a_{f_i}−1) if f_i differs from i. For an alternating word this gives m+1. In the single/double case j≥1, endpoint lengths are 1+s_0 and 1+s_j; every interior length is 2+s_i. Even with consecutive doubles (s_i=0) the interior length is at least 2. Thus b_i=max(0,i−1), f_i=min(j,i+1), including when j=1 and when either outer length is 1. The weights reduce exactly to 3+s_0, 3+s_j and 5+s_i on the interior. The largest remaining weight of classes 1–3 when j=1 is 6, even without any singleton; for j≥2 it is 9. With no doubles and m≥2 it is 4; at m=1 class 1 supplies 3. This proves the wordwise formula.

With j=1 the optimal two gap sizes are obtained by dividing m−2 as evenly as possible (not necessarily the only optimum because of the 6 floor). With j≥2 the lower bound of 9 is achieved at every m≥4, using runs all of length two, with one singleton appended for odd m. For m=2,3 this last option is infeasible but the other candidates have minimum less than 9. A run of length at least three forces the first class to have an entry at least 10, hence cannot minimize. This proves the claim.

## 2. The least element exists exactly up to length five

Ma–Zhang, *Maximal input entropy for binary two-deletion and two-insertion channels*, [Theorem 2.2 (4)](https://arxiv.org/html/2611.01064v1), prove that for every received length m≥1 the only Shannon maximizers for the binary two-deletion posterior are the alternating word A_m and its complement. Their two distributions are coordinate permutations. This preprint's distinct two-*insertion* length restrictions are not relevant here.

At m≥6 the alternating peak max(4,m+1) exceeds P(m): for m≥6, both 6 and 3+ceil((m−2)/2) are <m+1. If the finite posterior family had a least element for majorization, that posterior would maximize Shannon entropy **and** minimize the largest atom. The latter fails for both Shannon maximizing words. Consequently there is no least element. This is not a claim about absence of minimal (undominated) elements.

For 1≤m≤5, the two alternating/complement words do supply a least vector. One exact finite proof is the following full enumeration; it has no symmetry reductions, tolerance or entropy approximations. In particular it compares all 62 received words, including both first-bit choices. For each m initialize the count C[y,x] to zero for all length-m words y and length-m+2 words x. For each x, for each 1≤i<j≤m+2, increment C[delete_{i,j}(x),x]. Sort each row decreasing and cumulatively sum it. For every row subtract the corresponding alternating cumulative sums coordinatewise; the minimum over all rows and prefix positions is 0 for each m=1,2,3,4,5. The `small_cases` function of the [direct checker](binary_check.py) attests to these five claims (and thereby does not invoke the five-class formula). Ma–Zhang's equality case excludes any other words attaining the least sorted vector. The publicly accessible [Ma–Zhang project dossier, Scope assessment](https://www.trureturing.org/research/singhvi-sabary-barlev-yaakobi-2024-deletion-channel-max-input-entropy/) already proposed the length-12 obstruction using (0011)^3 and A_12, explicitly outside their declarations and finite experiments; the insight that a peak obstruction can exist is not new. Our result gives the exact minimax peak and the full length division, not a refutation of their Shannon theorem.

## 3. A strict disagreement for every fixed order greater than one

Write H_alpha(y)=(1−alpha)^{-1}log(sum_x p_y(x)^alpha), with alpha>1. Let B be a word with one double and l singleton runs to its left and r to its right, l+r=m−2. Let g(t)=t^alpha−t. Since g(0)=g(1)=0 and the total embedding counts are D for both words, we may subtract g-sums instead of power sums. For A_m the contributions beyond 1 are: m entries of 3, binom(m,2) of 4, 2m of 2, one of m+1. For B they are: m−1 of 6, m of 3, binom(m−2,2) of 4, 3(m−2) of 2 and the two exceptional entries l+3,r+3. Here and below take binom(0,2)=binom(1,2)=0, and these tables for comparisons assume m≥2. To verify the B table, the double contributes one extension by two (weight 6), a paired one-symbol extension (6) with every singleton, and two hosts in class 3 (weight 3); each singleton contributes 3 from its same-run extension, participates in the pairs of singleton runs (4), and has three class-3 hosts (2). The two alternating-segment extensions were evaluated above.

Consequently
```
sum_x K_B(x)^alpha − sum_x K_A(x)^alpha
= (m−1)g(6) + (3−2m)g(4) + (m−6)g(2)
   + g(l+3)+g(r+3)−g(m+1).
```
Choose |l−r|≤1. For each fixed real alpha>1 the right side is
(2^{1−alpha}−1)m^alpha + O_alpha(m^{alpha−1}+m),
by the mean value theorem at m/2 and at m. It is eventually negative. Hence H_alpha(B)>H_alpha(A_m) for all sufficiently large m depending on alpha. This does not assert the centered double is globally optimal at that order, nor a single finite m sufficient for every real alpha>1. At alpha=2, elementary expansion gives the exact difference 8m−2lr; the first centered example with negative difference is m=20, l=r=9 (at m=19, lr=72<76; for 2≤m≤19, (m−2)^2/4≤4m). There the exact two sums are 3822 versus 3824 with common normalization 924^2. Thus even order 2 and Shannon have incompatible maximizing words from m=20 onward, using the balanced choice (at odd m≥21, lr=floor((m−2)^2/4)>4m as well). No claim of global first failure before m=20 for other competitors is needed. At unit order Ma–Zhang's Shannon result is unchanged.
