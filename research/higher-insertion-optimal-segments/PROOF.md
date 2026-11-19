# The optimal first-order entropy gain and structure at each fixed higher insertion radius

**Yongxian Zhang.** Research note. This higher-radius asymptotic is distinct from the [exact finite-length three-insertion comparison](../three-insertion-entropy/README.md). All logarithms are base two. Constants in $O_k$ are allowed to depend on the fixed integer radius but not on the word or its length.

## Statement

For a fixed $k\ge4$, let $H_k(y)$ be the posterior input Shannon entropy conditional on the received binary word $y$ of length $n$ in the uniform exact $k$-insertion model of [Ma and Zhang](https://arxiv.org/html/2611.01064v1); thus the unknown input has length $n-k$. Write $H_k^*(n)=\max_y H_k(y)$ and $A_n=0101\cdots$. Define
\[
G_k(b)=(k-1)\log b-2(b-1),\quad
b_k=\left\lceil (2^{2/(k-1)}-1)^{-1}\right\rceil .
\]
Then
\[
 H_k^*(n)-H_k(A_n)=\frac{k}{n}G_k(b_k)+O_k(\log n/n^2).
\]
The coefficient is positive. For all sufficiently large $n$ every exact maximizing word has precisely $b_k$ maximal alternating segments, of lengths $n/b_k+O_k(\sqrt{n\log n})$ each. In particular its $b_k-1$ equal bonds are isolated doubled bits. Words with $b_k$ alternating segments as equal in length as possible attain the displayed entropy to within the error term; there is **no claim** that uniform integer rounding always gives a finite-length optimizer or that every nearby rounding does. These are not statements about the posterior on longer words in the deletion channel.

## 1. A uniform entropy bound for every host

Let $S$ be the uniformly random $k$-subset of omitted positions, let $X$ be the remaining word, and put $T(y)=H(S\mid X)=\mathbb E\log e_y(S)$, where $e_y(S)$ counts all masks with the same output as $S$. Then $H_k(y)=\log\binom nk-T(y)$. Partition the host into its constant runs and its maximal alternating segments with lengths $l_1,\ldots,l_b$. There are $D=b-1$ equal adjacent bonds. With $\lambda_i=l_i/n$, write $h(\lambda)=-\sum_i\lambda_i\log\lambda_i$.

The following entropy bookkeeping argument is the run/alternating-segment argument from the separate three-insertion note, now with arbitrary fixed $k$. The bipartite incidence graph of these two partitions is a tree (one site is one edge; each successive site adds one new block on precisely one side). Its vertex sums determine its edge labels. Thus the vector of run deletion counts $K$ and the vector of alternating-segment deletion counts $J$ together determine $S$. Also $K$ determines $X$. Consequently
\[
 T(y)=H(S\mid X,J)+H(J\mid X)\ge H(S\mid X,J)+H(S\mid K).
\]
The latter term is a sum, over run lengths $r$ and their random numbers $u$ of omissions, of expected $\log\binom ru\ge 2u(r-u)/r$. For $0<u\le r/2$ this follows from $\binom ru\ge(r/u)^u$ and $-\log s\ge2(1-s)$ on $0<s\le1/2$; symmetry covers the other half. Since $\mathbb E[u(r-u)]=r(r-1)k(n-k)/(n(n-1))$, this gives $H(S\mid K)\ge 2Dk(n-k)/(n(n-1))$.

Given $J$, the $b$ local outputs are known separately from $X$, and the masks on these segments are independently uniform at the prescribed local counts. Thus $H(S\mid X,J)$ is the expectation of the sum of the logarithms of the individual alternating-segment fiber sizes. In an alternating word of length $l$, if the local mask contains an adjacent omitted pair, it has at least one movable pair unit and its fiber size is at least one plus its retained length; cf. Ma–Zhang Theorem 5.1. For clarity one may place immutable sentinels opposite the two end bits: in every gap between retained sites, including sentinels, the least possible number of omissions is 0 or 1 according as the ends differ or agree. Above the least numbers all gap increments are even, and the free pair units can be distributed over the retained-length-plus-one gaps. The same rule covers a completely erased nonempty segment with one gap.

Let $w_i=\log\max(1,l_i-k+1)$. On a mask containing at most one adjacent pair in the *whole host*, the local log fiber sum is at least the sum of $w_i$ over all wholly omitted adjacent pairs in the segments containing them (pairs crossing segment boundaries are not in this sum). On any other mask the latter sum is at most $k\log n$. The probability of at least two distinct adjacent pairs is $O_k(n^{-2})$: a pair of neighboring edges needs three specified sites and has $O(n)$ placements; disjoint edges need four and have $O(n^2)$ placements. A specified pair occurs with probability $k(k-1)/(n(n-1))$. Accordingly,
\[
H(S\mid X,J)\ge \frac{k(k-1)}{n^2}\sum_i(l_i-1)w_i-O_k(\log n/n^2).
\]
For each $l\ge1$, the difference between $l\log l$ and $(l-1)\log\max(1,l-k+1)$ is at most $\log n+O_k(1)$: use $-\ln(1-t)\le2t$ for $t=(k-1)/l\le1/2$, and bound the remaining small $l$ directly. Combining the estimates proves the host-uniform bound
\[
T(y)\ge \frac{k(k-1)}{n}\big[\log n-h(\lambda)\big]
 +\frac{2kD}{n}-O_k\big((D+1)\log n/n^2\big).\tag{1}
\]

For $A_n$, its fiber has size 1 if no adjacent sites are erased, and size $n-k+1$ if precisely one adjacent pair is erased; this follows from the same gap argument, counting a length-two omitted run as one free pair. The exceptional probability of two or more pairs is $O_k(n^{-2})$, and always $0\le\log e\le k\log n$. Since the expected number of adjacent pairs is exactly $k(k-1)/n$, this yields
\[
T(A_n)=k(k-1)\log n/n+O_k(\log n/n^2).\tag{2}
\]

## 2. A matching construction at every fixed number of segments

Fix $b\ge1$, independent of $n$. Choose a host whose $b$ alternating segments have lengths differing by at most one (start each successive segment with the final bit of its predecessor). For large $n$ its $D=b-1$ native equal bonds have disjoint endpoints, are $\Theta_b(n)$ apart, and are as far from either end. We couple its mask with that on $A_n$ using the same omitted sites. We prove
\[
 H_k(y)-H_k(A_n)=\frac{k}{n}\big((k-1)\log b-2D\big)+O_{k,b}(\log n/n^2).\tag{3}
\]

Add fixed opposite sentinels to each end of the host, and append the same sentinels to its mask output. Count equal bonds, including bonds to the sentinels. Here a defect means an equal adjacent bond in the augmented string. A host with $D$ defects gives an output with at most $D+k$ defects. At that maximum the embedding is *unique*, as follows. In a gap with $r$ omitted sites, the change in equal-bond count is at most $r$. If $r\ge2$, it is at most 1 and so strictly smaller than $r$. A gap containing a native equality has change at most zero. Thus at the maximum all omitted sites are isolated, all native equality bonds survive unchanged, and every other equal output bond requires insertion of one opposite bit within it. To recover which equal bonds are native, read them left to right (index the left sentinel at 0). For the next native bond, the prospective host left index of a candidate is its output left index plus the number of strictly earlier equal bonds **minus the number of already assigned native equal bonds**. This is strictly increasing in the candidate. The ordered list of known native host indices therefore determines at most one assignment, then the mask is fixed. This argument also applies after a native double has been merged.

For the estimates call two omitted sites close if within $4k+10$ positions of each other. Count one proximity for each such pair and one for each omitted site within that distance of either end or any endpoint of a native double. A site in several marked neighborhoods counts only once. Masks with at least two proximities have probability $O_{k,b}(n^{-2})$: two marked sites have bounded choices; two close pairs require either two bounded distances or three sites in one bounded interval; a close pair and a marked site either share a site (two sites with bounded locations) or give two separate restrictions. Each log fiber size is at most $k\log n$. Discarding these masks has error $O_{k,b}(\log n/n^2)$.

* On a remaining mask with neither a consecutive pair nor an erasure at a native double, each isolated erasure creates one new equal bond. Thus $e_y=e_A=1$ by maximum-defect uniqueness. This also covers a single erosion immediately next to a native bond or at an end.
* If any native-copy site is erased, it is the only proximity. All other erasures are isolated and remote. The output is alternating throughout the window of possible consecutive retained ranks for this double (a host position $p$ has retained rank in $[p-k,p]$). Both-copy retention is impossible. Merge these two copies to one in the host, producing a skeleton with $D-1$ defects. The actual residual $k-1$ omissions in the skeleton create $k-1$ defects and retain the merged letter. By maximality the skeleton mask is unique. Any embedding that does not retain both copies projects to a skeleton mask with deletion budget $k-1$: if both are erased it erases the merged site, otherwise it retains it. Accordingly there are exactly two lifts of the actual skeleton mask. Thus $e_y=2,e_A=1$. The probability is $2Dk/n+O_{k,b}(n^{-2})$, since there are $2D$ distinct endpoints and any double counts fall within the discarded masks.
* If the mask contains an adjacent pair, this uses the only proximity. The pair is wholly in one segment away from the native doubles and ends. The other erasures are mutually isolated and separated from all doubles and from the pair. In $A_n$ the fiber size is $n-k+1$. For every native equal bond with left site $p$, the output contains just one equal bond whose left rank is in $[p-k,p]$, by the clean neighborhood at that double. Any embedding retaining **all** double endpoints must align them at these unique ranks. Their positions fix the separate surviving lengths in each pure alternating piece between successive anchors (and the two end pieces). The pieces have lengths $n/b+O_b(1)$; at internal boundaries the two anchor copies sit outside the piece. Only the piece containing the adjacent pair has a movable pair unit, and it has exactly one. The all-anchor embeddings consequently number one plus its retained length, or $n/b+O_{k,b}(1)$.
  
  For alternate embeddings retaining **not all** endpoints, sum over the native doubles lost (an upper bound allows overlaps). For each specified double, merging its two copies gives a skeleton with $D-1$ defects and $k-1$ available omissions. In the actual output there are exactly $D+k-2$ defects: each isolated omission creates one and the well-separated adjacent pair contributes none. The sentinels match the skeleton since a copy was merged in the interior. Therefore **every** mask in that skeleton giving this output would have maximal possible defect and is unique if it exists. It has at most two lifts. All lost-anchor embeddings together thus number at most $2D$, even if some lose more than one anchor. This proves $e_y=n/b+O_{k,b}(1)$, so $\log(e_A/e_y)=\log b+O_{k,b}(1/n)$. The probability of this case is $k(k-1)/n+O_{k,b}(n^{-2})$ by the exact expected adjacent-pair count and the discarded-mask bound.

Taking expectations proves (3). In particular for $b=2$ the gain is $k(k-3)/n+O_k(\log n/n^2)$; this alone suffices to disprove eventual optimality of alternation for every fixed $k\ge4$.

## 3. Optimization and rigidity for all maximizers

Take any exact maximizing word, equivalently one minimizing $T$. First its $D=O_k(\log n)$: the run term alone is $2Dk(n-k)/(n(n-1))$, while by (2) $T(y)\le T(A_n)=O_k(\log n/n)$. In (1)–(2) the error after multiplying by $n$ is now $O_k(\log^2 n/n)=o(1)$. As $h(\lambda)\le\log(D+1)$, this forces
\[
 2D-(k-1)\log(D+1)\le o(1),
\]
hence $D=O_k(1)$. In particular the original error in (1) for **all** maximizers is $O_k(\log n/n^2)$. The upper bound on their gain is therefore
\[
 H_k(y)-H_k(A_n)\le \frac{k}{n}[(k-1)h(\lambda)-2(b-1)]+O_k(\log n/n^2).
\]
Use $h(\lambda)\le\log b$ and (3) to conclude the discrete optimum formula.

The difference $G_k(b+1)-G_k(b)=(k-1)\log(1+1/b)-2$ changes sign from positive to negative at the real number specified inside the ceiling. Equality at an integer would give $(b+1)^{k-1}=4b^{k-1}$, which by coprimality forces $b=1$, then $k=3$, excluded. Hence the maximum is unique at $b=b_k$, with a fixed positive gap to all other integers (the sequence tends to minus infinity). Since the scaled remainder is $o(1)$, every exact optimizer eventually has exactly $b_k$ alternating segments. The coefficient is positive since $G_k(2)=k-3>0$.

With $b=b_k$ fixed, comparison against (3) gives $\log b-h(\lambda)=O_k(\log n/n)$. On the probability simplex, the curvature of $u\log u$ is $(\log e)/u\ge\log e$. Tangency at $u=1/b$ therefore yields $\log b-h(\lambda)\ge(\log e)\sum_i(\lambda_i-1/b)^2/2$. This proves the stated spacing estimate and the eventual isolation of each double.
