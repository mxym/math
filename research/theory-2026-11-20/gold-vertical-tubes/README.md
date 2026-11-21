# The largest binary Sidon set in a vertically thickened Gold graph

Let q=2^m, with m even, E=GF(q), 1≤k<m, gcd(k,m)=1, and e=2^k+1. For an r-dimensional binary subspace W of E define the full tube

    T_W = { (x, x^e+w) : x in E, w in W }.

The ambient group E×E is additive. A Sidon set has distinct sums for its unordered pairs of distinct elements. Write M(W) for the largest size of an arbitrary Sidon subset of T_W. No hypothesis of functionality, transversality, invariance, or proximity to the original graph is made.

**Theorem.**
1. Always M(W)≥q, and M(0)=q.
2. Let W-perp be the binary orthogonal complement for the absolute trace pairing. If W-perp contains a nonzero e-th power, then M(W)≤q+floor((2^r−1)/4). This hypothesis holds for every W if 2r<m.
3. If m≥3r+1 then **M(W)=q for every W**. In particular every fixed-rank vertical thickening eventually has the original graph as a maximum Sidon subset.
4. Regardless of the preceding threshold, every rank-one tube has exact maximum q for even m≥4, and **every rank-two tube has exact maximum q for even m≥6**. For rank three the universal bound is q+1 for even m≥8, and the universal exact maximum is q for even m≥10.

The rank-two cutoff m=6 is sharp: with m=4 one of the tubes contains **18** points, two more than the Gold graph. In fact the 35 rank-two spaces in m=4 give 25 maxima of 16 and 10 maxima of 18. This theorem is about an infinite family of supports; it does not determine the unrestricted Sidon number in dimension 12 or in general.

## 1. Derivative and the four-input packing

For a≠0, writing x=az gives

    (x+a)^e+x^e = a^e (1+z^(2^k)+z).

The last linearized difference has kernel GF(2), as gcd(k,m)=1. Its image has size q/2 and absolute trace zero, hence is exactly the absolute trace-zero hyperplane. In particular the Gold graph itself is Sidon: with a fixed nonzero first-coordinate difference each derivative value has just two ordered preimages, the endpoints of a unique unordered input pair. This proves part 1.

Call a nonzero input difference a *constrained direction* if a^(−e)∈W-perp. At that input difference every pair sum from the entire tube has second coordinate in the same affine hyperplane of size q/2, since W lies in the direction space a^e·ker(Tr). Thus a Sidon subset has at most q/2 unordered pairs with first-coordinate difference a. At first-coordinate difference zero it has at most v−1 pairs, v=2^r, because each such nonzero vertical difference lies in W.

If W-perp contains z^e with z≠0, put a=z^(-1). The three nonzero elements of U=a·GF(4) are all constrained: m even gives GF(4)⊂E and k must be odd, so 3 divides e. Partition the selected points by the q/4 cosets of U of their first coordinates. Within a block an unordered pair has first difference either zero or one of those three directions. The total number of such pairs is therefore at most 3q/2+v−1. If a block has b points, then binom(b,2)≥4b−10 for every nonnegative integer b, since the difference is (b−4)(b−5)/2. Summing shows any M selected points generate at least 4M−10q/4 such pairs. Hence 4(M−q)≤v−1, proving the conditional assertion of part 2.

For a binary basis w_1,...,w_r of W consider the r quadratic Boolean functions Q_i(z)=Tr(w_i z^e) on m bits. They are quadratic since z↦z^(2^k) is binary linear and field multiplication is binary bilinear. The indicator of their common zero set is ∏(1+Q_i). When 2r<m its unique multilinear polynomial over GF(2) has degree <m, so its sum over all binary words is zero modulo two (every proper squarefree monomial has even weight). There is already the zero solution, hence also a nonzero solution z with z^e∈W-perp. This elementary parity argument proves the unconditional part 2. It gives the asserted exact rank-one and rank-two results by taking the integer floor.

## 2. Many constrained directions force exactness

It remains to prove part 3. Suppose M=q+t with t≥1, let n_x count the selected outputs at input x, and put d_x=n_x−1. Let H be the number of missing inputs; these are exactly the d_x=−1. Let P be the sum of all positive d_x. Then P−H=t, and

    P ≤ sum_x binom(n_x,2) ≤ v−1.

The last inequality is the distinct vertical-difference bound. Let B denote the set of constrained directions. For a∈B the q/2 unordered input pairs {x,x+a} contribute ∑ n_x n_(x+a) Sidon pairs, at most q/2 in total. On subtracting the constant terms, the linear terms sum to t, because every input belongs to exactly one of the q/2 pairs. It follows that

    sum over unordered {x,x+a} of d_x d_(x+a) ≤ −t.

The total magnitude of *negative* products across every nonzero direction together is precisely HP: each unordered pair of a hole and a positive input belongs to exactly one direction. Therefore

    t |B| ≤ HP = P(P−t) ≤ (v−1)(v−1−t) ≤ (v−1)(v−2).

For v=1 part 1 already settles the result. For v≥2 we bound |B| arithmetically. Inversion identifies B with the nonzero z satisfying Tr(w z^e)=0 for every w∈W. Orthogonality over W gives

    |B|+1 = (q + sum_(0≠w∈W) sum_z (−1)^Tr(w z^e)) / v.

For nonzero w the quadratic form Q(z)=Tr(w z^e) has polar radical of size at most four. Indeed h is in the radical exactly when w h^(2^k)+(wh)^(2^(m−k))=0. Raising to the 2^k power and taking h≠0 gives h^(2^(2k)−1)=w^(1−2^k). The multiplicative power-map kernel has size 2^gcd(2k,m)−1=3. Squaring the character sum and summing on h as a difference of the two arguments gives

    (sum_z (−1)^Q(z))² = q sum_(h in rad Q) (−1)^Q(h) ≤ 4q.

Consequently |B|≥q/v−2(1−1/v)√q−1. For m≥3r+1 we have q≥2v³. The bound increases as a function of √q once √q>v−1. At q=2v³ its excess over (v−1)(v−2) equals

    v(√v−√2)² + v + 2√(2v) − 3 > 0.

This contradicts the necessary hole–positive-input bound. No Sidon subset larger than q exists.

## 3. Small sharpness example, fully reproducible

For m=4 use the polynomial basis for GF(16) defined by X^4+X+1 and encode (x,y) as x+16y. For e=3, W={0,1,8,9}, the following 18 elements of T_W have 153 distinct unordered pair sums:

    0 1 2 99 68 181 6 40 249 234 219 140 61 14 207 16 129 150

The controls list every binary rank-two W≤GF(16). Of the 35 choices, 25 have W-perp meeting the five nonzero cubes and hence exact maximum 16 by part 2. The other ten form one orbit of output scaling by a cube and squaring; on the Gold graph these are induced by (x,y)↦(a x,a³ y) and (x,y)↦(x²,y²). Thus all ten admit the displayed 18-set.

For the upper bound on the latter ten, write π:E→E/W. For each nonzero input difference a, the derivative of π(x³) takes each of its four output values on precisely two unordered input pairs. In fact the trace hyperplane of the Gold derivative plus W fills E because a^(−3)∉W-perp, and each value of the original derivative has two ordered preimages. If 19 tube points were Sidon, the vertical difference bound P≤3 and P−H=3 would force H=0,P=3, with no triple in any fiber (a triple costs three vertical pairs for only two excess points). Thus exactly three distinct inputs would be doubled. Choose two of them. For their common input difference their four selected point pairs have the same *projected* output difference. A second, disjoint unordered input pair shares that projected difference and is occupied at both ends, giving a fifth point pair. Only four actual output differences lie over any projected value, contradiction. A larger putative set contains a 19-subset. This proves the exact m=4 table; e=9 is equivalent to e=3 under output Frobenius.

## Reproducibility and context

Run `python3 -O verify.py` (Python standard library only). The infinite theorem is proved above without numerical assumptions. The script checks the small witness, every m=4 rank-two space, scalar/Frobenius orbit coverage, and the finite-field derivative identities and signed-sum bounds in m=4,6. No classification of APN functions or external code census is needed.

Known APN maximality concerns **sets containing the whole graph**, rather than arbitrary sets inside its vertical thickening: see [Carlet, On APN functions whose graphs are maximal (2023)](https://eprint.iacr.org/2023/621), and [Mihaila–Thornburgh, On lower bounds for the distances between APN functions (2026)](https://doi.org/10.1007/s12095-026-00908-9). For Sidon and vectorial-nonlinearity background see [Nagy, JCTA (2025)](https://doi.org/10.1016/j.jcta.2024.106001). The distinct 0-extendability question for Gold maps is considered in [Gold functions and switched cube functions are not 0-extendable in dimension n>5](https://doi.org/10.1007/s10623-022-01111-6). A search through 2026-11-21, including the August 2026 [Carlet–Thornburgh quadratic APN paper](https://arxiv.org/abs/2608.23888) and September [Thornburgh's unrestricted dimension 4k+3 bound](https://arxiv.org/abs/2609.27731), did not identify the same thickened-support maximum theorem. This comparison is not a guarantee of bibliographic priority.
