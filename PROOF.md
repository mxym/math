# Low moments do not identify a pairing of a known prime set

Let P be a set of 2k distinct primes. A pairing is a perfect matching of P. Replace each matched pair {p,q} by the integer pq, yielding a set of k pairwise coprime squarefree semiprimes. Its product is N=product(P), a squarefree integer independent of the matching. For a pairing M write
```
s_j(M) = sum over {p,q} in M of (pq)^j.
```

**Theorem.** For each integer r>=1 and each epsilon>0, there exist k with r+2<=k<=8r^2 and infinitely many choices of P for which there are two pairings with no common edge and identical s_1,...,s_r. For each example, all 2k distinct primes can be taken from a single prime arithmetic progression, and the ratio of the largest to the smallest semiprime across both pairings is less than 1+epsilon. Their two block sets are disjoint. In particular, for every k>=8 there are examples with exactly k blocks per pairing for which the first floor(sqrt(k/8)) moments do not identify the grouping; the latter statement allows shared blocks through padding.

The hidden object is a matching, not the prime factorization of N. Nonuniqueness holds even if P itself is provided as part of the observed data. The observations consist of P, N and the low moments; the hidden matching is not determined by them. This is not a computational lower bound for finding a matching, and not an information-theoretic or computational lower bound on integer factorization.

## 1. A classical distinct-set moment bound

Put K=2r-2 and s=K(K+1)/2+1. For fixed K and large integer X there are binom(X,s)=Theta_s(X^s) different s-element subsets of {1,...,X}. A subset's vector of power sums of degrees 1,...,K takes at most
```
product_{h=1}^K (s X^h+1) = O_K(X^(K(K+1)/2))
```
values, since its h-th sum is a nonnegative integer at most s X^h. Thus two distinct s-element subsets share the same vector. For K=0 the signature is empty and this argument just chooses two distinct singletons. Remove their common intersection and denote the remaining disjoint sets by A and B. They have the same cardinality s' with 1<=s'<=s; degree zero agrees because the cardinalities agree. Hence for every polynomial H over any characteristic-zero field with degree at most K,
```
sum_{j in A} H(j) = sum_{j in B} H(j).             (1)
```
The counting device is a classical Prouhet-Tarry-Escott bound. In particular, it uses subsets with distinct entries, not multisets that might reuse a future prime.

## 2. A four-vertex identity with multiplicative conservation

For an index j take four formal elements t,t+D,t+2D,t+3D with t=A0+4jD, where A0 and D are indeterminates. The two local perfect matchings of the index offsets are
```
U = {{0,1},{2,3}},   V = {{0,2},{1,3}}.
```
Their lists of pair products are respectively
```
(t^2+Dt, t^2+5Dt+6D^2),
(t^2+2Dt, t^2+4Dt+3D^2).
```
The product of the two entries is the product of the same four elements in both cases. The difference Delta_h(j) of their h-th power sums is a polynomial of degree at most 2h-2 in j: viewing the expression first in t, the two degree-2h coefficients are both 2, and the two degree-(2h-1) coefficients are both 6hD. Their subtraction cancels both top degrees, and the substitution t=A0+4jD does not increase the remaining degree. This also holds for h=1, when the difference is the constant 3D^2. No edge belongs to both U and V.

Make one such cell for each j in A union B, using offsets 4j through 4j+3 in a single progression. These cells are disjoint. In the first global matching use U on A and V on B. In the second use V on A and U on B. Every vertex is used exactly once in either matching. For each h<=r their profile difference is
```
sum_{j in A} Delta_h(j) - sum_{j in B} Delta_h(j) = 0
```
by (1), since 2h-2<=K. This is a formal identity in A0,D; the common product holds cell by cell. No edge is shared, since the two local choices differ in every used cell. Both matchings have k=4s' blocks, so k<=4((2r-2)(2r-1)/2+1)<=8r^2.

## 3. Specialization to a single set of odd primes

Let J be the largest of all used offsets 4j+3. Fix a positive integer H so large that (1+J/H)^2<1+epsilon; H may also be taken arbitrarily large. The Green–Tao theorem supplies a nonconstant increasing prime arithmetic progression
```
a, a+d, ..., a+(H+J)d,       a>=2, d>=1.
```
Set A0=a+Hd and D=d in the formal identities. All used vertices are distinct primes, and they are odd since H can be chosen positive, so none is the first term 2. They all lie between A0 and A0+Jd, whose ratio is at most 1+J/H. Thus all block products across both matchings have ratio at most (1+J/H)^2, strictly below 1+epsilon. This is a tail-of-an-AP argument and requires no small-relative-span conclusion from the Green–Tao theorem itself.

Within each list the semiprime blocks are pairwise coprime and their product is the same squarefree N on both sides. The two lists are also disjoint from each other as *sets of block values*: equality of two products of distinct primes forces identical unordered edges, which were excluded. This does not mean opposite-list blocks are pairwise coprime across the two lists; they use the same prime support. Since H may be taken arbitrarily large with fixed A,B and A0>=H+2, the integers N cannot lie in a finite set.

## 4. Cardinality and the observation model

The first j power sums determine the first j elementary symmetric functions by Newton identities over Q. For k blocks, if the first k-1 power sums and the product are supplied, all k coefficients of their monic root polynomial are known. The block set is then unique. Our two different sets with equal product and first r moments therefore satisfy k>=r+2. Conversely, the construction above shows a lower bound of order sqrt(k) on the required number of initial moments for a uniform reconstruction theorem in this observation model. More precisely, for any specified k>=8 take r=floor(sqrt(k/8)). The constructed number of blocks is at most k. If it is smaller than k, pad both pairings with the same pairs of fresh prime vertices at new offsets beyond J. Choose the sufficiently long prime progression only after adding those offsets, so the same relative upper bound remains valid. This gives an exact k-block example; the stronger no-shared-block statement concerns the unpadded construction.

Equivalently, appending all symmetric polynomial measurements of total degree at most r does not break these examples: by the fundamental theorem of symmetric polynomials in its graded form, those measurements are polynomials in the elementary symmetric functions of index at most r. Our claim does not cover arbitrary high-degree statistics, even if their outputs are short. We append the exact product as a separate observable of degree k. As P, N and these observations can all be identical while the matching differs, no universal deterministic inverse exists for this data, and randomization cannot identify both choices with success greater than one-half on each when the only input is identical. One can still output one *compatible* matching or both; existence and search complexity are not at issue. In particular the true prime factors of N are unique.

## 5. Small exact example

Take eight prime terms p_i=199+210i, 0<=i<8. The matchings
```
{05,12,36,47} and {03,14,27,56}
```
have no common edge. Their block sets are
```
{248551,253171,1209511,1734091}
{164971,424951,1033111,1822291}.
```
Both have first sum 3445324, second sum 4595861610244 and product 131980928240562546234721. Their first moment equality follows from their common sum of i*j over edges, 48. Their second moment equality follows additionally from the common values of sum (i+j)i*j = 476 and sum (i*j)^2 = 1112: the remaining coefficients follow from the common vertex set and sum i*j. This small four-block example attains r=k-2, the largest possible r for a nontrivial collision, and is an illustration separate from the asymptotic proof.
