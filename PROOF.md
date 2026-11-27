# Explicit weak-privacy sharing at threshold n−1

## 1. Model and claims

For n≥3, a dealer shares s∈{0,1}, producing a word in the product of n finite alphabets. Any n−1 shares must recover s for every dealer tape and both secrets. For any A with |A|≤n−2 and any share tuple x_A, let P_s^A(x_A) denote its probability when the shared secret is s. For 0<p≤1 the requirement is the pair of pointwise inequalities

    P_0^A(x_A) ≥ p P_1^A(x_A),     P_1^A(x_A) ≥ p P_0^A(x_A).

This is p-weak privacy as in Beimel–Ishai–Kushilevitz–Li Definition 2.2. Share size is the maximum log₂ of a party alphabet size. The case n=2 is trivial, as each party may receive the secret with no nonempty unauthorized set. In what follows n≥3. Party identities and fixed public parameters are used; no anonymity is required.

**Theorem 1 (construction).** Let 0<η≤1/4, put L₀=⌈log₂(2n/η)⌉, and choose q to be the smallest power of two at least 16 η^(−2) L₀. With

    L=ceil((1/2−η)q),  U=floor((1/2+η)q),

there is a perfectly correct scheme sharing one bit at threshold n−1, with log₂ q bits per share and exactly n log₂ q fair dealer bits, satisfying p-weak privacy for

    p = (L/U) · floor(q²/U)/ceil(q²/L).                          (1)

The public description can be constructed deterministically in time polynomial in n, q, and the representation length of a rational η. Dealer sampling and reconstruction are also deterministic polynomial-time computations given the specified dealer bits. The privacy parameter in (1) is at least

    ((1−2η)/(1+2η))² · (1−1/q)/(1+1/q) ≥ 1−9η.                  (2)

In particular any fixed p_target<1 can be achieved with O(log log n) bits per share by taking η=(1−p_target)/9 or a smaller rational tolerance. Taking η=min(1/4,1/ceil(log₂(2n))) achieves p≥1−O(1/log n) and still O(log log n) bits. A second sampling rule with η=1/4 uses exactly (n−1) log₂ q fair bits and guarantees p≥1/12.

**Theorem 2 (converse for arbitrary finite alphabets).** For any p-weakly private, perfectly correct (n−1)-out-of-n scheme for one bit, let q_i≥1 be the size of party i's alphabet and put δ=(1−p)/(1+p). Then

    Σ_i 1/q_i ≤ (1+sqrt(1+4n(n−1)δ²))/2.                         (3)

In particular the maximum alphabet size is at least 2n/(1+sqrt(1+4n(n−1)δ²)). For p=1 this is the known inequality Σ_i 1/q_i≤1; at fixed p<1 it does not rule out constant alphabets.

## 2. Deterministic almost-balanced shifted color tables

Write G=F₂^a additively, where a=log₂ q; identify its elements with a-bit words. We construct tables g_1,…,g_n:G→{0,1} with the following property for every i≠j and every w∈G:

    L ≤ |{u∈G : g_i(u) ≠ g_j(w+u)}| ≤ U.                        (4)

For a fixed prior table g_j and shift w, the distance of a uniformly random candidate table from its translate has law Binomial(q,1/2). Its probability of lying outside [L,U] is at most 2 exp(−2η²q): being outside those integer bounds means a deviation greater than ηq, and the bound follows by applying exponential Markov to the product of cosh(λ/2), with cosh(λ/2)≤exp(λ²/8), or directly by the fair-bit Hoeffding inequality. There are at most (n−1)q constraints for each next table. The expected number of bad constraints is therefore at most 2nq exp(−2η²q)<1. For an explicit check of the last inequality put x=2n/η≥24. We have q<32η^(−2)ceil(log₂ x), ceil(log₂ x)≤x, and n η^(−2)=x²/(4n)≤x²/12, so 2nq<6 x³. Also exp(−2η²q)≤2^(−2η²q)≤x^(−32). This proves the strict bound, including at power-of-two rounding boundaries. We may take the first table to be all zero.

Here is a deterministic construction avoiding a search through all 2^q words. For each next table, assign its q entries in a specified order. At a partial assignment, if r entries are unset and d mismatches to one fixed translated earlier table are already assigned, its contribution to the conditional expected number of bad constraints is the exact value

    2^(−r) · Σ_{0≤j≤r, d+j outside [L,U]} binom(r,j).            (5)

The sum is a rational potential obtained by summing (5) over all earlier tables and all q shifts. On assigning the next bit, its two possible future potentials average to the current one, by conditioning on that fair bit; pick a smaller one (use fixed tie breaking). The initial potential is strictly below one. At a complete table its value is the integer number of bad constraints, where every bad constraint contributes one, so it is zero. In particular each earlier table and every translation is checked; testing only zero shifts would not suffice. Hamming distance is symmetric, and translation is an involution in G, so both orders of the pair in (4) are covered.

All numerators in (5) have at most q+1 bits before adding constraints. Binomial prefix sums or a simple loop evaluate them exactly; a complete table of such counts for r,d in the appropriate ranges costs polynomial time in q. The q successive decisions compare sums over at most (n−1)q terms of common denominator, so the whole public description has polynomial-time construction in n and q. Alternatively straight table search has size 2^q, polynomial in n for any fixed η, but (5) also makes the displayed η tending to zero efficient.

## 3. Shares, all erasure positions, and exact sampling

The full words of possible shares lie in

    C = {x∈G^n : Σ_i x_i = 0}.

Define the bit c(x)=⊕_i g_i(x_i). The scheme for secret s only produces x∈C of color s. Every n−1 subset reconstructs exactly: first compute the unique missing group element from the parity constraint, then compute c. With n shares either compute c directly or ignore one share. The claim is for every choice of genuine dealer tape; no probability of failure is allowed or incurred.

Fix an arbitrary largest unauthorized view A with |A|=n−2, and an arbitrary tuple x_A, including tuples not resulting from a particular run. Let i,j be the two missing indices. Their possible coordinates in C are exactly (u,w+u), u∈G, where w=Σ_{k∈A}x_k; characteristic two handles the sign. The word color is the known XOR of fixed table outputs, plus g_i(u)⊕g_j(w+u). By (4) the number of completions of color 1 before the known flip is in [L,U]. The number of completions of color 0 is also in [L,U], since q−U=L and q−L=U. This holds for every pair and every fixed tuple.

The dealer picks the first n−2 coordinates independently uniformly in G. It then lists the m valid completions to the final two coordinates with color s, in a fixed order. The preceding paragraph proves L≤m≤U, so the list is nonempty and can be scanned in q trials. Draw an independent W uniformly in {0,…,q²−1}, and choose completion number W mod m (indexing from zero). This is **not** assumed to be a uniform draw from the m entries. Each completion has either floor(q²/m) or ceil(q²/m) preimages. Consequently every valid full word for secret s has probability in the interval

    q^(−(n−2)) · [floor(q²/U)/q², ceil(q²/L)/q²].               (6)

Every invalid full word has probability zero. Since q is a power of two, the first n−2 draws consume (n−2)log₂ q fair bits and the residue draw exactly 2log₂ q bits, with no rejection or extra sampling. The public tables are fixed and carry no per-execution information.

For any largest unauthorized A and tuple x_A, sum (6) over the valid completions for each secret. There are between L and U terms, so for either order of the secrets the ratio of the smaller guaranteed mass to the larger possible mass is at least (1). If A is smaller, extend it to a largest unauthorized A' and sum the pointwise inequalities over all tuples on A' extending x_A. Thus the same p applies to every unauthorized set; the argument checks all maximal views before marginalizing.

To verify (2), each completion draw probability deviates from 1/m by less than 1/q², so it lies between (1−1/q)/m and (1+1/q)/m. Since m lies between (1/2−η)q and (1/2+η)q, summing over the same number bounds for any unauthorized view gives the first expression in (2) directly. It also lower bounds (1): the quantities floor(q²/U)/q² and ceil(q²/L)/q² are at least (1−1/q)/U and at most (1+1/q)/L, respectively, while L/U≥(1/2−η)/(1/2+η). The first squared factor in (2) is at least 1−8η (exact deficit 8η/(1+2η)²); the rounding factor is at least 1−2/q. The deficit of the product is no more than the sum of the two deficits. Since q≥2/η under the chosen parameters, that sum is at most 9η. Finally log₂ q=O(log log n + log(1/η)), by the choice of the next power of two and log₂ log₂(2n/η)≤O(log log n+log(1/η)) in this range. For η=min(1/4,1/ceil(log₂(2n))), q=O((log n)^3). This gives the claimed family with p tending to one.

**Shorter constant-privacy sampler.** Use η=1/4; q is divisible by four, so L=q/4,U=3q/4. Draw W uniformly in {0,…,q−1} instead of {0,…,q²−1}, again selecting the residue modulo m. Each valid completion has a preimage multiplicity in {floor(q/m),ceil(q/m)}⊂[1,4]. Thus valid full-word masses lie in [1,4]q^(−(n−1)). For any largest unauthorized view the secret's mass is at least (q/4)q^(−(n−1)) and at most 4(3q/4)q^(−(n−1)), giving p≥1/12, then every smaller view follows by marginalization. This consumes exactly (n−1)log₂ q fair bits and no samples from an approximately implemented distribution.

## 4. Converse for the general weak-privacy parameter

For any proposed scheme, use the Cartesian product of its actual q_i-symbol alphabets and regard its two full probability mass functions as real functions p_0,p_1 on that product. We use counting-measure inner product Σ_x f(x)g(x) and squared norm Σ_x f(x)²; scaling by the uniform measure would give the same ratios. Put f=p_0−p_1 and g=p_0+p_1. Correctness for even a single fixed authorized set implies that the full secret supports are disjoint; thus g=|f| and ||g||₂=||f||₂>0.

For each i let P_i be the orthogonal projection averaging the i-th coordinate uniformly over its alphabet, with the result extended constantly on that coordinate. The projections commute. For a fiber over all other n−1 shares, correctness says that the nonzero f values are of one sign, since that visible tuple cannot occur for two secrets. Consequently the square of their sum is at least the sum of their squares. With the normalization from the average and the q_i equal extended entries, summing over fibers gives

    ||P_i f||₂² ≥ ||f||₂²/q_i.                                 (7)

For distinct i,j, pointwise p-weak privacy on the other n−2 coordinates implies

    |P_i P_j f| ≤ δ P_i P_j g, where δ=(1−p)/(1+p).

Indeed, if nonnegative masses a,b satisfy a≥pb and b≥pa, then |a−b|≤δ(a+b); this also holds when a=b=0. The averaging divides numerator and denominator by the same q_i q_j. Orthogonal projection is a contraction, so

    ||P_i P_j f||₂² ≤ δ² ||P_i P_j g||₂² ≤ δ² ||f||₂².          (8)

For B⊆[n] form the product orthogonal projection Q_B using P_i on i∈B and I−P_i on i∉B. The Q_B are mutually orthogonal and sum to the identity. Give B probability ||Q_B f||₂²/||f||₂² and write Z=|B|. The one-coordinate and two-coordinate inclusion probabilities are respectively the squared norm ratios in (7) and (8), because summing the corresponding Q_B gives P_i or P_iP_j. Hence

    μ:=E Z ≥ Σ_i 1/q_i,     E[Z(Z−1)] ≤ n(n−1)δ².

The last count sums over ordered i≠j. Since E[Z²]≥μ², we get μ²−μ≤n(n−1)δ²; the positive root is (3). The conclusion applies to unequal alphabet sizes and needs no support or linearity assumption beyond correctness. The exact p=1 specialization recovers the known perfect-privacy bound of Bogdanov–Guo–Komargodski, rather than improving it. In particular a target 1−p≤n^(−c) for fixed c>0 forces Ω(log n) bits for some share. Our polylogarithmic-alphabet construction approaches one more slowly and does not conflict with that implication.

## 5. Scope and boundaries

Theorem 1 answers the one-bit (n−1)-threshold question. It is not a scheme for every high threshold, other access structures, adversarial errors, or perfect privacy. Weak privacy is a pointwise probability-ratio guarantee, not a claim that the distributions are equal.

For comparison, if every party alphabet has at most two symbols, perfect correctness and p>0 are already impossible for n≥3. Choose any supported word of either secret. Weak privacy forces a word of the opposite secret matching it off any designated pair; correctness on n−1 coordinates forces both missing coordinates to change, so the opposite word is the unique double flip in binary alphabets. Three distinct coordinates i,j,k give a contradiction: flipping i,j and then j,k changes secret twice and equals the direct flip of i,k, which changes secret once. Singleton alphabets make the required double flip impossible as well. This small obstruction does not imply nonconstant alphabets.

Within the particular parity-code construction with full color supports and c(x)=⊕_i g_i(x_i), the order log log n cannot be improved. With all other coordinates zero, the missing pair uses w=0, so g_i=g_j or g_i=1−g_j would make that fiber monochromatic. Thus the n local tables must be distinct modulo complementation, so n≤2^(q−1) and log₂ q≥log₂(1+log₂ n). This is a template restriction only. It gives no lower bound of order log log n for arbitrary weakly private schemes at a fixed p<1.
