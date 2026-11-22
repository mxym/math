# Odd Goldbach counts in one of three prescribed residue cells

Write P_a(z) over F₂ for the series with coefficient 1 at the **odd primes** in the reduced class a mod q and 0 elsewhere. For distinct classes a,b the coefficient of P_a P_b at N is the parity of the number of unordered representations N=p+r in those two classes. The classes distinguish the order, so there is neither a diagonal term nor a factor of two.

**Theorem.** There is an absolute η>0 with the following property. For all sufficiently large integers X, put
$$
 H=\left\lfloor X/(100\log X\log\log X)\right\rfloor.
$$
For every q≤X^η and every three distinct reduced classes mod q, at least one of the three pairwise cells has an **odd** number of genuine prime pairs at some even integer H<N≤X. In particular the result applies along arbitrary moving moduli q=X^{o(1)}. Neither the successful cell nor N is prescribed. This does not give the parity of the uncolored count or solve the binary problem at each target.

## A supply of individual primes (not pairs)

Uniformly in q≤X^η and its reduced classes, each class contains a prime in (H/8,H/4] and one in (X/4,X/3]. For fixed moduli the ordinary prime number theorem in progressions suffices. For the moving statement use [Thorner and Zaman, Theorem 1.1 and (1.2), (1.7)](https://arxiv.org/pdf/2108.10878), published in *Mathematische Zeitschrift* 306 (2024). Here are the details from the authors' v2 statement. Take x=H/4, h=x/2, or x=X/3, h=x/4. Their sum is over **primes** with weight log p. Its main term is λh/φ(q), with λ=1 if there is no exceptional zero; otherwise λ≥(1/8)min(1,(1−β₁)log x), and 1−β₁≫q^{-1/2} effectively. Thus the main term is ≫x q^{-3/2}. With fixed ε=1/100 their threshold is x^{θ+ε} with θ≤32/37. Take η sufficiently small that 1−3η>32/37+ε, using q≤x^{2η} for large X. For fixed h/x the relative error is bounded by C_ε exp(−c_ε log x/[log q+O(1)+(log x)^{2/5}(loglog x)^{1/5}]); reducing η once more makes this less than 1/2 uniformly. This uses their exceptional-zero factor rather than subtracting two separate lower bounds.

## From three vanished products to a reversible recurrence

Denote the three series by F₁,F₂,F₃. Suppose all three pairwise coefficients vanish in (H,X]. Let A,B,C be the truncations through H of F₂F₃,F₁F₂,F₁F₃ respectively. They equal their full products modulo z^{X+1}. Each is nonzero: the first exponent is the sum of the least primes in the two named cells, attained uniquely and ≤H/2 by the early prime supply. Frobenius in characteristic two gives
$$
 A F₁(z²)\equiv BC\pmod {z^{X+1}}.
$$
Let w=ord_z(A)≤H. Then z^w divides BC as a polynomial. Dividing gives A₀ F₁(z²)≡P mod z^{X+1−w}, where A₀(0)=1, its highest coefficient is 1, d=deg A₀≤H and deg P≤2H. If d=0, all coefficients of F₁(z²) in [2H+1,X−H] vanish. This is impossible at 2t for the late prime t of the first class.

If d>0, the coefficients of F₁(z²) satisfy the homogeneous order-d recurrence with denominator A₀ from index 2H+1 through X−w. Using as initial values its d coefficients ending at 2H, extend them to a bi-infinite sequence f by that recurrence; extension in either direction is unique since both endpoint coefficients are 1. On I=[2H+1,X−H] the sequence f agrees with F₁(z²) coefficientwise. All translates of f belong to the d-dimensional solution space over F₂. The shift on states is an invertible d-by-d matrix S; for any ℓ≥1 every step-ℓ subsequence satisfies the reversible degree-d characteristic polynomial of S^ℓ. Therefore d consecutive zero terms of a step-ℓ subsequence imply it is zero everywhere in both directions.

## A CRT rank test on the actual primes

Set Y=⌊X/(4H)⌋, and take all s odd primes ℓ≤Y. Throughout I the coefficient at every multiple of ℓ is zero: the only possible nonzero such index in F₁(z²) is 2ℓ, and 2ℓ<2H+1. The interval I contains at least d consecutive multiples in the ℓ-progression, since its length is X−3H and ℓ≤X/(4H), d≤H. Consequently f(n)=0 at **every** integer multiple of each of these s primes.

Let n₀=2t, with t a late first-class prime. Then n₀ lies in I and f(n₀)=1. For each ℓ_j choose an integer u_j congruent to n₀ modulo ℓ_j and to zero modulo every other ℓ_i in this list. Write u_A=Σ_{j∈A}u_j. The matrix
$$
 (f(n₀+u_A-u_B))_{A,B\subseteq\{1,\ldots,s\}}
$$
has diagonal 1; whenever B is not a subset of A, the argument is zero modulo some ℓ_j with j∈B minus A. In an order extending inclusion this matrix is triangular, hence has rank 2^s. But its columns evaluate translates of the same reversible sequence, so rank≤d≤H. This is impossible: Y∼25 log X loglog X, so by the prime number theorem s∼25 log X and 2^s>X for large X. This proves the theorem.

## How many cells? Which congruence of centers?

Among any m≥3 distinct reduced classes modulo the same q, draw an edge if the cell has **no** odd witness in this window. The theorem makes this graph triangle-free. Mantel's bound gives at least binom(m,2)−⌊m²/4⌋ successful cells. A given N can witness at most ⌊m/2⌋ of these, since a class has just one possible partner N−a mod q. Thus at least m/2−1 **distinct** centers have a certificate for some cell. To keep centers in a fixed progression, take all selected summand classes to project to the same prescribed reduced class a mod b, with b dividing q; then N≡2a mod b. This does not cover arbitrary b and arbitrary nonunit a by the same reduction.

For fixed q the graph of cells which have only finitely many odd witnesses is in fact bipartite. If there were any fixed odd cycle, the nonzero pair products on that cycle would be polynomials (finite support). Taking their alternating product and quotient shows the square of one vertex series is rational. Its coefficient sequence is then eventually periodic, and so is the original series by taking the even subsequence. This contradicts infinitude and zero density of the primes in its reduced class. This observation concerns fixed cells, not the parity of the total count.

## Optional Gaussian mod-8 realization without prime-power error

Let K be the least integer ≥5 with K log K≥log X, and W=8 times the product of the odd primes ≤K. Then log W=O(log X/loglog X) by Chebyshev. Pick a prime Q≡1 mod W. By [Linnik's theorem, e.g. Xylouris](https://arxiv.org/abs/0906.2749) one may take Q=X^{o(1)}; alternatively fix δ=η/4 and choose Q in (X^δ,2X^δ] in that progression, by the prime-in-progression input above at scale 2X^δ since W=X^{o(1)}. These are two different allowed choices. No proper positive power b^e≤X, b,e≥2, is a primitive root mod Q. A prime divisor of e at most K divides Q−1. If all its prime divisors exceed K, then e>K and b≤X^{1/K}≤K; quadratic reciprocity and Q≡1 mod W make every prime ≤K a quadratic residue, including 2. In either case the class is not primitive (also not so if Q divides b). The integer 1 is not a primitive root.

For each primitive residue u mod Q choose the class a_u≡1 mod 4, a_u≡u mod Q. Let h*(n) be the number of primitive Gaussian representations x²+y²=n divided by 4. For odd n>1 it vanishes if any prime factor is inert (3 mod 4). If all factors split, h*(n)=2^{ω(n)}: primitivity forces the full exponent of each split prime onto exactly one of its two conjugates, independently, with four units. Thus within these classes up to X, h*(n) is 2 mod 4 exactly at genuine primes and 0 mod 4 otherwise. No prime power, endpoint 1, even integer or zero survives as a false hit. Write H*_u for its series restricted to positive n in the class. For distinct u,v the coefficient of H*_u H*_v at N≤X is 4 times the unordered prime-pair count modulo 8. For a union of classes used on both legs the *ordered* convolution instead requires subtracting the exact diagonal h*(N/2)^2 when eligible; then dividing by 8 gives the parity of the unordered **distinct** pairs. A prime diagonal itself is directly recognized.

Applying the theorem to the m=φ(Q−1) classes a_u makes an actual Gaussian coefficient nonzero modulo 8 in one of each triangle's cells, **without** presupposing a representation. The count above gives ≥m/2−1 distinct centers. In the polynomial-size choice of Q this is X^{δ−o(1)}; standard elementary bounds give φ(n)=n^{1−o(1)}. The centers are 2 mod 4. One may instead refine by a common fixed reduced class compatible with 1 mod 4 using the Chinese remainder theorem; the enlarged modulus still meets the theorem's range. These assertions neither identify a preassigned center nor evaluate an unrestricted two-leg theta series through a single modular form.

**Comparison.** [D. A. Goldston, Linnik's theorem on Goldbach numbers in short intervals](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/F73ED944781B38B244B14ADD72AD7B24/S001708950000937Xa.pdf) studies the presence of Goldbach numbers in intervals, not parity of the count in specified summand cells. Almost-all results or unsigned lower bounds do not determine that parity. Existence of infinitely many represented even integers is of course not new. No general priority claim is made.

The [local Gram refinement](LocalPrimeCellGram.md) proves a hereditary bound for odd full-cell counts in much shorter prescribed windows, using actual midpoint primes to select the classes. It also does not give a prime pair at a specified single target.
