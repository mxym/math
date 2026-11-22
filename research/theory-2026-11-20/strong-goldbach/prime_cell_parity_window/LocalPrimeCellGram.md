# Hereditary odd Goldbach cells in a prescribed short window

Use the **full** set of odd primes in each summand class; the midpoint primes below select classes, not a truncation of the pairs being counted. Let T be a large integer, 2≤q<h≤T/4 integers and W=[T−h,T]. Call a reduced class a modulo q occupied if it contains a prime p with h/4≤T−2p≤h/3. On any chosen subset U of the occupied classes draw a successful edge between distinct a,b if, for some N in W, the number of unordered prime pairs N=p+r in these two classes is odd.

**Local theorem.** There is an absolute constant C such that every independent set has size at most
$$
 D=C T (\log h)(\log\log h)/h .
$$
Here h and T are sufficiently large. A finite version of the proof uses only the actual occupancies, without assuming primes in short intervals. For m=|U|, there are at least m(m/D−1)/2 successful edges, and at least m/D−1 **distinct** certified centers (a negative lower bound is vacuous). In particular the theorem applies after arbitrarily deleting occupied classes, including selecting them before inspecting any pair counts.

Uniformly for 100 T^{0.525}≤h≤T/4 and 2≤q<h, taking all occupied classes gives ≫q/log T vertices. Once qh/[T(log T)(log h)(loglog h)] tends to infinity, the corresponding number of certified centers is
$$
 \gg qh/[T(\log T)(\log h)(\log\log h)].
$$
For instance take h=⌈100 T^{0.525}⌉ and q=⌊T^{1/2}⌋: every such prescribed window has ≫T^{0.025}/[(log T)^2 loglog T] distinct centers certified by odd full-cell counts. The modulus need not be prime. Here a fixed residue cell potentially contributes at about h/q distinct positions in the window, and its calculation at a position is not restricted to the short window for either summand. This is not a conclusion at a specified N, nor oddness of the uncolored count. Ordinary existence in a window of this size already follows from midpoint primes; it is not the new conclusion.

## One local Hankel block

Work over F₂. Put L=⌊h/2⌋, and let F_a(z) be the odd-prime indicator series in class a modulo q. Set
$$
 w_j=[z^{T-j}]F_a(z)^2.
$$
For 0≤j≤2L this is 1 just when T−j is twice a prime of the class. In particular for an occupied class there is a hit s₀∈[h/4,h/3]. Its (L+1)-square Hankel block (w_{i+j}) for 0≤i,j≤L has rank r>h/[100 log h loglog h] for h large enough.

Indeed r≥1. Suppose r≤h/[100 log h loglog h]; in particular r<L/6. The first r+1 columns are dependent, so there are coefficients, not all zero, with Σ_{j=a}^b c_j w_{i+j}=0 for all 0≤i≤L; a,b are the first and last nonzero coefficient indices and 0≤a≤b≤r. If a=b this would force w_{s₀}=0. Otherwise the order d=b−a recurrence extends the d values starting at a uniquely to a bi-infinite sequence f because c_a=c_b=1. It agrees with w on [a,L+b] and in particular on [r,L]. Translates of f span dimension at most d. Every step-ℓ subsequence satisfies a reversible degree-d recurrence (Cayley–Hamilton on the ℓ-th power of the invertible shift), so d consecutive zeros on that progression force it to vanish there for all integer indices.

For each odd prime ℓ≤Y=⌊L/(3r)⌋, the progression j≡T mod ℓ has at least d consecutive entries in [r,L]. They are all zero: the only possible hit would satisfy T−j=2ℓ, excluded by h≤T/4 and ℓ≤L/(3r). Hence f vanishes on that entire residue class. Write s=π(Y)−1. For each ℓ_j choose b_j≡s₀−T mod ℓ_j and b_j≡0 mod the remaining primes. For every subset A let b_A be its subset sum. The 2^s-square matrix f(s₀+b_A−b_B) has diagonal 1 and entry 0 whenever B is not a subset of A. It is triangular in an order extending inclusion, hence has rank 2^s, but evaluates translates of f and so has rank ≤d≤r. As Y≥(16+o(1))log h loglog h under the alleged upper bound on r, the prime number theorem gives 2^s>h, a contradiction.

## From blocks to pair counts

In F₂[z]/(z^{T+1}) use the bilinear form (G,J)↦[z^T]GJ; its ambient dimension is T+1. For each vertex a take the L+1 vectors z^i F_a, truncated modulo z^{T+1}. Entries of their mutual Gram matrix between blocks a,b are the coefficients of F_a F_b at T−i−j in W. For distinct classes these coefficients count unordered true pairs modulo two with no diagonal or factor-of-two issue. For an independent set all off-diagonal blocks therefore vanish, while each self-block has the rank just proved. The sum of their ranks is at most T+1; this proves the hereditary bound.

For completeness the graph on m designated vertices has independence number at least m²/(m+2e) if it has e edges: a random ordering gives an independent set of vertices preceding every neighbor, of expected size Σ_v(1+deg v)^{-1}≥m²/(m+2e). Thus e≥m(m/D−1)/2. At any one center the successful class pairs it can witness form a matching (the partner is N−a mod q), of size ≤m/2. This gives the asserted number of centers.

## Prime input and comparison

[Baker, Harman and Pintz, *The difference between consecutive primes, II*, proof of Theorem 1, p. 562](https://www.cs.umd.edu/~gasarch/BLOGPAPERS/BakerHarmanPintz.pdf) give an actual lower bound ≫x^{0.525}/log x for π(x+x^{0.525})−π(x), not just one prime. The midpoint interval [T/2−h/6,T/2−h/8] has length h/24. For h≥100T^{0.525} it contains ≫h/T^{0.525} disjoint intervals of the type in this bound: partition from its left endpoint into blocks of length T^{0.525} and take the BHP interval starting at each block's left endpoint. Their start points are ≍T. This gives ≫h/log T midpoint primes. Each class modulo q occurs ≤1+h/(24q) times, and all these primes exceed q since q<h≤T/4. This proves the occupancy estimate.

[Halupczok, *Goldbach's problem with primes in arithmetic progressions and in short intervals*](https://jtnb.centre-mersenne.org/item/10.5802/jtnb.839.pdf) studies related almost-all solvability and weighted estimates; these do not evaluate parity in the prescribed cells. [Chirre and Hagen (August 2026)](https://doi.org/10.1007/s40993-026-00767-6) studies occurrence of an ordinary Goldbach number under RH in a much shorter window, not parity. See also the preceding broad-window [three-cell result](Proof.md), whose modulus and quantifiers differ. The November 2026 [polynomial-value exceptional set result of Althöfer–Chen–Perelli–Pintz](https://arxiv.org/abs/2611.09386) concerns existence for almost all polynomial indices, not the hereditary parity question here. No priority claim or claim about eliminating an individual exception is made.
