# Counting connected prime supports of bounded degree

## 1. Statements

Let L(n)=⌊log₂ n⌋+1. For each L let G_L be a simple undirected graph on the positive rational primes, and suppose its maximum degree is ≤K(1+L)^d, with K fixed and d≥0 fixed and real. Put
    A_G(X) = #{2≤n≤X : ω(n)≥2 and the distinct prime divisors of n
                         induce a connected subgraph of G_{L(n)}}.
The exponents in n are unrestricted. In particular n with just one support prime is *excluded*. Otherwise all primes would enter irrespective of graph.

**Extremal theorem.** With α=max(1/2,d/(1+d)), all such families satisfy A_G(X)≤X^{α+o(1)}, uniformly for fixed K,d. For every d there is a family with A_G(X)=X^{α+o(1)}. At the exponent the upper estimate actually is
    A_G(X) ≪ X^α (1+T)^{O(1)} exp(O((1+T)^min(d,1)/log(2+T))),
    T=1+⌊log₂ X⌋.
Constants can depend on K,d. For the sharpness claim the implicit constant in the degree bound is not prescribed.

**Arithmetic theorem.** Let H_L join p≠q when |p−q|≤L^c. For each integer c≥1,
    A_H(X)=X^{c/(1+c)+o(1)} .
The lower construction for c≥2 in fact works for all fixed real c≥21/19; c=1 has a separate proof. No equality for the full open interval 1<c<21/19, nor an assertion about twin primes, is needed or claimed. When c=0, A_H(X) counts exactly the integers 2^a3^b≤X with a,b≥1 and is asymptotic to (log X)^2/(2 log(2) log(3)), where log without a subscript denotes the natural logarithm.

More generally if S_L consists of O((1+L)^b) rational slopes m≥1, and p<q are joined for |q−mp|≤L^c with any such m, c,b≥0, the upper theorem applies with d=b+c: for each m a fixed vertex has O(1+L^c) possible prime neighbors in the two orders, since the inverse interval has length at most 2L^c too. No matching lower bound is asserted for a particular arbitrary slope collection.

## 2. Weighted forest upper bound

Fix X large, T as above, and treat each length L≤T separately. Use the bound Δ=K(1+T)^d for this one graph. Do not take the union of graphs at different L. We can increase K so Δ≥1. Set σ=α<1 and Y=(2+8Δ)^{1/σ}. Use the Dirichlet weight n^(−σ); a bound B for the total weight for this stratum and n≤X bounds its unweighted count by X^σ B. For each vertex p the weight of arbitrary positive multiplicity is w(p)=1/(p^σ−1).

Distinguish the small vertices p≤Y. For a fixed ordered set of t specified root vertices, sum over all plane forests attached to them in which every other vertex is >Y, is joined to its parent in the graph, and receives positive multiplicity. Vertex labels and powers of the t roots are not charged in this attachment sum. The unrestricted attachment weight is bounded above by C(z)^t where
    z=Δ/(Y^σ−1)≤1/8,       C(z)=1+z C(z)^2≤2 .
Indeed each new vertex with its multiplicity has total weight at most Δ/(Y^σ−1), conditional on its parent's label. One may even allow repeated labels; this only enlarges the sum over encodings, with each duplicate occurrence independently charged. A plane rooted tree with its fixed root uncharged has ordinary generating series C(z) counting nonroot vertices: its ordered list of children gives C=1/(1−zC) with C(0)=1. Independent root slots give C^t. This is just the standard Catalan generating series, not a bound asserting independence of actual prime factors.

If small vertices occur in the support of a counted integer, designate *all* of them as roots, sorted numerically. Every other vertex can attach to a neighbor one step nearer the root set in graph distance within the induced support; ordering each collection of children gives a plane forest covering the support. Edges among different rooted branches need not be encoded. For fixed nonempty small support S this bounds the total weight by C(z)^|S| ∏_{p∈S}w(p). Each counted integer has at least one representation of exactly its weight, and labels and multiplicities determine the integer, so overcounting poses no problem. Summing over all S (even adding empty) gives
    ∏_{p≤Y} (1+C(z)/(p^σ−1)) ≤ exp(O_σ(1+Y^{1−σ}/log(2+Y))).
For this last step use log(1+u)≤u, 1/(p^σ−1)≪_σ p^(−σ), and the Chebyshev bound π(t)≪t/log(2+t) with partial summation. Smooth-part multiplicities have not been dropped: taking only one power for each small vertex would go in the wrong direction.

If all support vertices exceed Y, choose as roots the smallest one p and any one of its true neighboring support vertices q. Such a q exists by connectedness and ω(n)≥2. Then q>p, p≤√X, and there are ≤Δ possibilities for q. Charge both full multiplicities; w(p)w(q)≪_σ p^(−2σ). Every remaining vertex has a path to the two-root set, so the attachment bound gives for this case at most
    O_σ(C(z)^2 Δ Σ_{p≤√X} p^(−2σ)).
The endpoint sum is O(log(2+log X)) for σ=1/2 by partial summation, O_σ(1) when σ>1/2. Keeping p≤√X is important at the endpoint; summing p^(−1) over all primes is invalid. For Δ=O((1+T)^d), the positive scale Y^{1−σ} is O((1+T)^min(d,1)) since d(1−α)/α equals d when d≤1 and 1 when d≥1. For fixed d>0 log(2+Y) is comparable to log(2+T) for the chosen degree majorant; for d=0 the whole Euler product is constant. Multiplying by X^σ and summing ≤T strata proves the stated upper bound. At no stage does the arbitrary choice of graph cost another factor of T in its degree.

## 3. Extremal graph families for every real d

For 0≤d≤1, a single graph that matches p_{2i−1} to p_{2i}, the primes in increasing order, has degree one. Each full pair up to √X produces a different semiprime ≤X, and PNT gives ≫√X/log X pairs. This proves the matching logarithmic exponent. It does not make an assertion about bounded *numerical* prime gaps.

Now fix d>1 and at length L join primes whose prime indices have positive distance at most ⌊L^d⌋. The maximum degree is ≤2L^d. For a large integer k let M=⌊k^{d+1}⌋, and consider the M primes with indices M+1 through 2M. Partition those indices into consecutive blocks of length W=⌊k^d √log k⌋ (the final block can be shorter), and use the first vertex of each block as an anchor. There are J=⌈M/W⌉=o(k) anchors. Keep all anchors and any k distinct nonanchors. Every resulting squarefree product has
    (d+1+o(1)) k log k = log n,
uniformly, since PNT gives p_j=(1+o(1))j log j and all the indices are in [M,2M]. In particular L(n)^d>2W eventually. Consecutive anchors are one block apart, and every chosen vertex is in the block of its anchor. Hence the support is connected in the graph for the product's *actual* length. Distinct subsets yield distinct integers, at least
    binom(M−J,k) ≥ ((M−J)/k)^k = exp((d+o(1)) k log k).
The standard product formula yields the displayed binomial bound. For a given X and fixed 0<η<1 choose k=⌊(1−η) log X/((d+1)log log X)⌋. All products then fit below X, yielding lower logarithmic exponent ≥(1−η)d/(d+1); let η decrease to zero. This proves sharpness for all X, not just a sparse subsequence.

## 4. Unit slope: ordinary numerical gaps

For unit slopes the upper theorem gives exponent max(1/2,c/(1+c)). At c=1 let u=√X/2 and split [u,2u] into bins of width at most W=⌊2log₂ u⌋, using (1+o(1))u/W bins. PNT counts (1+o(1))u/log u primes, whereas the bin count is (log(2)/2+o(1))u/log u. The total number of unordered same-bin pairs is at least the number of primes minus the number of bins (binom(t,2)≥t−1). Thus ≫√X/log X distinct products are obtained. Each product n lies in [u²,X], so L(n)≥W; every pair meets the required additive gap.

For real c≥21/19, in particular every integer c≥2, let u=k^{c+1}, W=k^c√log k, and split [u,2u] into J=⌈u/W⌉ equal bins of length between W/2 and W, disregarding harmless endpoints via half-open bins. Every bin contains a prime when k is large. Indeed Baker–Harman–Pintz gives one in [v−v^0.525,v] for any sufficiently large v; take v one unit inside the right end, and note (2u)^0.525=o(W) since 0.525(c+1)≤c and there is a √log k cushion. Choose one prime in each bin as a fixed anchor; J=o(k). By PNT there are M=(1+o(1))u/log u primes in the entire interval. Add any k distinct nonanchors. All chosen consecutive vertices in numerical order have gaps at most 2W. For these products log n=(c+1+o(1)) k log k and L(n)^c>2W eventually. The count is at least
    binom(M−J,k) ≥ exp((c+o(1)) k log k).
With k chosen as in §3 with c in place of d this gives lower exponent c/(1+c) for all X. PNT alone does not place an anchor in *each* such bin; the short-interval result supplies precisely this step.

At c=0 the only two distinct primes at distance ≤1 are 2 and 3, so the allowed integers have the form stated in §1. Counting positive integer pairs below a straight line a log(2)+b log(3)≤log X gives its triangle area plus O(log X), proving the formula. All these conclusions concern counting, with no method for recovering a factor from an input.
