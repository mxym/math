# A local lower bound on every component of the prime support

## 1. Statements

Write L(n)=1+⌊log₂ n⌋. Let G_L be an arbitrary simple undirected graph on the positive rational primes. For a fixed integer s≥2 let A_s(X) count 2≤n≤X such that every connected component induced by its distinct prime divisors in G_{L(n)} has at least s vertices. Different components can have any sizes ≥s and there is no bound on their number. Multiplicities in n are unrestricted. All logarithms without subscript are natural logarithms.

**I. Degree extremum.** If the maximum degree is ≤K(1+L)^d for fixed K and real d≥0, then
    A_s(X) ≤ X^{α_s+o(1)},      α_s=max(1/s,d/(1+d)).
The bound is uniform for fixed K,d,s. For each d and s the logarithmic exponent is attained by some graph family of this degree order. Extremal means best possible as an upper exponent over families, not that every family has many such integers.

**II. Ordinary numerical windows.** For a radius function H(L)≥0 join distinct primes of difference ≤H(L). If H(L)→∞ and log H(L)/log L→d≥0, then
    A_s(X)=X^{α_s+o(1)} .
This includes all H(L)=L^c for real c>0 and also arbitrarily slow divergence with exponent zero. No monotonicity of H is required. At fixed H=1 the assertion is not applicable: for s=2 just products 2^a3^b, a,b≥1, qualify; for s≥3 the set is empty.

**III. Fixed ordinary width.** For fixed H≥0 let B_{H,s}(t) count primes p≤t for which there exist primes p=p₁<p₂<⋯<p_s with p_{i+1}−p_i≤H. Set δ=limsup_{t→∞} log(1+B_{H,s}(t))/log t. For the fixed graph of numerical width H one has
    limsup_{X→∞} log(1+A_s(X))/log X = δ/s .
In particular at H=2 and s=2 this is one half the upper logarithmic counting exponent of twin-prime starts (indeed B_{2,2}(t) adds the one start 2, for t≥2, to the count of lower members of twin-prime pairs). This identity does not determine that exponent, imply the twin-prime conjecture, or prove an asymptotic formula for twin primes.

## 2. Weighted count over components of an arbitrary graph

Take α_s<σ<1, T=1+⌊log₂X⌋, Δ=max(1,K(1+T)^d), and Y=(2+8Δ)^{1/σ}. Treat one bit length at a time, with this Δ as a uniform upper bound on that graph only. Summing length strata at the end costs ≤T; taking their graph union would incorrectly change the degree bound. Use n^(−σ) weights and w(p)=1/(p^σ−1) for a selected vertex's arbitrary positive multiplicity.

For t specified ordered root labels, all further vertices in an attached plane forest are required to be >Y. The sum over attachments, not charging the roots, is at most C(z)^t, where z=Δ/(Y^σ−1)≤1/8 and C=1+zC², C(0)=1. This counts uncharged roots with an ordered list of children; at each child, summing its possible labels and positive multiplicities costs at most z given its parent. Repetitions in an encoding can be allowed for an upper bound. In particular C(z)≤2.

Divide each support into the union of components touching some prime ≤Y and the components lying wholly above Y. For the first group take *all* small primes of the support as roots. Assign every other vertex in these components to a neighbor nearer that root set, and order the children. If S is the set of small roots, the encoding charges their full positive multiplicities by ∏_{p∈S}w(p) and the attachments by C(z)^|S|. Summing S gives a bound
    ∏_{p≤Y}(1+C(z)w(p)) ≤ exp(O_σ(1+Y^{1−σ})),
by the sum of p^(−σ), even replacing the primes by all integers ≥2. We may drop the component-size restriction in this part.

For a wholly large component, take its smallest prime p as a distinguished root. Since the component has at least s vertices, it contains a rooted connected seed of *exactly s distinct vertices* containing p: start at p and extend a tree one incident vertex at a time. For fixed s, at most O_s(Δ^{s−1}) rooted, tree-encoded seeds are possible, using the finite number of ordered tree shapes and ≤Δ choices along each new edge. In an actual seed all its vertices q≥p, so the combined positive-multiplicity weight is at most O_{σ,s}(p^(−sσ)). Take the seed vertices as root slots for remaining attachments. Thus the sum of weights of all wholly large component encodings with minimum p is bounded by
    D_p = O_{σ,s}(Δ^{s−1} p^(−sσ) C(z)^s).
Enlargements used in this bound cannot remove any actual component.

Crucially there can be *many* wholly large components. Their distinct minimum labels form a set, so the product ∏_{p>Y}(1+D_p) majorizes all choices, instead of paying for only one component. Relaxing disjointness between tentative encodings is harmless: actual configurations still occur, and each genuine encoding with powers determines its integer. Multiply by the small-root product. As sσ>1,
    Σ_{p>Y} D_p ≪_{s,σ} Δ^{s−1}Y^{1−sσ} ≪_{s,σ} Y^{1−σ} .
For the first inequality the convergent tail over all integers suffices; the second uses Δ≤Y^σ. Therefore total weight per length is exp(O_{σ,s}(1+Y^{1−σ})). Because d(1−σ)/σ<1 by σ>d/(1+d), this is exp(o(T)). Multiplying by X^σ, summing ≤T strata, taking the upper logarithmic exponent, and then letting σ↓α_s proves I's upper bound. No endpoint convergence of Σ1/p is used.

## 3. The 1/s lower exponent from genuine clusters

For numerical widths H(L)→∞, fix s. Maynard, *Dense clusters of primes in subsets*, Theorem 3.2, gives an absolute c₀>0 so that for fixed y sufficiently large there are ≫u exp(−√log u) integers z∈[u,2u] with at least c₀ log y primes in (z,z+y], for all sufficiently large u. Choose and fix an integer y_s with c₀ log y_s≥s and beyond any absolute lower threshold. No effective numerical value of y_s is required.

Each such interval gives one set of s primes, all within width y_s. Any fixed such set can be chosen for at most y_s+1 integer z: z must be before its least prime and within y_s of its greatest. By unique factorization different sets produce different squarefree products. For a given large X take u=X^{1/s}/3; then all products are ≤(2u+y_s)^s≤X and ≥u^s, so their bit lengths tend to infinity uniformly. Eventually all their H(L)≥y_s. Their supports are cliques on s vertices; their number is X^{1/s−o(1)}. The quantitative lower bound is important: infinitely many bounded clusters without a counting estimate would not justify this exponent. For sufficiently large fixed H≥y_s the same proof applies.

For I at d=0, without any arithmetic closeness requirement, partition consecutive prime *indices* into disjoint blocks of s primes and make each block a clique. This fixed graph has degree s−1. The full blocks with primes ≤X^{1/s} give ≫_s X^{1/s}/log X products by PNT. This also shows why numerical width one and unrestricted constant graph degree must not be confused.

## 4. Dense entropy lower bound without filling every bin

Suppose d>0. Fix 0<ε<min(d/4,1/4) and a large integer k. Take u=k^{1+d−3ε} and W=k^{d−ε}; partition [u,2u] into O(u/W+1)=O(k^{1−2ε}) bins of length at most W. Discard any bin with fewer than s primes. In each surviving bin choose exactly s fixed anchor primes. Both the total number discarded and the number J of anchors are O_s(k^{1−2ε})=o(k); this count does not require a prime in every bin. By PNT the interval has (1+o(1))u/log u primes, so the number M of remaining eligible nonanchors is k^{1+d−3ε+o(1)}. Keep every anchor and choose any k distinct nonanchors. Each product is squarefree, and uniformly
    log n=(1+d−3ε+o(1)) k log k .
In particular L(n) is comparable to k log k. The exponent assumption on H implies H(L(n))≥L(n)^{d−ε/2}>W eventually. Every selected prime therefore belongs to a clique containing at least s anchors (or to that anchor clique itself). Components can merge, which preserves the lower-size restriction; empty bins can separate them freely.

There are binom(M,k)≥(M/k)^k choices, with log count ≥(d−3ε+o(1)) k log k. For any 0<η<1 put k=⌊(1−η)log X/((1+d−3ε)log log X)⌋. All these products then lie below X; taking X to infinity, then η,ε to zero, gives the lower exponent d/(1+d). This is a different construction from a connected scaffold: no short-interval prime theorem is needed for the surviving bins.

To finish II, any H(L)=L^{d+o(1)} graph has degree O((1+L)^{d+ε'}) for each fixed ε'>0. Apply I's upper bound with d+ε', then send ε' to zero. Combine §§3–4; when d=0 use only §3. For I's sharpness at d>0 the ordinary graph with H=L^d itself is a witness attaining the maximum; §3 supplies d=0.

## 5. The fixed-window identity

For fixed H the graph has bounded degree Δ≤2⌊H⌋. The minimum p of any connected support component of size at least s belongs to the set counted by B_{H,s}: in increasing order, successive vertices in an additive interval graph can have no gap >H, else the gap disconnects the component. Conversely each such p yields a different squarefree integer of exactly s factors, at most (p+(s−1)H)^s, satisfying the component condition. This gives the lower limsup δ/s, interpreting the exponent using 1+count when necessary.

For the upper choose any σ with δ/s<σ<1, hence sσ>δ but not necessarily sσ>1. Choose a constant Y large enough for z≤1/8 as in §2. The small-root Euler product is finite. In the wholly large component product it suffices now to sum D_p over starts in B_{H,s} only. Since sσ>δ, dyadic grouping shows Σ_{p a start}p^(−sσ)<∞: for any δ<γ<sσ, the number of starts up to y is O_γ(y^γ). The bounded-degree graph is fixed, and its full sum of eligible n^(−σ) is consequently bounded independently of X. Thus A_s(X)=O_σ(X^σ), proving III on letting σ↓δ/s. For δ=0 the same argument works with every σ>0. Finite products of small-prime powers never create a positive upper logarithmic exponent. No claim is made that the general fixed-width limsup is a limit.
