# The endpoint and log-log-log window for genuine-prime masks

Keep the precise masks and observed data of [the genuine-prime mask theorem](Proof.md), including the complete low-rank composite incidences (not only squarefree ones). Write \(H=\log\log P\) and protect all ranks through \(K_c(P)=\lfloor eH-c\log H\rfloor\), with \(c\) fixed.

* If \(c<1/2\), masks are impossible on a positive proportion of even targets in each sufficiently large dyad, in particular at \(c=0\).
* If \(c>1/2\), the requested two masks exist on all but \(o(X)\) even targets in each dyad \([X,2X]\).
* If \(c>e+1/2\), they exist for every sufficiently large even target.

The exact case \(c=1/2\) and the every-target cutoff below the third bound are not decided here. This only concerns the specified masking data, not the existence of Goldbach representations.

## Upper obstruction from a dyadic average

 Let x be large, L=log x, H=log L. For each odd integer m≤x write m=b d, with b squarefree and d the product of the full prime powers with exponent ≥2. Then d is odd squarefull and Ω(m)=ω(b)+Ω(d). There are O(x^(3/4)) integers represented with d>√x: the number of squarefull integers up to T is O(√T) from the representation u²v³ with v squarefree, and the reciprocal tail above √x is O(x^(−1/4)).

For d≤√x, apply the classical Hardy–Ramanujan Lemma A to squarefree b≤y=x/d. It bounds the count at rank j≥1 by C y(log log y+C)^(j−1)/[(log y)(j−1)!]. The largest term of the tilted Poisson sum (eU)^i/i!, U=log log y+C, is O(exp(eU)/√H) by Stirling. Removing the tilt e^(j−1) and summing a geometric tail yields O(y L^(e−1)e^(−k+Ω(d))/√H) for ranks j≥k−Ω(d). When that lower rank is nonpositive, the same bound holds trivially, including b=1. The factor log y is comparable to L since d≤√x. The odd squarefull sum is finite:

    Σ_d e^Ω(d)/d = ∏_{p≥3} (1+Σ_{a≥2}(e/p)^a) <∞.

Oddness and e<3 are essential here. Thus the total count of odd m≤x with Ω(m)≥k is O(x L^(e−1)e^(−k)/√H+x^(3/4)). At k=eH−c log H+O(1) and c<1/2 this is O(x/[L H^(1/2−c)]). [Hardy–Ramanujan, original Lemma A](https://ramanujan.sirinudi.org/Volumes/published/ram35.html)

For P∈[X,2X], sum the number of central genuine primes p with Ω(P−p)>K_c(P) by writing m=P−p. All m are odd. Across the dyad use the estimate with x=2X and the smallest relevant rank, which differs from e log log(2X)−c log log log(2X) by O(1). Multiplication by the elementary upper bound for π(2X) gives O(X²/[log²X (log log X)^(1/2−c)]). Markov then makes the candidate replacement population o(P/log²P) for all but o(X) centers, uniformly on this good set (take a square root of the factor tending to zero). Intersect with the positive proportion of central Goldbach-rich targets in the published theorem. On these targets, deleting one endpoint per genuine pair costs ≫P/log²P. Equal total mask size and equal counts of preserved low-rank composites would demand at least this many replacement vertices, which are unavailable. Unlike the published t>e proof this step does not need a pointwise high-rank prime upper bound.

## Uniform lower construction

 Keep the published medium prime tag P^.02<g<P^.03, the central interval/residue cells, and the true masks. Split the small markers into disjoint sets of primes, omitting those dividing target P or the cell modulus W:

    S1: [L², exp(L/(100H))],
    S2: (exp(L/(100H)), exp(L/(100 log H))].

Use a fixed endpoint convention. Their conditional reciprocal sums λ_i=Σ_{p∈S_i}1/(p−1) are H−2 log H+O(1) and log H−log log H+O(1), respectively. Excluded primes above L² cost O(1/L). Require exactly k2=floor(e log H) marks from S2 and exactly k1=K_c(P)+1−k2 from S1. Together with g this is a neutral replacement outside the protected rank cut.

For each enforced marker choice, take odd/even lower/upper Bonferroni truncations L_i,U_i for no further marks in its block, at adjacent orders around 12H and 12 log H. To combine the blocks use the pointwise lower L_1 U_2+U_1 L_2−U_1 U_2, not the product of the two lower bounds. This follows from U_i≥1_{E_i}≥L_i and U_i≥0. On each block the next omitted term divided by the exact no-further-mark principal probability is o(1), uniformly in the enforced set, by λ_i^J/J!, Stirling and the same estimate as in the published proof. CRT gives product principal factors because the blocks are disjoint. For sufficiently large P each block uses at most 16H or 16 log H factors, respectively, per modulus. Including g and the polylogarithmic W, all moduli are ≤P^(.35+o(1)). Divisor-bounded coefficients and ordinary maximal-prefix prime BV give arbitrary logarithmic error exactly as in the published argument. One g label has positive constant harmonic mass and each actual row has O(1) g labels.

Distinct-marker symmetric sums give (1+o(1)) exp(−λ1−λ2) λ1^k1 λ2^k2/(k1! k2!), as repeated independent draws have probability o(1). The first block's log probability is −H+(c−e+3/2)log H+O(1+log²H/H). The second block gives −log H+O(log log H). The combined neutral pool in a cell therefore has size at least
     
    X_I L^(−1) H^(c−e+1/2+o(1)),   X_I=|I|/[φ(W)L].

The original prime-pair endpoint upper is O(X_I 𝔖(P)(W/φ(W))/L). The standard uniform bounds 𝔖(P)≪H and W/φ(W)≪log H follow by Mertens (for 𝔖 split the target factors at L²). Thus the neutral pool dominates when c>e+1/2, and the same cellwise matching gives both masks.

## Lower construction on almost all targets

Use the same two marker blocks and counts, but lower the bottom of S1 from L² to H². For large P this is still above every prime dividing the cell modulus W, whose largest prime is ≤C H. Uniformly for all but o(X) targets, the sum of 1/(p−1) over p≥H² dividing P is at most 1. Indeed its dyadic expectation is O(Σ_{p≥H²}p^−2)=O(H^−2), since d|P has frequency O(1/d), using d≤2X. Also 𝔖(P)≤(log H)^2 on all but o(X) targets by its bounded dyadic first moment. That moment follows by expanding the product over odd primes dividing P as the squarefree divisor weights ∏_{p|d}1/(p−2), whose reciprocally weighted series converges. Compare the published mask proof for this singular series.

The typical reciprocal means are now λ1=H−log H−log log H+O(1), λ2=log H−log log H+O(1). The same finite Bonferroni orders and BV moduli apply. Repeated independent prime draws in the symmetric sums are negligible since k_i/λ_i stays bounded and Σ_{p≥H²}1/(p−2)²=o(1). With k2=floor(e log H) and k1=K_c+1−k2, the log probabilities are respectively −H+(c+1/2)log H+O(log log H) and −log H+O(log log H). Their product gives a neutral cell pool ≫X_I L^−1 H^(c−1/2+o(1)). On the typical targets the actual endpoint upper is O(X_I L^−1 (log H)^3), since W/φ(W)≪log H. This is smaller for every fixed c>1/2. The exact matching argument then gives the same masks. The uniform every-target construction with c>e+1/2 still holds and does not rely on these exceptional-set bounds. At c=1/2 the comparison is undecided.
