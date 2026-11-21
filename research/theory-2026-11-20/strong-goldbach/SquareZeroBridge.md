# An unrepresented large multiple of six forces a square-zero cubic killed by x₃

Let G be the binary Goldbach ring on all genuine odd primes, over an arbitrary field. For each large odd s divisible by 3 write m₁,m₂ for the monomial classes of the two [central giants](CubicGiant.md), in their respective residue signs modulo 3. These classes are defined in the full weight-s ring; they might already coincide there. Unconditionally,

    x₃(m₁−m₂)=0,      (m₁−m₂)²=0   in G.                         (1)

If N=s−3 is not a sum of two odd primes then m₁,m₂ are DISTINCT, hence f=m₁−m₂ is an actual nonzero square-zero cubic annihilated by the specified smallest-prime variable. In particular reducedness of the full ring (or merely exclusion of square-zero differences of just these giant cubics) would imply binary Goldbach for every sufficiently large multiple of six. Independently, injectivity of the indicated x₃ multiplication on their span would suffice. These are conditional implications, not a proof of reducedness, regularity, or binary Goldbach. Domainhood is stronger than reducedness. The proof applies in characteristic two as well.

## A direct x₃ bridge in three quartic moves

Write all primes in the following chart:
    a,b,c=s−a−b;     p,q=3+a−p;     b′,u=b+p−b′,d=b′+c−3.
They implement the path
    (3,a,b,c) → (p,q,b,c) → (u,q,b′,c) → (3,u,q,d).
Require a,b,b′≡1 and p≡2 mod3 so that a,b,c are all 1 and u,q,d all 2. Central positivity is uniform: independently restrict a/s,b/s,p/s,b′/s to fixed sufficiently small boxes around 0.45,0.275,0.225,0.275 respectively. Then c/s≈0.275, q/s≈0.225, u/s≈0.225, d/s≈0.55, all inside [1/8,5/8]. Normalized as eight variable forms in coordinates (a,b,p,b′), the linear parts are pairwise nonproportional (including c, q, u and d). Impose the four mod-3 conditions by substitution. At 2 take all odd. At every ℓ≥5 choose a≠0, b outside {0,s−a}, p outside {0,3+a}, b′ outside {0,b+p,3−c}. These choices work for all s mod ℓ. At all but finitely many primes the normalized local factors are 1+O(ℓ^(−2)) uniformly by pairwise independence, so the weighted main term is ≫s⁴ uniformly. The finite-complexity [Tao–Teräväinen theorem 1.6](https://doi.org/10.4171/JEMS/1404) allows this O(s) intercept and fixed coefficients/box with a uniform o(s⁴) error. Proper powers cost O(s^(7/2) log^O(1)s) by fixing any one affine form.

Ensure the two endpoint triples are in the central giants: their non-giant central prime label sets total O_D(s/log^D s) for every D, uniformly by CubicGiant.md. Prescribing a bad value of any one of a,b,c,u,q,d leaves O(s³) possible integer quadruples (all forms have a nonzero coefficient), weighted at most log⁸(O(s)); choose D>9 and subtract. Thus there is a genuine path between the classes x₃m₁ and x₃m₂; it does not require a prime pair summing to s−3.

## Uniform one-carrier catalysis and the square

The one-prime catalyst counting argument has the following uniformity useful here. For any two prime triples A,B of total s, all but o(s/log s) primes t∈[s/8,5s/8] satisfy x_t(m_A−m_B)=0. The o term is independent of the choice of the two triples and of s. More generally fix the tuple length d and fix positive c,C; one has the same statement for t∈[c s,C s] and endpoint lists of total s. We give the uniformity details since the density-one statement for FIXED endpoint lists does not alone imply this moving-endpoint assertion.

Use the three stages and finite schedules of OnePrimeCatalyst.md, separating t modulo 3. In the independent coordinates (t,U₁,…,U_d, each C_j, W₁,…,W_d), take the following common product box:
    t∈[c s,C s],   U_i∈[h s,1.1h s],   C_j∈[0.4h s,0.45h s],
    W_i∈[h s/(100d),h s/(50d)],      h=c/(100d).
Ignore harmless rounding to integers. Then R_i≥c s−1.1d h s, and U_{d+1}=t+s−ΣU_i ≥s+(c−1.1dh)s. The triple-conversion heads X,Y never include U_{d+1}; whether Z is small or terminal, D=3+Z−C_j is positive and every V_i is ≥0.39h s for large s. Every F_i=Σ_{j=0}^iV_j−Σ_{j=1}^iW_j is therefore positive of order s, as is each S_i=t+Q_i−ΣW_j. Trivial total-size bounds put every variable label ≤O_{c,C,d}(s). The remaining-variable section volume is a fixed positive constant times s^m, independent of the actual endpoints and of t in this whole interval.

There are only finitely many possible coefficient matrices for fixed d (including orders and conversions), independent of endpoint values. The one-copy and duplicated-t-fiber two-copy linear parts remain pairwise nonproportional, and the small-prime nonvanishing construction in OnePrimeCatalyst.md works for every reduced t class and all endpoint offsets. When a W-class is fixed, each finite conditional factor k_w(r) is bounded below uniformly over endpoints by a constant depending only on d,w: there are finitely many residue data and each admits at least one tuple. The uniform TT estimates (coefficients fixed, intercepts O(s)), upper/lower uniform large-prime tails, and prime-power slicing bounds therefore give, in each reduced class,
    P(bad | t≡r mod W) ≤ O_d(1/w)+o_{w,d,c,C}(1)
uniformly in the endpoint lists. Let s→∞ then w→∞, and use the fixed-ratio comparability of log t and log s. This proves the moving-endpoint version without interchanging the quantifiers silently.

Fix A and B from the two central giants at weight s. For f=m_A−m_B, each giant contains ≫s/log s prime labels and the same uniform bad-t set has o(s/log s) members. Pick t₁ in the first giant and t₂ in the second with x_{t_i}f=0. Each giant's class has a representative divisible by its chosen variable: that label belongs to a hyperedge of its connected component, and any two hyperedges in the component are linked by shared-label moves. Hence m₁ f=m₂ f=0 in G and f²=0. In fact every central giant monomial class in the fixed weight kills every cubic toric difference in that weight by this argument, whether or not the endpoints of that difference belong to giants.

If N=s−3 is unrepresented, no triple of s contains 3. Every triple of s then has its three labels all of the same sign modulo 3. Distinct signs cannot be linked by one shared-label move, hence not by any path. The two component basis vectors of the prime binary-move ring are linearly independent over every field (Nelson Proposition 2.5); in characteristic two as elsewhere their difference is not zero. This proves the nonzero assertion in (1).

## A decisive control against a generic radicality shortcut: delete only the genuine prime 7

On A=P_odd ∖ {7}, with no upper cutoff at all, the cubic binomial g=x₃² x₁₇−x₅²x₁₃ is nonzero of square zero. Put U=(3,3,17) and V=(5,5,13). The pair 3+3 is uniquely represented, and 3+17=20 has only 3+17 on A (the full-support alternative 7+13 is absent). Thus U is isolated; no later prime can change this, since every tuple of total 23 uses primes ≤17. V is a distinct valid tuple. Here is a single path of six-label states, containing 2U, U+V and 2V, where plus denotes concatenation:
    3 3 3 3 17 17
    3 3 3 3  5 29
    3 3 3 5 13 19
    3 3 5 5 13 17    (U+V)
    3 3 3 5 13 19
    3 3 5 5 11 19
    3 5 5 5 11 17
    3 5 5 5  5 23
    5 5 5 5 13 13.
Each line differs by a single equal-pair move on A. Thus all three products become the same monomial class, giving g²=0 in every characteristic although g≠0. This persistent example uses actual prime labels and exact arithmetic, retains relative density one, and even changes the prime set by only one omission, but it is NOT a nonradicality example for the full ring: restoring 7 repairs U's isolation (indeed U→(3,7,13)→(5,5,13)). A general claim that imposing every available equal-pair binomial makes a radical ideal is false. The genuinely unthinned case remains unsettled.

[Exact diagram and finite controls](check_squarezero_bridge.py) are checked with `python3 -O check_squarezero_bridge.py`. For the prior algebraic setup and questions see [Nelson’s Proposition 2.5, Question 8.1 and Appendix B](https://arxiv.org/html/2611.14580v2); the generic full-ring radicality or regularity required for the implication remains unproved here.
