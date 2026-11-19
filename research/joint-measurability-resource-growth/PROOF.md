# Exponential outcome/dimension cost of universal joint-measurability structures

**AI-assisted, internally checked research note; not externally peer reviewed.** Finite, labeled settings; exact ordinary POVM compatibility and arbitrary finite parent measurements. All resource lower bounds below are worst case (also typical under a specified middle-layer distribution), not claims about every graph or about the optimal exponential rates. The counting input is an existing theorem.

## 1. Counting theorem

Let L(n,d,q) be the number of distinct joint-measurability complexes on [n] that are realizable by n POVMs on C^d with at most q outcomes in each POVM. Allow repeated settings for an upper bound; whether or not these are excluded leaves the lower-bound implications intact. Pad shorter individual alphabets to [q] with zero effects (removing zero-probability coordinates recovers the original joint). Write

    p = n q d²,       m = 1 + p + d q^n,       D = max(2,d).

There is an **absolute** C such that for all n,d,q≥1,

    log₂ L(n,d,q) ≤ (p+1)² log₂ m + C p² log₂ D.                 (1)

No numerical value of C, or of the threshold n implicit below, is claimed.

**A dual certificate.** For nonempty S⊆[n], let K_S be the cone of all unnormalized PSD marginals:

    B_(i,a) = Σ_{x∈[q]^S:x_i=a} G_x  (i∈S, a∈[q]),   G_x ≥ 0.

Its ambient vector space is the real direct sum of Hermitian matrix spaces with trace inner product. This cone is convex and closed. To check closedness, take a convergent sequence of marginal arrays and choose any representing parent for each. For one fixed i∈S, summing its marginals over a gives T=Σ_x G_x. Along the sequence the trace of T is bounded; every PSD G_x has operator norm at most tr(T). The finitely many matrices thus admit a common convergent subsequence. Its positive limit has the desired marginals. For normalized given settings M, membership in K_S is precisely unconditioned joint measurability: summing over outcomes for any one i forces Σ_x G_x=I.

The dual cone consists of Hermitian tuples F_(i,a) with Σ_{i∈S} F_(i,x_i)≥0 for every deterministic tuple x. Indeed the trace pairing on any parent is Σ_x tr(G_x Σ_i F_(i,x_i)); choosing one G_x at a time tests exactly positive semidefiniteness. Closed-cone separation now proves that S is incompatible iff there exists a tuple F on all n labels such that

    F_(i,a)=0 for every i outside S and every a,
    Σ_{i=1}^n F_(i,x_i) ≥ 0 for every x∈[q]^n,
    Σ_{i,a} tr(F_(i,a) M_(i,a)) < 0.                         (2)

Extension by zeros and restriction justify the common q^n set of positivity tests; repetitions of the same restricted tuple are harmless. The strict separation is separation from a closed convex cone in a finite real inner product space; it does not require a Slater condition or positive-definite measurement effects. The empty set is always compatible and does not require a cone.

**A single list of polynomials.** Use real coordinates for all Hermitian matrices (d diagonal and d(d−1) off-diagonal real/imaginary coordinates), so both F and M use p coordinates. No tracelessness, projectivity or real-matrix assumption. We will count over all real M coordinates, a superset of the valid normalized measurements, so no normalization inequalities need be added. Make a polynomial list in (M,F) consisting of:

1. the p individual real coordinates of F;
2. the one real trace pairing in (2), of total degree at most two;
3. for each of the q^n tuples x, the d non-leading coefficients of det(t I+Σ_i F_(i,x_i)) as a polynomial in t.

For Hermitian A these coefficients are real polynomials of total degree ≤d in its real parameters. Their nonnegativity is equivalent to A≥0: in one direction it follows by expanding the product over nonnegative eigenvalues. In the other, nonnegative coefficients with leading coefficient 1 make the value strictly positive for t>0, while a negative eigenvalue would give a strictly positive real root. This uses d rather than 2^d tests per tuple and works with singular A. The list has m entries of degrees ≤D.

For a fixed M, retain the **set of full joint ternary sign vectors** of this entire list as F varies. It is one fiber-wise set, not just the set of signs attained separately by each polynomial. For each S, inspect whether this set contains a vector with all coordinate signs outside S zero, all characteristic-coefficient signs nonnegative, and the unique pairing sign negative. By (2) this answers precisely the incompatibility query on S. Thus the one fiber set determines the whole labeled complex; it is unnecessary to create one formula/polynomial list for every S.

**Existing quantitative input.** [P. Hrubeš, CCC 2024, Appendix A, Eq. (4), printed p. 13:11](https://users.math.cas.cz/~hrubes/PDFs/HardSub.pdf) ([proceedings](https://doi.org/10.4230/LIPIcs.CCC.2024.13)) states the parametrized sign-fiber bound from Basu–Pollack–Roy, *Algorithms in Real Algebraic Geometry*, Thm. 14.16. For m polynomials of degree at most D in k₁ fixed/free and k₂ varying/fiber coordinates, the number of **different sets of realizable signs in the fibers** is bounded by

    m^((k₁+1)(k₂+1)) · D^(O(k₁)O(k₂)).

The constants in the two big-O factors are absolute, independent of m,D,k₁,k₂. This is a product of powers, not a power of a power. The paper's following page also uses the looser (Dm)^(O(k₁)O(k₂)). Apply it with k₁=k₂=p. Taking binary logarithms proves (1). The cited theorem counts entire fiber-sign families and includes zero signs; an ordinary Warren bound just on signs of unquantified polynomials would not suffice.

## 2. Consequences and quantifiers

For n≥4 let k=⌊n/2⌋ and b_n=binom(n,k). Start with every subset smaller than k; select any subcollection of the k-sets and include exactly those, with no larger faces. This gives exactly 2^(b_n) different valid labeled complexes, each containing all vertices. We call their uniform distribution the *random middle-layer complex*. We only need the classical bound b_n≥c₀ 2^n/√n for an absolute c₀>0 (e.g. Stirling).

**Simultaneous resource tradeoff.** There exist absolute c>0,n₀ such that for every n≥n₀ some n-vertex complex has the following property: every realization of that *same* complex in any positive integer dimension d with any outcome budget q satisfies

    q d² ≥ c 2^(n/2) / n^(9/4).                                  (3)

Indeed for 1≤B≤2^n take the union of all pattern families with qd²≤B. There are at most B² integer pairs, p≤nB, D≤2^n, and log₂m≤C₁ n² for some absolute C₁ (as q≤2^n,d≤2^n). By (1), the binary logarithm of the union's size is at most 2log₂B+C₂ n⁴ B² for an absolute C₂. Put B=c 2^(n/2)n^(−9/4). Then C₂n⁴B²=C₂c² 2^n/√n. Choose c>0 with C₂c²<c₀/4 and n large enough that 2log₂ B≤b_n/4 and B≥1. The number of realizable patterns at this cost is at most 2^(b_n/2); some middle-layer complex lies outside the union. In fact its random middle-layer probability of **any** realization at this cost is at most 2^(−b_n/2). Labels do not weaken the conclusion: relabeling permutes the realizable class and preserves d,q.

**Fixed d≥2.** If R_d(n) is the least q such that *every* n-vertex complex can be realized in dimension d with ≤q outcomes per setting, (3) gives R_d(n) ≥ (c/d²)2^(n/2)n^(−9/4) for all sufficiently large n. In particular liminf log₂R_d(n)/n≥1/2. Finiteness follows from the [variable-alphabet qubit construction](https://github.com/mxym/math/pull/118) with q≤2 binom(n,⌊n/2⌋)+1 (Sperner's bound on facets); for d>2 extend each setting by the same deterministic measurement on the orthogonal summand. Parents of faces extend block-diagonally, and compressing any joint parent to the qubit block preserves its marginals, so nonfaces remain incompatible.

**Fixed q≥2.** Let D_q(n) be the least d permitting every n-vertex complex with at most q outcomes per setting in that dimension. A sharper polynomial prefactor follows directly from (1). For d≤2^n and fixed q, log₂m=O_q(n), log₂D=O(n), so log₂L(n,d,q)≤C_q n³ d⁴. Universality requires log₂L≥b_n; hence

    D_q(n) ≥ c_q 2^(n/4) n^(−7/8),     liminf (log₂ D_q(n))/n ≥ 1/4.   (4)

The bound already holds if D_q(n)>2^n. Finiteness at q=2 is prior work: assemble a binary Specker scenario for each inclusion-minimal nonface in its own direct-sum block, with all other vertices deterministic on that block, as in [Kunjwal–Heunen–Fritz 2014](https://arxiv.org/abs/1311.5948). Using one qubit for each minimal nonface is the [Andrejić–Kunjwal 2020 improvement](https://arxiv.org/pdf/2003.00785), see their discussion immediately after Corollary 8. Take a deterministic block if there are no nonfaces, and pad to a common upper dimension if desired. If every vertex must be assigned a different measurement, append one common commuting two-dimensional block: for vertex i its first binary effect is diag(0,tᵢ), where the tᵢ are distinct in (0,1/2), and its other effect is the complement. All these tags are jointly measurable in the same basis; they distinguish the measurements even up to relabeling without changing the realized complex or exponential upper bound. Thus the standard unconditional upper resources are exponential too; the exponent constants in (3)–(4) are lower bounds only, and are not asserted to be optimal. For d=1 or q=1 all measurements are simultaneously compatible, so the separate universal parameters above are only defined in the stated nontrivial regimes.
