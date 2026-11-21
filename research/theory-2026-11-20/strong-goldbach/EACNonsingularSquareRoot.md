# At most square-root-many centers have a compact nonsingular prime-factor component

For every function K(X)=o(log log log X), the number of even N≤X admitting a nontrivial [Bożek exceptional autonomous component](https://arxiv.org/abs/1909.09900) of size k≤K(X) with det(I−A)≠0 is **at most X^{1/2+o(1)}**. Here A_{ij}=v_{p_j}(N−p_i) is the exact integral exponent matrix; row degrees and the number of distinct prime factors per row are unrestricted. In particular the estimate applies to every fixed size bound. The little-o in the conclusion allows dependence on K. This counts centers, not labeled tuples or ordinary Goldbach exceptions.

Consequently at most X^{1/2+o(1)} even centers up to X can have a three-label EAC, with no hypotheses on the labels or exponents. More generally outside the indicated set of centers **each** EAC of size ≤K(X) contains two vertex-disjoint directed cycles. Large components and singular compact components in general are not excluded. A center having an EAC can still have a Goldbach representation, as the known examples do; this is not an upper estimate on the exceptional set of the binary Goldbach conjecture.

### 1. From a nonsingular component to a short order certificate

Let m be the smallest label, D=max_i Ω(N−p_i), and e the largest Smith invariant of B=I−A. All labels are odd primes coprime to N and all complementary rows are composite and factor over the labels. Mapping each free generator to its residue in (ℤ/Nℤ)^×/{±1} kills every row of B since each complementary product is N−p_i. Thus
     
    N | m^{2e}−1,      m≤√X,      e≤|det B|≤(1+D)^k,
    D≤log X/log 3,     m^D≤X.                                          (1)

The square of the e-th power removes the sign; an unsquared exponent e cannot generally be used. The size bound on m follows by taking a least factor of any composite row, and m^D≤X follows from a row with D factors, counted with multiplicity. Each row of B has Euclidean norm at most 1+D, giving the determinant bound. These reductions require no prior theorem on the size of the smallest label.

### 2. Counting small divisors of a low-order power minus one

Write L=log X and σ>1/2 fixed. For integers 3≤m≤√X, e≥1 with log(2e)=o((log L)(loglog L)), uniformly in the bounds below, let W=m^{2e}−1. Let π_W(t) count distinct prime factors of W at most real t≥2. Each such r is coprime to m and d=ord_r(m) divides both 2e and r−1 (including d=1 at r=2 if relevant). For a fixed d there are at most d log m/log 2 prime divisors of m^d−1, and at most t/d integers 1+jd≤t with j≥1. Taking their minimum, then their geometric mean, gives
     
    π_W(t) ≤ τ(2e) √(t log m/log 2).                                    (2)

The ordinary bound log τ(v)≪log(3v)/loglog(3v) implies τ(2e)=L^{o(1)} in this range. To see uniformity, split log(2e) at log L: below it the bound is O(log L/loglog L) (with bounded v harmless), and above it divide the assumed o((log L)(loglog L)) by at least loglog L. The ordinary divisor bound itself follows by putting Z=log v: primes ≤√Z contribute O(√Z log Z) to log τ(v), since every exponent is O(Z); the others have total exponent ≤2Z/log Z and contribute at most log 2 per exponent.

By summing the integral σ ∫_r^∞ t^{−σ−1}dt=r^{−σ} for every prime r|W, (2) yields
     
    ∑_{r|W prime} r^{−σ} ≪_σ τ(2e) √log m ≪ L^{1/2+o(1)}.

Since −log(1−r^{−σ})≤r^{−σ}/(1−2^{−σ}), the finite-prime Euler product over r|W, including *arbitrary* powers of these r, is exp(o(L))=X^{o(1)}. Rankin's inequality, or just 1≤(X/n)^σ for n≤X, now gives
     
    #{n≤X : n|W} ≤ X^σ ∏_{r|W prime}(1−r^{−σ})^{-1} ≤ X^{σ+o(1)}.       (3)

This uses the residue-order structure of prime divisors of m^{2e}−1; a divisor bound using just its size is inadequate when e is a large power of log X.

### 3. Low and high complementary multiplicities

Fix an integer T≥2, independent of X. When D≤T, (1) gives e≤(1+T)^{K(X)}=(log L)^{o(1)}. For all m≤√X, ordinary divisor counting suffices in this case: log W≤2e log m≤eL, so by monotonicity of Z/log Z for large Z and the preceding divisor bound,
     
    log τ(W) ≪ 1 + eL/log L = o(L).

Each choice of m,e thus gives at most X^{o(1)} centers. There are ≤√X choices of m and X^{o(1)} of e, so this case contributes ≤X^{1/2+o(1)}.

When D>T, (1) instead gives m≤X^{1/T}. From the uniform bound on D and k follows log(2e)=O(1+K(X)log L)=o((log L)(loglog L)), so (3) applies uniformly; there are only X^{o(1)} possible e. Summing over m,e bounds this case by X^{σ+1/T+o(1)}. To conclude, given any δ>0 first choose a fixed σ>1/2 and T so that σ+1/T<1/2+δ, and only then take X sufficiently large. This proves the claimed exponent. No summation over matrices or components is necessary; multiple certificates for one N merely overcount.

### 4. What singularity forces

If B is singular, take f≠0 real with Af=f. On the strongly connected component a nonnegative f cannot have any zero, since zeros propagate to successors. Nor can it be strictly positive, because a row at its minimum has at least two factors and therefore (Af)_i≥2 min f>f_i. The same holds for nonpositive f. Each vertex where f_i>0 has a successor with positive f; finite iteration supplies a directed cycle there. Likewise the negative support supplies a disjoint cycle. There are no loops, since all labels are coprime to N. Three labels cannot accommodate two vertex-disjoint cycles, proving the unqualified three-label counting conclusion.

[Earlier](EACThreeSubpower.md) fixed-signature finiteness and smallest-label estimates are not needed in this proof; neither is a full-EAC census. The elementary finite checks in `check_eac_order_divisors.py` verify the order partition and its two separate counting bounds, as well as the center certificate in small genuine examples. They do not establish the asymptotic by enumeration.

### Comparison with related work

[Bożek](https://arxiv.org/abs/1909.09900) defines the component, proves its necessity at a hypothetical exception, and reports a bounded census. The [Kelanemer record](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460) also describes directed exponent matrices; only its public abstract was accessible. [The August 2026 v2 survey of Goldbach exceptional sets](https://arxiv.org/abs/2607.27282) counts missing prime-pair representations, not centers with the particular factor-closed structures counted here. Nothing in the present estimate bounds the number of centers with a singular or arbitrarily large component; it does not improve an upper bound on missing representations.
