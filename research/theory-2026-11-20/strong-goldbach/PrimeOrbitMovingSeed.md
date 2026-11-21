# One fixed and one moving independent direction in a prime-factor orbit

Fix an odd prime p, an integer k, a finite set S of rational primes and ε>0. Write N_S=∏_{ℓ∈S}ℓ^{v_ℓ(N)} for the S-part. For all sufficiently large even N with (p,N)=1 and N_S≥N^{1/2+ε}, the following holds.

Let C be a set of at most k distinct odd primes <N−1 coprime to N, with p∈C. For every x∈C require that N−x is composite and all its prime divisors lie in C. Put A_{xy}=v_y(N−x), B=I−A. Then q=min(C∖{p}) exists, q<√N, and the classes of e_p and e_q are linearly independent in ℚ^C/row_ℚ B. In particular the rational nullity of B is at least two and every set meeting all directed cycles in the support of A has at least three labels. Strong connectivity is not required. The threshold for this assertion is not claimed effective.

At a hypothetical Goldbach failure with these size and coprimality conditions, the entire forward prime-factor orbit from the single prescribed seed p has at least six labels (uniformly for all sufficiently large N). This includes, for instance, every sufficiently large dyadic center, taking S={2}. For an orbit larger than a fixed k, no rank conclusion is being asserted. No terminal component is identified, and Goldbach is not decided on this family.

## 1. A relation with unequal coefficient bounds

The composite N−p has a prime divisor at most √(N−p); this is not p since p∤N. Write L=log N and T=L/log q>2. If the two classes are dependent, the rational row space of B contains a nonzero vector supported on them. Take t independent columns J spanning all columns outside {p,q}, then one of the two marked columns increasing the rank, and t+1 rows on which this augmented minor is nonzero. Take the signed maximal minors of J on those rows as coefficients of a row combination (empty minor 1 if t=0). Its coordinates on J vanish, hence so do all outside coordinates. Its selected marked coordinate is nonzero. Entries of J and of the q-column have size O(T), since the corresponding labels are ≥q; entries in the p-column have size O_p(L). Expanding the minors gives a nonzero integral row combination u e_p+h e_q with
     
    |h| ≪_k T^{t+1},       |u| ≪_{p,k} L T^t,       0≤t≤k−2.

Every row of B has multiplicative value −1 in (ℤ/Nℤ)^× under e_x↦x. Squaring therefore gives p^{2u}q^{2h}≡1 mod N, valid also with negative exponents. Its left side is not 1 as a rational number by unique factorization.

## 2. The normalized *two*-logarithm bound

Discard p from S since p∤N. Select ℓ∈S with v_ℓ(N)log ℓ maximal. The hypothesis gives v_ℓ(N)≫_{S,ε}L. Both labels are ℓ-units. If h=0, the elementary lifting-the-exponent formula for the fixed unit p gives v_ℓ(p^{2u}−1)≪_{p,S}1+log(2|u|)=O(log L), impossible. If u=0, the corresponding one-log estimate is
     
    v_ℓ(q^{2h}−1) ≪_S log q + log(2|h|).

For odd ℓ use q^{ℓ−1}−1 (when the original valuation is positive, raise to exponent ℓ−1 and apply LTE); for ℓ=2 use q²−1. These bounds hold for negative exponents as well.

When u,h≠0, apply [Bugeaud–Laurent, *Minoration effective de la distance p-adique entre puissances de nombres algébriques*, §2, Théorème 3/Corollaire 1](https://irma.math.unistra.fr/~bugeaud/travaux/logpadicdef.pdf). At the local prime ℓ take their two rational bases p^{sgn u} and q^{−sgn h}, with positive exponents 2|u| and 2|h|. The valuation of the difference of those powers is exactly that of p^{2u}q^{2h}−1. The bases are multiplicatively independent ℓ-units, D=f=1 in their notation. Choose the two log-height bounds a₁=max(log p,log ℓ), a₂=max(log q,log ℓ). Their b′=2|u|/a₂+2|h|/a₁ is O_{p,k}(T^{t+1}), rather than a quantity of size L T^t. The uniform theorem gives
     
    v_ℓ(p^{2u}q^{2h}−1) ≪_{p,S,k} log q · (1+log T)^2.

The same estimate suffices in the u=0 case. In particular T≪_{p,S,k,ε}(1+log T)^2, so T is bounded independently of N. This forces q→∞ on any counterexample sequence and makes h nonzero and bounded, with |u|=O_{p,S,k,ε}(L).

## 3. A fixed binomial and a two-place cancellation

If there were counterexamples with N→∞, pass to an infinite subsequence with H=2|h| fixed. The congruence reads q^H≡p^b mod N with b=−2u sgn(h). Write b=Hd+j, allowing d∈ℤ; fix the remainder 0≤j<H on a subsequence. Put z=p^d, a rational p-unit away from p, so (q/z)^H≡p^j mod N and |d|=O(log N).

For every ℓ∈S the polynomial X^H−p^j has H distinct algebraic ℓ-adic unit roots; choose a nearest one α_ℓ to q/z. Distances to the other roots are bounded below by their minimum separation from one another, by the ultrametric inequality and nearest-root choice. Thus for ℓ|N the factorization gives |q−α_ℓ z|_ℓ≪_{p,S,H}|N|_ℓ (|z|_ℓ=1). For ℓ∤N it suffices that |q−α_ℓ z|_ℓ≤1. Fixed H,j leave finitely many local choices, so pass to a fixed system of roots. This argument includes ℓ dividing H; no uniform root separation over varying H is used.

Take the pair (X,Y)=(q,z). At ∞ and at p take the two coordinate linear forms; at each ℓ∈S take X−α_ℓY,Y. The product of all absolute values of these forms is at most
     
    C q |z|_∞ |z|_p / N_S = C q/N_S ≤ C N^{−ε},

since |q|_p=1 and |z|_∞ |z|_p=1. For an integer-vector formulation multiply both coordinates by p^{max(0,−d)}. The product of the local scaling factors squared is exactly one, so the same bound holds. The resulting primitive integral pair has sup norm at least q and at most N^{C₁}, for a fixed C₁. Thus for sufficiently large N the product is less than its sup norm to exponent −ε/(2C₁). Apply the p-adic Subspace Theorem, e.g. [Evertse's precise integer formulation, Theorem 11.1.2](https://pub.math.leidenuniv.nl/~evertsejh/Padicsubspace.pdf) or [Evertse–Schlickewei, Theorem B](https://pub.math.leidenuniv.nl/~evertsejh/98-absolute.pdf). The local forms are independent at each place and have algebraic coefficients in the indicated completion. Only finitely many rational lines can contain the resulting vectors. A fixed rational projective ratio q/p^d determines q (its only non-p prime factor), contrary to q→∞. This proves the asserted independence.

## 4. Feedback and actual forward orbits

Every upward support edge x→y with x<y has x=N mod y; thus each target has at most one smaller parent. The undirected graph of upward edges is a forest, since the largest vertex on a putative cycle would have two smaller parents. A smaller color class of this bipartite forest meets every upward edge and has size ≤⌊|C|/2⌋. Since A has no loops and each directed cycle must use an upward edge, it is a feedback set.

For any feedback set F, the complementary U supports a nilpotent matrix A_UU. First-return elimination gives nullity(I−A)=nullity(I−K), where K=A_FF+A_FU(I−A_UU)^{-1}A_UF. Each of the at least two outgoing arcs with multiplicity at f∈F extends to a first-return path: the complement is acyclic and no row is a sink. Hence K has each row sum ≥2 and I−K is nonzero. Consequently nullity(B)≤|F|−1 and, in particular, ≤⌊|C|/2⌋−1. This also proves that at least six labels are necessary under the theorem's hypotheses.

Under Goldbach failure the forward factor closure from p consists of odd primes coprime to N: coprimality propagates along factoring N−x, and the complement cannot be prime or 1. Every new factor is at most (N−3)/3. The process closes in a finite set. Applying the theorem with k=5 rules out all closure sizes ≤5 for sufficiently large N in the stated family.

## Relation to nearby work

[Bożek](https://arxiv.org/abs/1909.09900) provides the factor-closure framework and [Kelanemer's August 2026 record](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460) announces other graph and spectral arguments; its full text remained unavailable for audit. The earlier [dyadic rank result](PrimeOrbitDyadicRank.md) concerns two prescribed seed directions and a height/size alternative. Here the second direction is the least other label, allowed to move, and the argument uses the normalized two-log bound plus the Subspace Theorem for the stated fixed-set prime-power family. This gives no upper bound on the closure size or a proof of representability.
