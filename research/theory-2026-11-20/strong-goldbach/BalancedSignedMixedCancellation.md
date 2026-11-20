# Fixed-target signed prime–rough cancellation at the square-root scale

**Status.** An unconditional signed mixed-correlation estimate at balanced divisor sizes. It removes the mixed and rough–rough terms in a specified Möbius-row variance, but leaves the actual two-prime term completely unestimated. It is not a Goldbach proof.

Let N be large and even, L=log N, and let D,K be between fixed positive multiples of √N. Let 2≤z with (log z) log L=o(L), for example z=exp(Lᵝ) with any fixed 0<β<1, or exp(L/(log L)²). Write P_z=∏_{r≤z}r with r prime, V_z=∏_{r≤z}(1−1/r), and μ_N(e)=μ(e)1_{(e,N)=1}. On pairs (e,k) with m=N−ek in a fixed interval [αN,(1−α)N], put
    A_{e,k}=(log m) 1_{m prime},       B_{e,k}=V_z⁻¹ 1_{(m,P_z)=1}.
When either function is extended by zero outside this interval, the extra restriction in e is an interval for each k>0. The main estimate is: for every A>0, any integer k>0, and every real interval I⊂[1,CD],
    Σ_{e∈I} μ_N(e) B_{e,k} ≪_{A,C,α} D L^(−A).                         (1)
The constant is independent of N, k and the endpoints. The sufficiently-large threshold also requires the stated limit on z; for a fixed β it may depend on β. The estimate is relative to the whole scale D, not to the length of an arbitrarily short I.

In particular, take an interval J⊂[cK,CK], let I_{d,k}⊂[cD,CD] be arbitrary intervals varying with d,k, and suppose |c_{d,k}|≤L^C₁. Then, at each fixed N,
    Σ_{k∈J} Σ_{cD≤d≤CD} c_{d,k} A_{d,k}
                          Σ_{e∈I_{d,k}} μ_N(e) B_{e,k}
       ≪_{A,C,C₁,α} D²K L^(−A).                                       (2)
There is the same conclusion for the reversed mixed product, interchanging the roles of d and e and evaluating (1) on the rough variable, and for (2) with B in place of A in the outer row. This is a signed sum with the structured Möbius coefficient on the rough row, not a bound on the sum of the absolute errors of individual row pairs.

## 1. Coprime maximal Möbius distribution

The only distribution input is classical maximal Möbius Bombieri–Vinogradov in reduced classes: for every B>0, some C_B gives
    Σ_{q≤Y^(1/2)/(log Y)^C_B} max_{a mod q, (a,q)=1}
                    sup_{t≤Y} |Σ_{n≤t, n≡a mod q} μ(n)|
         ≪_B Y (log Y)^(−B).
See [Murty–Vatwani, Proposition 3](https://www.mathjournals.org/jrms/2018-033-002/2018-033-002-001.html), citing Corollary 1 of Siebert–Wolke; the reduced-class form is also spelled out as (3.1) in [Lü–Wang–Wu v2](https://arxiv.org/pdf/2610.20242v2). We use none of the shifted-prime correlation results in the latter paper.

The same sum with μ_N in place of μ, restricted to q coprime to N and q≤Q=N^{o(1)}, is ≪_B X L^(−B) with X=CD. To see this, let S_N be the positive integers whose prime factors all divide N, with 1 included. The Euler factors give
    μ_N = μ * 1_{S_N}.
Use this convolution in the prefix. Each s∈S_N is invertible modulo q, and because a is a unit the inner Möbius sum lies in a reduced class. For s≤X^(1/5) apply maximal BV at Y=X/s; all those scales satisfy Q<Y^(1/2)/(log Y)^C_B for sufficiently large N. Also log Y≍L uniformly. The sum of 1/s over S_N is ∏_{r|N}(1−1/r)⁻¹≪log L, by Mertens up to L² and the trivial bound on the number of larger prime divisors. Increasing B in the input absorbs this factor.

For the tail, ∏_{r|N}(1−r^(−3/4))⁻¹=exp(O(L^(1/4)))=X^{o(1)}: split the sum of r^(−3/4) at L and use at most L/log 2 prime factors above L. Rankin therefore gives
    #{s≤X:s∈S_N} ≤ X^(3/4+o(1)),
    Σ_{s>X^(1/5),s∈S_N}1/s ≤ X^(−1/20+o(1)).
In a single modulus the trivial inner bound is X/(sq)+1 uniformly in t and a. Summing q≤Q, the whole large-s part is
    ≪ X^(19/20+o(1)) log(2Q) + Q X^(3/4+o(1)),
which is smaller than X L^(−B) for any fixed B. This proves the asserted uniform coprime variant. Ordinary interval maxima cost at most twice the prefix estimate.

## 2. A short congruence sieve in the signed row

Keep N,k fixed. If some prime r≤z divides both k and N then B_{e,k}=0 for all e. Otherwise primes r|k with r≤z never divide N−ek. On the support of μ_N, primes r|N with r≤z and r∤k also never divide N−ek, since e is a unit at r. Thus the sieve uses only r≤z with r∤Nk. For each such r the excluded class e≡N k⁻¹ (mod r) is reduced. Every squarefree product q of these primes yields the single reduced class e≡N k⁻¹ (mod q), and (q,N)=1.

Expand the roughness indicator by truncating inclusion-exclusion at order J₀−1, where J₀ is a large fixed multiple of log L as a function of A. The pointwise error is at most the J₀-th binomial term, also when multiplied by the possibly signed μ_N because |μ_N|≤1. Each modulus q has one class, hence its absolute error count on I is ≤CD/q+1. Consequently the truncation error before multiplying by V_z⁻¹ is bounded by
    CD (Σ_{r≤z}1/r)^J₀ / J₀! + z^J₀.
Mertens gives Σ_{r≤z}1/r≤log L+O(1) and V_z⁻¹≪log(2z)≪L. Choose J₀ large to make the factorial term O_A(D L^(−A−2)). The remaining term has size Q:=z^J₀=N^{o(1)} and is absorbed as well.

Every surviving q appears at most once with coefficient μ(q); all are ≤Q and coprime to N. Including q=1, the complete interval-maximal error sum is bounded by §1. Inserting V_z⁻¹ proves (1). The proof works with arbitrary sliding endpoints because the sieve is applied directly in e, not to the numbers N−dk in residue classes modulo d times a small sieve product.

## 3. The mixed terms disappear, the actual two-prime term remains

To prove (2) multiply (1), with a larger A, by at most O(DK) outer coefficients, using |A_{d,k}|≤L and |B_{d,k}|≪L. No average over N or over k was used to cancel the inner row.

For exact variance algebra, set
    a_k=Σ_{e∈I_k} μ_N(e) A_{e,k},     b_k=Σ_{e∈I_k} μ_N(e) B_{e,k},
for arbitrary intervals I_k⊂[cD,CD]. Then for each fixed N and every fixed A>0,
    Σ_{k∈J} |a_k−b_k|² = Σ_{k∈J} |a_k|² + O_A(D²K L^(−A)).             (3)
Indeed the difference is Σ(|b_k|²−2Re(a_k overline(b_k))); (1) and |a_k|≪DL give the claimed bound. Expanded, Σ|a_k|² consists of the actual prime–prime row terms A_{d,k}A_{e,k} weighted by μ_N(d)μ_N(e). The diagonal d=e costs O(DK L²), negligible at this scale. None of (1)–(3) bounds the off-diagonal actual pair terms, even with this Möbius weighting. In particular, controlling a fixed column against rough residues is not a prime-pair asymptotic in the two affine forms N−dk,N−ek.

**Comparison.** [Pham Van Khanh, *Uniformity, Local Structure and Boundary Correlations in Goldbach Representations*, Appendices A, C and D](https://www.preprints.org/manuscript/202610.3061/v1) uses fixed row pairs and estimates an absolute slope aggregate of prime–rough errors; the cited C.2 range approaches the square-root scale from below and D separately gives an uncentered upper bound for actual two-prime rows. Estimate (2) reaches exactly balanced rows by keeping a structured signed sum on the rough side and switching which variable is sieved. It does not imply the stronger rowwise absolute estimate there and does not remove the AA obstacle.
