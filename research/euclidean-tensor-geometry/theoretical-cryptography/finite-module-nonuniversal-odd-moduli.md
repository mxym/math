# Nonuniversal critical-window law for all odd moduli

This is an asymptotic counting theorem for a uniform finite-module kernel. It does not give a short-relation algorithm, a noisy Ring-LWE reduction, or a security claim. The prime-modulus precursor is [here](finite-module-nonuniversal-all-moduli.md); [Gargava–Serban–Viazovska–Viglino](https://arxiv.org/abs/2510.12893) treat other random module-lattice ensembles. The ingredients used below include [Wang–Wang's cyclotomic-factor context](https://people.math.carleton.ca/~wang/papers/CycloFactor.pdf) and [standard Hensel lifting](https://stacks.math.columbia.edu/tag/04GG). Multilevel CRT constructions over different primes also appear in [Huang–Narayanan](https://arxiv.org/abs/1506.08269), which studies coding and decoding rather than this critical-window law.

## Theorem

Let w→∞, let d be a power of two, t≥1, B/w²→∞ and B≤w^C for fixed C, and let Q≥3 be any odd integer, possibly varying. Put S=Z[Y]/(Y^d+1) and D=dt. The B rows M_i are independent and uniform in (S/QS)^t. Use the squared coefficient energy E(c) of c∈S^B. A tuple is feasible if Σ_i c_i M_i=0; exclude universal tuples c∈(QS)^B. Count feasible orbits under common signed monomial multiplication. Suppose

    λ_w = binom(B,w)(2d)^(w−1) Q^(−D) → λ∈(0,∞).

Then the number of nonuniversal feasible orbits with E≤w converges in total variation to Pois(λ). The nonuniversal minimum is w or w+1 with respective probabilities 1−e^(−λ)+o(1) and e^(−λ)+o(1). The full (nonzero) minimum is exactly the nonuniversal minimum clipped at Q².

## Exact signed-monomial shell over the lifted ring

Normalize by setting the first nonzero entry to 1. Write N=binom(B,w)(2d)^(w−1) for the shell size. In each Hensel CRT component, the 2d monomials remain distinct units in any residue field of characteristic p|Q: a root of Y^d+1 has order 2d. Thus two distinct normalized candidates have rank 2 in every residue field.

For s distinct shell candidates, let r be the minimum of the ranks over the residue fields of all local CRT components. Each component has a unit r×r minor over its local ring, so the joint event probability is at most Q^(−Dr). If r=s this is equality. In all cases the joint probability is at least Q^(−Ds), since the output space has size Q^(Ds). The deficient tuple counting in the [shell factorial-moment proof](finite-module-sparse-poisson.md) uses only the residue-field ranks, the injective monomial alphabet and the support pattern. There are at most d·ω(Q) local components, where ω(Q) is the number of distinct prime divisors of Q. Consequently the same basis-counting argument over all components gives:

    0 ≤ E[(Z)_s] − (N)_s Q^(−Ds)
      ≤ d·ω(Q) Σ_(r=2)^(s−1) binom(s,r) λ_w^r ρ_r (2d+1)^(r(s−r)),
    ρ_r = min(1, binom(r,2) 2^w (w/B)^ceil(w/[2(r−1)])).

In particular this is not an assertion that a deficient residue rank determines the exact lifted probability. A unit minor suffices for the bound: after fixing the remaining input coordinates, the selected output equations determine the pivot input coordinates uniquely. For full rank it also shows surjectivity, giving the equality.

Put R=D log Q. Criticality and standard binomial bounds give

    R=w log(Bd/w)+O(w+log d), R=Θ(w log w), d=O(w log w/log Q).

Indeed d log Q≤R≤O(w(log w+log d)); this first implies d≤w² eventually and then the stated estimates. Since ω(Q)≤log Q/log 3 is polynomial in w by these estimates, all fixed higher factorial-moment errors vanish, yielding the shell Poisson law and TV convergence by the cited proof. The w+1 mean diverges by the factor 2d(B−w)/(w+1); rank 2 gives pairwise independence there, so that shell is nonempty with high probability.

Tuples with a unit coordinate in every residue component are called fully active (the coordinate can depend on the component). Their feasibility probability is exactly Q^(−D). The fully active exceptional raw tuples of E≤w are o(binom(B,w)(2d)^w), by the [unrestricted energy-ball counting argument](finite-module-unrestricted-critical-window.md): almost all such raw arrays have w signed unit entries, and O(w²/B)=o(1) of the latter repeat a row. Dividing by the free orbit size 2d and weighting by Q^(−D) bounds the exceptional expected count by o(1). The action is free on nonzero tuples since S is a characteristic-zero domain and signed monomials are distinct.

## Valuation profile and norm bound

Write Q=∏_(p|Q) p^k_p. For each p all irreducible residual factors of Y^d+1 have common degree f_p=ord_(2d)(p). Define J_p=d/f_p, h_p=max(1,f_p/2), and d'_p=d/h_p. There are factors Gbar_(p,j)(Y^h_p) with Gbar_(p,j) dividing Z^d'_p+1 and of degree f_p/h_p≤2. Also d'_p≤p+1 and J_p≤(p+1)/2. To see this, for f_p=1 use h_p=1 and 2d|p−1. Otherwise write f_p=2^a, a≥1. The identity v_2(p^(2^a)−1)=v_2(p²−1)+a−1 (by repeated difference of squares) implies that p²≡1 mod 2d/h_p. The root β=y^h_p has order 2d/h_p. Its degree is exactly 2 because it is at most 2 and adjoining a root of Y^h_p=β has degree at most h_p, whereas y has degree f_p=2h_p. Thus Gbar_(p,j)(Y^h_p) is irreducible by the degree of y. Moreover d'_p≤2^(v_2(p²−1)−1)≤p+1 since exactly one of p−1,p+1 has 2-adic valuation 1.

Use the common block size h=min_(p|Q) h_p, which divides each h_p. Write d'=d/h=max_(p|Q) d'_p≤p_max+1≤Q+1, and B'=Bh. For each p, the polynomials Gbar_(p,j)(Z^(h_p/h)) are the distinct irreducible factors of Z^d'+1: a proper factor would remain a proper factor after substituting Z=Y^h in the irreducible polynomials above. Their degree is e_p=f_p/h, possibly greater than 2. Lift these factors by Hensel to monic G_(p,j) over Z_p. Then G_(p,j)(Y^h) multiply to Y^d+1 and lift its residual irreducible factors. Write A_(p,j)=Z_p[Z]/G_(p,j) and C_(p,j)=Z_p[Y]/G_(p,j)(Y^h). The monic equation Y^h=Z gives C_(p,j) free over A_(p,j) on 1,Y,…,Y^(h−1). Both are free over Z_p with residue fields, and any element nonzero modulo p is a unit after reduction mod p^k_p. Divisibility by p^v is coordinatewise in the block basis.

For a coefficient tuple set v_(p,j)=min(k_p,min_i v_p(c_i in C_(p,j))), with zero having valuation +∞. Define

    γ_p = Σ_j v_(p,j)/J_p,   Γ=Σ_(p|Q) γ_p log p,   R=D log Q.

For a nonuniversal tuple Γ≤log Q−δ with δ=min_(p|Q) (log p)/J_p, and not fully active means Γ>0. The output in C_(p,j)/p^k_p C_(p,j) is uniform on the ideal p^v_(p,j) C_(p,j)/p^k_p C_(p,j) of size p^((k_p−v_(p,j))f_p). All components and all t copies are independent, giving the exact feasibility probability

    exp[−D(log Q−Γ)].

Decompose each c_i as Σ_(ℓ<h) Y^ℓ c_(i,ℓ)(Y^h), and let L count the nonzero integral blocks c_(i,ℓ) in S'=Z[Z]/(Z^d'+1). Blocks have additive energy. If Γ>0 no nonzero block can have energy 1, as a signed monomial is a unit in every component; hence L≤w/2 when E≤w. For each p every block is divisible by p^v_(p,j) in A_(p,j). For any nonzero block b, its integral nonzero norm (determinant of multiplication) is divisible by p^(Σ_j v_(p,j)e_p)=p^(γ_p d') for every p. Multiplying these independent divisibilities lower-bounds the absolute norm by exp(Γd'). The mean squared magnitude across the complex embeddings of S' equals its coefficient energy, by root orthogonality. Apply arithmetic–geometric mean to a block of energy ≤w/L:

    exp(Γd')≤(w/L)^(d'/2),   L≤w exp(−2Γ),
    Pr(feasible) ≤ exp[−R+(D/2) log(w/L)].                    (*)

## Bounded Q

Pass to a constant Q subsequence. For a nonuniversal, non-fully-active profile, 0<Γ≤log Q−δ. Uniformly for all such profiles,

    exp(−2Γ)<1−Γ/log Q.

Indeed δ≥δ₀=2 log 3/(p_max+1) and δ₀≤(log 3)/2. The function F(x)=log(1−x/log Q)+2x is concave with F(0)=0 and F(log Q−δ₀)>0, because

    exp(2δ₀) log Q/δ₀ ≤ 3(Q+1) log Q/(2 log 3) < Q².

For the last step use log Q≤Q/2 and 3(Q+1)≤4Q<4Q log 3 for Q≥3. Since all J_p and k_p are bounded at fixed Q, only finitely many profiles can occur, making the gap uniformly positive (or there are no such profiles).

At given L, select the blocks in binom(B',L) ways. There are at most 2^min(Ld',w) binom(Ld'+w,w) arrays on their slots, since the sum of absolute coefficients is no larger than the energy and there are at most min(Ld',w) nonzero signs. As d' is bounded, array cost is exp(O_Q(w)); selector cost is exp(L log(B'/w)+O(w)). Also R=w log(B'/w)+O_Q(w). The norm bound and exact probability therefore give total cost exp(−[1−Γ/log Q−exp(−2Γ)] w log(B'/w)+O_Q(w)). Sum over L and the finitely many profiles to get o(1).

## Unbounded Q

Pass to Q→∞. Three ranges suffice; the last two use the same counting bounds as the prime proof, with d'≤p_max+1≤Q+1.

**Low support, 1≤L≤2w/Q².** For a nonuniversal tuple choose any local CRT component (p,j) with at least one coefficient nonzero mod p^k_p. For fixed support, projected block assignments have at most p^(k_p e_p L) possibilities. Freeness ensures a nonzero assignment produces a nonzero coefficient tuple there, hence at least a residue-field output constraint per copy after removing the common p-power. The exact output probability is therefore at most p^(−tf_p). Compared to tf_p log p, the log assignment count ratio is

    k_p e_p L/(tf_p) = k_p L d'/D = O((log Q)²/(Q log w)) = o(1),

since d'≤Q+1, k_p≤log Q/log 3, D=Θ(w log w/log Q) and L≤2w/Q². This avoids requiring descended degree ≤2 in each component. Also

    tf_p log p ≥ 2D log p/(p+1) ≥ D log Q/Q = R/Q,

using the monotonic decrease of (log x)/x on x≥3 and p+1≤2p. The sum over supported size choices and selectors, and over at most d log Q/log 3 components, has logarithmic cost O(w log w/Q²+log w) because a nonempty range implies Q²≤2w. This is o(R/Q). The union over projected nonzero assignments, their supports and active components is therefore o(1). This bounds probabilities, not counts of integral lifts.

**Middle support, 2w/Q²<L≤w/Q^(3/2).** By (*) the probability is at most exp(−(D/2)log 2). There are Ld'=O(w/√Q) slots; the array logarithm by the preceding combinatorial bound is O(w log Q/√Q) and the selector logarithm O(w log w/Q^(3/2)). Both are o(D), with D=Θ(w log w/log Q); this range is nonempty only for Q≤w^(2/3), so D=Ω(w) and summing O(w) support sizes is harmless.

**Large support, w/Q^(3/2)<L≤w/2.** For completeness, consider a subsequence with limits a'=lim log d'/log w, b'=lim log B'/log w≥2, β=lim log L/log w, c=lim log Q/log w∈[0,∞]. All but c are bounded, 0≤β≤1, and R/(w log w)→r_0=b'+a'−1. If c<∞ then a'≤c. Normalize log(selector × array count × probability bound (*)) by w log w.

* When 0<c<∞ the probability contributes −(r_0/c)(c−(1−β)/2) and the term in parentheses is ≥c/4. For β<1, the selector contribution vanishes and the array contribution is at most (β+a'−1)_+, by the binomial bound. When β+a'≤1 the sum is negative; otherwise it is an affine function of β, negative at β=1−a' (since a'≤c) and at β=1 (where it is −(b'−1)). If β=1 use L≤w/2 for selector ≤(b'−1)/2, and array ≤a'; again the total is ≤−(b'−1)/2.
* When c=0, a'=0 and the array logarithm is o(w log w). Pass further so L/w converges. If its limit is zero the selector contribution vanishes and (*) costs at least R/4. If positive, log(w/L)=O(1), while log Q→∞, so the probability contributes −r_0 and the selector at most (b'−1)/2.
* When c=∞, log(w/L)≤log w=o(log Q), so the probability contributes −r_0 uniformly, against a selector ≤(b'−1)/2 and array ≤a'.

Every subsequence with the displayed limits has negative limsup, hence the bound is uniformly exponentially small on the w log w scale (otherwise extract such a subsequence from failures). Summing O(w) choices of L preserves o(1).

This proves that with probability 1−o(1), no nonuniversal tuple of energy ≤w is feasible outside the normalized shell, for any sequence of odd moduli. This transfers the shell law in TV. The available w+1 shell gives the minimum law. Every nonzero universal tuple has energy ≥Q², with equality attained by a single coefficient Q, proving clipping.

## Why oddness matters for this shell count

For Q=2, changing any of the w−1 noninitial signs of a normalized shell candidate leaves its finite equation unchanged. Hence the shell count is always a multiple of 2^(w−1). If its expected value remains bounded, the probability that the count is positive tends to zero, despite the positive limiting mean in a critical window. This rules out simply copying the positive Poisson shell law at Q=2; it is not a classification of even moduli.

## Small independent checks

[The generated toy verifier](verify-finite-module-odd-moduli.js) works over Z/25 with split Y²+1. It additionally checks all 225 coefficients in the mixed inert/split toy ring (Z/15)[Y]/(Y²+1) against direct multiplication counts and norm divisibility. It also checks ten cases at Q=51, d=8, where the common block produces residue degrees four and one. It checks multiplicative and row equations over Z/25 against brute-force output counts, integral norm divisibility against both local valuations, and pairwise independence for all 120 pairs of its 16 shell rows. A triple with determinant valuations (0,1) exhibits the precise issue that residual rank alone misses: the probability in the deficient component is 5^(−5), not 5^(−4), with the third Smith entry divisible by 5 but not 25. Another triple has (2,2), and full-rank triples have (0,0).
