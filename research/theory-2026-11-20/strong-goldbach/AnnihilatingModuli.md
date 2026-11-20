# The all-modulus twisted EH hypothesis already bounds its own mean

Write L=log N, ρ(n)=Λ(n)μ(N−n) for n<N, and T(y)=Σ_{n≤y}ρ(n) for y<N. Let E(N,Q) be the sum over q≤Q of the maximum over y<N and reduced a modulo q of

    |Σ_{n≤y,n≡a mod q} ρ(n) − T(y)/φ(q)|.

This is exactly the centered discrepancy in [Huang–Li, (twisted EH) preceding Theorem 1.1](https://arxiv.org/html/2005.03811v2). Their ordinary EH and their twisted EH are distinct assumptions. No such estimate of Goldbach strength is proved here. The elementary observations below concern its logical content.

**Zero-class lemma.** For each prime p not dividing N, take q=p² and a=N mod q. There are no nonzero summands: p² divides N−n throughout this reduced class. Thus E(N,Q)≥max_y|T(y)|/φ(p²) when p²≤Q. Some such p≤2L for all sufficiently large N by the prime number theorem for the primorial. In particular, if Q≥4L² and E(N,Q)≪_A N/L^A for every A, the full correlation satisfies max_y|T(y)|≪_A N/L^A for every A; just increase the requested exponent by 2. This works even if only the diagonal class N mod q is tested for (q,N)=1, provided these nonsquarefree moduli are retained. A coprime-restricted reference total instead of the full T does not affect this conclusion at q=p²: n omitted from its support are powers of p of total Λ-weight O(L).

**Amplification at polynomial Q.** Define W(N,Q)=Σ_{q≤Q:∃p∤N, p²|q}1/φ(q). Each such q has a *reduced* residue a≡N mod p², taking a=1 at other prime-power factors by CRT and lifting the unit N at p. Thus

    E(N,Q) ≥ W(N,Q) max_y |T(y)|.                                    (1)

For Q=N^σ, σ>0 fixed, W(N,Q)≫_σ 1/log L for all large N, and this order is attained along primorial targets. Indeed, on L<p≤4L there are (3+o(1))L/log L primes, no more than L/log L of which divide N. For the remaining primes P, u=Σ_{p∈P}p^(−2) satisfies 1/(10L log L)≪u≪1/(L log L). Using 1/φ(q)≥1/q, Bonferroni and the harmonic sum of multiples yields the lower bound

    Σ_{p∈P} p^(−2)[log(Q/p²)+O(1)]
      −Σ_{p<r∈P} (pr)^(−2)[log(Q/(pr)²)+O(1)] ≫_σ L u.

Here Q exceeds (4L)^4 for large N. For N=∏_{p≤t}p we have t∼L; the union bound using φ(p²k)≥φ(p²)φ(k) and Σ_{k≤x}1/φ(k)≪log(2x) gives W(N,Q)≪log(2Q)Σ_{p>t}1/[p(p−1)]≪_σ 1/log L. Hence (1) gives the explicit worst-case control max_y|T(y)|≪_σ (log log N)E(N,Q). This optimal order is asserted for the *annihilating weight W alone*, not for the ratio involving the actual correlations. The amplification uses the original maximum over residue classes, unlike the single-square argument above.

**Equivalent uncentered formulation.** For Q polynomial with Q≥4L², the centered and uncentered assertions (arbitrarily high fixed log savings) are equivalent. In one direction apply the zero-class lemma and then the triangle inequality, using Σ_{q≤Q}1/φ(q)≪log(2Q). In the other direction the q=1 summand of the uncentered hypothesis already bounds max_y|T(y)|, and the same inequality applies.

**Conditional asymptotic, not just positivity.** Under the two *global* all-modulus conjectures in Huang–Li (at complementary levels with their allowed log buffer), every fixed A>0 gives

    Σ_{p₁+p₂=N} log p₁ log p₂ = N S(N) + O_A(N/L^A).

Indeed take B=L^(A+2) in CenteredDivisorSwitch.md, where ordinary EH at the larger same-scale modulus cutoff follows by harmless rescaling of its global prefix version. The zero-class lemma absorbs S(N)T(N), since S(N)≪log log(3N). No rescaling of the twisted sequence is used. Alternatively, for qualitative asymptotic alone, Huang–Li's stated equivalence and the zero-class lemma immediately suffice. In particular by Bombieri–Vinogradov the *single* conjecture EH_μ(N^σ) at any fixed σ>1/2 implies this full asymptotic for large even N, not merely eventual Goldbach positivity: take cutoff exponent θ=1−σ<1/2 and supply ordinary EH there by BV. These are consequences of a hypothesis, not unconditional asymptotic formulae.

**The smaller hypothesis that is actually used.** The positivity conclusion under the squarefree comparison need not posit bounds at any annihilating modulus. In CenteredDivisorSwitch.md, in the ordinary discrepancy keep only the class N mod z for (z,N)=1, z cubefree of shape z=b²h with b,h squarefree, (b,h)=1; no prefix maximum is needed on that side (the endpoint is N−1). In the twisted discrepancy retain only squarefree k with (k,N)=1, a=N mod k, and y≤N−αk (strict endpoint immaterial at the vanishing weight), k<N/α. The same proof and the unconditional squarefree margin still imply R(N)≥(exp(γ)−o(1))N/L if B=L h(N) as in that note. In particular the single-square argument forcing T small is no longer part of the assumptions. This is a restriction of the inputs used, not a proof of logical independence or an assertion that ordinary fixed-class reduction is new: Huang–Li themselves remark after Corollary 1 that the fixed residue suffices. For this smaller, same-N ordinary hypothesis do not use global prefix rescaling without specifying stronger data.

**Related work and boundary.** [Cantarini, §§1–2](https://arxiv.org/html/2607.09110v1) formulates a terminal-endpoint diagonal conjecture with both μ and μ log weights over all coprime moduli, and obtains estimates for *averages* conditional on several zero hypotheses. The single-square lemma applies to each terminal reference total in the stated Conjecture 6. Those averaged estimates do not supply our required individual-N squarefree-modulus bounds. Similar zero classes exist for shifts n+h (use −h mod p² with p∤h), but no assertion about twin-prime proofs is needed here.
