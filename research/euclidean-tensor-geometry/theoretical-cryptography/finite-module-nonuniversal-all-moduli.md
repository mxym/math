# Nonuniversal critical-window law for arbitrary odd prime moduli

This is a theorem about the minimum coefficient energy in a random finite-module kernel, not an algorithm to find short relations. The random ensemble is discrete and sparse; [Gargava–Serban–Viazovska–Viglino](https://arxiv.org/abs/2510.12893) study shortest vectors and moments for other random module-lattice ensembles. The cyclotomic factor-substitution context includes [Wang and Wang](https://people.math.carleton.ca/~wang/papers/CycloFactor.pdf).

## Statement

Let w→∞, d be a power of two, q any odd prime, possibly fixed, t≥1, B/w²→∞ and B≤w^C for a fixed C. Put S=Z[Y]/(Y^d+1), D=dt. The B rows M_i are independent and uniform in (S/qS)^t. For c∈S^B use the squared coefficient energy E(c) and call it feasible when Σ c_i M_i=0. Exclude all universal tuples c∈(qS)^B (including zero). Count orbits under common signed monomial multiplication, an action free on nonzero integral tuples.

Suppose the signed-monomial shell mean
    λ_w=binom(B,w)(2d)^{w−1} q^(−D) → λ∈(0,∞).
Then the number of nonuniversal feasible orbits of E≤w converges in total variation to Pois(λ), and the minimum energy among nonuniversal feasible tuples is w or w+1, with respective limiting probabilities 1−e^(−λ) and e^(−λ). No fixed comparison between q² and w is required. If universal tuples are restored, the minimum is clipped by q² and their orbit count is added deterministically (see [the crossover note](finite-module-q-square-crossover.md)). This theorem requires a positive limiting critical mean; no claim is made outside that critical window.

## Criticality and the known active part

Write R=D log q. The exact criticality identity and elementary binomial bounds give
    R=w log(Bd/w)+O(w+log d), R=Θ(w log w), d=O(w log w/log q).
Indeed initially d log q≤R≤O(w(log w+log d)); since log q is bounded below, d≤O(w(log w+log d)), first forcing d≤w² for large w, then yielding all displayed estimates, since log(B/w)≥log w eventually. All exponents of d and of B are bounded. Thus the [monomial-shell factorial moment theorem](finite-module-sparse-poisson.md) applies. The shell w+1 has mean diverging by the ratio 2d(B−w)/(w+1) and pairwise independent indicators, so it is nonempty with high probability. Every shell member is nonuniversal.

For any tuple active in every CRT field, feasibility probability is q^(−D). As shown in the [unrestricted coefficient note](finite-module-unrestricted-critical-window.md), the number of fully active exceptional raw tuples of E≤w is o(binomial(B,w)(2d)^w): the support-loss weight x=w/[2(Bd−w+1)] and excess-energy series Σ_{m≥2}x^(m²−1) show that almost every array in the energy ball has w signed unit entries, and row repetitions among these have proportion O(w²/B)=o(1). Dividing by the free orbit size 2d and weighting by q^(−D) makes their expected number o(1). Only CRT-inactive nonuniversal tuples remain.

## Descended blocks

All irreducible factors of Y^d+1 modulo q have common degree f=ord_{2d}(q). Let h=max(1,f/2), d'=d/h, B'=Bh. The dyadic factor-substitution argument in the crossover note gives d'≤q+1, tf≥2D/(q+1), and each factor G_j(Y^h) with G_j irreducible of degree f/h≤2. These facts also hold when f=1: 2d|q−1 then. In a factor field K=F_{q^f}, if y denotes the residue of Y, the subfield k=F_q(y^h) has degree f/h and 1,y,…,y^{h−1} is a basis of K over k. Write c_i=Σ_{ℓ<h}Y^ℓ c_{iℓ}(Y^h); each c_{iℓ} is an integral polynomial modulo Z^{d'}+1. In any dormant factor all reduced c_{iℓ} vanish separately. Block energies add. Let L be the number of nonzero integer blocks; inactive tuples cannot have an energy-one block, since it is a unit in every factor, so L≤w/2 when E≤w.

If dormant factors occupy degree fraction γ, their corresponding lower-degree factors in Z have the same fraction γ. Take a nonzero block of energy ≤w/L. Divisibility of its algebraic norm by at least q^(γ d') and the arithmetic–geometric mean inequality across embeddings give q^(γ d')≤(w/L)^(d'/2); the mean squared embedding magnitude equals the coefficient energy by orthogonality of the roots of Z^{d'}+1. Thus each tuple's probability of feasibility is at most
    exp[−R+(D/2) log(w/L)].                                      (*)

## Bounded modulus: dormant-degree gap

First consider a subsequence along which q is fixed. The number J=d/f of CRT factors is at most (q+1)/2<q. If a tuple is inactive and nonuniversal, necessarily J≥2 and γ=j/J for some 1≤j≤J−1. This means 0<γ≤1−1/J. For every such γ,
    q^(−2γ)<1−γ.
Indeed F(γ)=log(1−γ)+2γ log q is strictly concave, F(0)=0 and F(1−1/J)=−log J+2(1−1/J)log q>0, since J<q and 2(1−1/J)≥1. At fixed q only finitely many J and γ occur, so the gap is uniformly positive. The descended block norm forces L/w≤q^(−2γ). Since d'≤q+1 is bounded, the number of arrays on L d' slots costs at most exp(O_q(w)); this follows from the support, signs and composition bound used below. The block selector costs at most exp(L log(B'/w)+O(w)) by the binomial bound and L log(w/L)≤w/e. Exact feasibility probability is exp(−R(1−γ)), with R=w log(B'/w)+O_q(w), so the selector times array times probability is at most
    exp(−[1−γ−q^(−2γ)] w log(B'/w)+O_q(w)).
This is exp(−Ω_q(w log w)) even after allowing all finite γ classes and O(w) possible support sizes. If J=1 there are no inactive nonuniversal tuples.

For q→∞ there is no fixed dormant-degree gap, but the following three support ranges suffice.

## Low support: local residues rather than integral arrays

For L≤2w/q² (if this range is nonempty), use the existence of any active factor for a nonuniversal tuple. For a fixed factor and block support the projected coefficients in its subfield k have at most q^(2L) choices in total, irrespective of the number of integral lifts. Ignore all-zero assignments: basis independence makes a nonzero assignment a nonzero combination of the original independent uniform rows in K^t, hence with probability q^(−tf) to vanish. Taking a union over factors, supports and assignments bounds the total probability by
    d q^(−tf) Σ_{1≤L≤2w/q²} binom(B',L) q^(2L).
As q²≤2w here, the combinatorial log cost is O(w log w/q²+log w), whereas tf log q≥2R/(q+1)=Ω(w log w/q). The former is little-oh of the latter, so this probability is o(1). This argument does not assert a small expected raw number of low-support lifts.

## Middle support

For 2w/q²<L≤w/q^(3/2), use the bound exp(−(D/2)log 2) from (*). Counting integer arrays on C'=Ld' slots costs at most 2^min(C',w) binom(C'+w,w) (choose support, signs, and a positive integer composition of total at most w; squared magnitudes only reduce the count). Here C'=O(w/√q), so the array log is O(w log q/√q). Choosing blocks costs O(w log w/q^(3/2)). This range is nonempty only if q≤w^(2/3), and both costs are o(D), since D=Θ(w log w/log q). There are at most w possible sizes L, and D=Ω(w) in this range. The total probability is o(1).

## Large support

It remains to show uniform exponential decay on w/q^(3/2)<L≤w/2. The selector and array bounds are binom(B',L) and 2^min(C',w) binom(C'+w,w) as above. Argue by subsequences along which c=lim log q/log w exists in [0,∞], b'=lim log B'/log w≥2, a'=lim log d'/log w∈[0,1] exist, and β=lim log L/log w∈[0,1] exists. We have a'≤c when c is finite and R/(w log w)→r=b'+a'−1, because B'd'=Bd. Consider the log of selector times array times bound (*) divided by w log w.

* If 0<c<∞, the probability contributes −(r/c)(c−(1−β)/2), with c−(1−β)/2≥c/4 by the lower limit on L. For β<1, selector cost is o(w log w); array contribution is at most (β+a'−1)_+. If β+a'≤1 this gives a strictly negative sum. On the other branch the sum is affine in β, negative at β=1−a' since a'≤c, and at β=1 since it equals −(b'−1). For β=1 use L≤w/2 to bound the selector contribution by (b'−1)/2 and the array by a'; the total is at most −(b'−1)/2.
* If c=0 then a'=0 and the array log is o(w log w) uniformly. Pass further so L/w has a limit. If that limit is zero the selector also contributes zero in the limit, and (*) costs at least R/4 in the logarithm. If the limit is positive, log(w/L)=O(1), while log q→∞, so the probability contributes −r and the selector at most (b'−1)/2, strictly smaller than r.
* If c=∞, log(w/L)≤log w=o(log q), so the probability contributes −r uniformly. The selector costs at most (b'−1)/2 and the array at most a', leaving a gap at least (b'−1)/2.

A failure of a uniform negative bound would give a subsequence with normalized exponents tending to zero or above, but every convergent subsequence as above has strictly negative limsup. Thus the large-support contribution is o(1), even after summing over all L.

Every sequence of odd primes admits a subsequence with fixed q or q→∞, and likewise every subsequence does. The two analyses therefore establish a uniform o(1) exceptional probability along the given parameter sequence.

With high probability every nonuniversal feasible tuple of energy at most w is a member of the shell. Equality with the shell count with probability 1−o(1) transfers its Poisson limit in total variation. Nonemptiness of the w+1 shell gives the stated minimum law. In particular, when q²/w→0 the nonuniversal minimum still follows this law, but the ordinary minimum is instead q² with high probability (including fixed q).


[Exact finite checker](verify-finite-module-dormant-degree-gap.js): verifies the dormant-degree inequality for small primes; the analytic argument above covers every odd prime.
