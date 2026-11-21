# Positive density of genuine Goldbach sinks reachable from a fixed prime seed

Use the reverse of [Bożek's prime-factor graph, Definition 2.1](https://arxiv.org/abs/1909.09900): the arc x→y means y divides N−x, where the vertices are primes between 2 and N−2. A pair Q and N−Q of distinct primes is a terminal directed two-cycle. Reachability is an additional restriction on a binary representation, not part of the classical almost-all Goldbach theorem.

**Theorem.** Fix an odd prime p and any fixed arithmetic progression containing even integers coprime to p. There is a constant c>0 depending on these fixed data such that for every sufficiently large X, at least cX even integers N in [X,2X] in this progression have a strictly increasing path from p to a prime Q between X^(1/20) and X^(1/12) for which N−Q is prime. All complements of labels strictly before Q on this path are composite.

**Finite-menu corollary.** Given finitely many prescribed odd primes and any fixed progression admitting even integers simultaneously coprime to them, a positive proportion in every sufficiently large dyadic interval in that progression have a single genuine Goldbach two-cycle reachable from *all* the prescribed primes. The paths in this general corollary need not be increasing in their initial part.

No effective constant, density-one, or pointwise statement is asserted. The proof uses the distribution of individual primes, not an assumption about the occurrence of prime pairs.

## 1. Classes and the first moment

Refine the progression to N=a mod h with 2p|h, a even, and p∤a. There is a reduced class Q=b mod h with (a−b,h)=1: take b odd and at each odd prime divisor of h avoid the two possibly identical residues 0 and a. This works at 3, even when p=3. Use the Chinese remainder theorem (CRT) and lift to prime powers. Without any initially prescribed progression one may take h=2p, a even and 1 mod p, b odd and −1 mod p.

Put γ=1/1000, α=1/20, β=1/12, Y=X^γ, and let J consist of primes Q in [X^α,X^β] lying in b mod h. Fix a large cutoff U>max(p,h), to be chosen only in terms of the fixed data. Let s≤Y be squarefree, with all prime factors >U, allowing s=1. In increasing order list the factors of sQ, starting the path with p; Q>Y is its last label. For each target ℓ in this list, write r_sQ(ℓ) for the preceding label. The residue class n(s,Q) modulo h sQ is defined by
\[
 N=a\pmod h,\qquad N=r_{sQ}(\ell)\pmod\ell\quad(\ell\mid sQ).
\]
It forces every edge. The predecessor of a target ℓ is always a prime strictly below ℓ, so all path labels are units of N. An intermediate N−x is divisible by its next label ≤X^β and is ≫X, hence composite.

For the residue of the desired prime P=N−Q to be reduced, one must exclude the coincidences Q=r_sQ(ℓ) mod ℓ for ℓ|s. These are the only additional obstructions: the modulus h was treated in choosing b, while modulo Q the prime residue is the nonzero predecessor. Without these exclusions raw path counts would not suffice.

The good classes have reciprocal mass
\[
  \sum_{s,Q\ {\rm good}}\frac1{sQ}\gg_h \log X. \tag{1}
\]
Indeed for fixed U the reciprocal sum of admissible squarefree s≤Y is asymptotic to c_U log Y, with
\[
 c_U=\prod_{\ell\le U}(1-1/\ell)\prod_{\ell>U}(1-1/\ell^2)\asymp 1/\log U.
\]
This follows by inclusion-exclusion for small primes and square divisors, or the elementary density of these integers followed by partial summation. The fixed-modulus prime number theorem gives ∑_{Q∈J}1/Q→log(β/α)/φ(h). For each ℓ|s the single forbidden nonzero Q class has reciprocal mass O(1/(ℓ−1)), even before restricting Q mod h, by Brun–Titchmarsh and partial summation: ℓ≤X^γ and log(u/ℓ)≫log u at every u≥X^α. Thus the total removed is at most
\[
 C\sum_{\ell>U}\frac1{\ell(\ell-1)}\sum_{v\le Y/\ell}\frac1v
 \ll \frac{\log Y}{U}.
\]
Here and below ℓ denotes a prime in prime sums and products. First choose U sufficiently large that the loss is less than half the main coefficient, then let X grow. This proves (1).

For each good (s,Q) count the primes P in the common, unmoving interval [X,3X/2] in the reduced class n(s,Q)−Q mod h sQ. Each contributes to Z(N), the number of such paths at N=P+Q; in particular N∈[X,2X]. Bombieri–Vinogradov for the prime counting function, at the two fixed endpoints, gives
\[
 \sum_N Z(N)=\big(\operatorname{Li}(3X/2)-\operatorname{Li}(X)\big)
 \sum_{s,Q\ {\rm good}}\frac1{\varphi(hsQ)}+O_{h,A}(X/\log^A X).
\]
There is no weight or multiplicity loss in its error: Q is the largest prime factor of sQ, so each modulus h sQ occurs once; its size is at most h X^(γ+β)<X^(1/3). The usual average of the maximum over reduced classes therefore dominates the entire error. The lower bound uses 1/φ(hsQ)≥1/(hsQ), not an asymptotic replacement. For the upper bound ∑_{s≤Y}1/φ(s)≪log Y by the squarefree Euler product ∏_{ℓ≤Y}(1+1/(ℓ−1)), and ∑_{Q∈J}1/(Q−1)≪1. Consequently
\[
            X\ll_h \sum_N Z(N)\ll_h X.                          \tag{2}
\]

## 2. Unique backward ancestry and the pair sieve

At a fixed N, a target prime ℓ on an increasing path has only one possible smaller predecessor: the ordinary remainder N mod ℓ. Iteration backwards implies that two paths from p sharing a vertex share their prefixes through it. In particular distinct paths have different terminal primes Q,Q′. No terminal prime can be an interior label of the other path by Q,Q′>Y. Write c for the product of their common prefix labels after p; then s=c v and s′=c w, with c,v,w pairwise coprime, and every prime in v,w larger than P⁺(c), the largest prime factor of c. For the empty prefix set P⁺(1)=1. This description also covers v=1 or w=1. Any residue-incompatible pair contributes zero.

For a compatible pair, N is in one CRT class mod L=h c v w Q Q′. Put Δ=|Q−Q′|, and F(j)=∏_{ℓ|j}(1+6/ℓ). Uniformly the count in [X,2X] with both N−Q and N−Q′ prime is
\[
 \ll_h \frac{X}{L\log^2 X}\,F(L\Delta).                       \tag{3}
\]
Here L≤h X^(2γ+2β), so the interval for the progression index has length H≈X/L≫X^(4/5). To see the bound without assumptions about local singular factors, sift only by primes ℓ>2 not dividing LΔ: both shifted forms omit two distinct index classes modulo every such ℓ. Take z=H^(1/3), w₀=z^(1/8). The arithmetic large sieve bounds the count by (H+O(1)+z²)/G(z), where G(z) is the sum over squarefree d≤z with all factors good and ≤w₀ of ∏_{ℓ|d} 2/(ℓ−2). Its untruncated Euler mass is ∏_{good ℓ≤w₀}(1−2/ℓ)^(−1). Under the probability measure proportional to this Euler mass the mean log d is ∑_{good ℓ≤w₀}2 logℓ/ℓ ≤2 log w₀+O(1), so at least half the mass has d≤z for all large X. By Mertens, the full product over 2<ℓ≤w₀ is ≍log² w₀; each removed factor at ℓ|LΔ costs at most 1+6/ℓ. These inequalities prove (3). Both purported primes are ≫X, so neither can equal a sifting prime. Missing or coincident local classes at any path, branch or terminal prime are *all* safely charged in F(LΔ); no independence of the two terminals is used.

## 3. Summing the correlations

The terminal difference costs a bounded factor on average:
\[
 \sum_{X^\alpha\le Q\ne Q'\le X^\beta\atop Q,Q'\ {\rm prime}}
     \frac{F(|Q-Q'|)}{QQ'}\ll 1.                                 \tag{4}
\]
Expand F as a sum of 6^ω(d)/d over squarefree divisors d. For d≤X^(α/2), Q is a unit mod d and Brun–Titchmarsh with partial summation gives ∑_{Q′=Q mod d}1/Q′≪1/φ(d) on the indicated prime range. Sum against 6^ω(d)/d; the squarefree series converges by its Euler product, and ∑_Q1/Q≪1. For each nonzero Δ≤X^β, the remaining divisor tail is at most X^(−α/2)7^ω(Δ)=X^(−α/2+o(1)) uniformly, by the elementary maximal-order bound on ω. This proves (4).

Removing only restrictions for upper bounds, bound F(LΔ) by F(h)F(c)F(v)F(w)F(Q)F(Q′)F(Δ). The new v or w factors have reciprocal Euler mass
\[
  \prod_{P^+(c)<\ell\le Y}\left(1+\frac{1+6/\ell}{\ell}\right)
       \ll \frac{\log(2Y)}{\log(2P^+(c))}.
\]
The shared prefix is summed only once, at cost
\[
     \sum_{c\ {\rm squarefree}}\frac{F(c)}{c\,\log^2(2P^+(c))}<\infty.
\]
Indeed, the c with largest factor ℓ have total F(c)/c at most O(log(2ℓ)/ℓ), again by the Euler product, and ∑_{ℓ prime}1/(ℓ log(2ℓ)) converges. Therefore the sum of F(LΔ)/L over all compatible distinct ordered path pairs is O_h(log²X), using (4). Combining with (3) and the diagonal bound (2) gives ∑_N Z(N)²≪_h X. Cauchy–Schwarz and (2) give the asserted cX centers. No numerical solver or heuristic independence enters the argument.

## 4. Common sink for a prescribed list

For distinct seeds p_i first refine the prescribed progression to fix even parity and nonzero residues at every p_i (possible by hypothesis). Select an auxiliary odd prime r not dividing the resulting fixed modulus, and fixed distinct bridge primes t_i≡1 mod r, avoiding all seeds, r, and all fixed modulus factors. Choose r distinct from the seeds. Refine further by N=1 mod r and N=p_i mod t_i, consistently by CRT. The forced arcs p_i→t_i→r have composite input complements at all large centers. Apply the theorem with root r on this fixed progression. The same pair Q,N−Q is then accessible from every seed. Without a prescribed progression, alternatively order the seeds p₁<⋯<p_s and impose N=p_i mod p_{i+1}, and N nonzero mod p₁; applying the theorem at p_s gives increasing paths from every seed to that common terminal.

## Sources and scope

[Bożek (2019), Definition 2.1 and concluding options (2)–(3)](https://arxiv.org/abs/1909.09900) defines the factor graph and distinguishes the existence of a Goldbach component from excluding every exceptional autonomous component. [Vaughan, The Bombieri–Vinogradov Theorem, §1](https://personal.science.psu.edu/rcv4/Bombieri.pdf) gives the distribution theorem used above; [Montgomery and Vaughan, Multiplicative Number Theory II, Ch. 19](https://personal.science.psu.edu/rcv4/571s25/montgomery-vaughanII.pdf) proves the arithmetic large sieve used in (3). The other inputs are the classical prime number theorem in a fixed reduced progression, Brun–Titchmarsh, Mertens' estimates and the CRT. [Kelanemer, SSRN 7274460](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460) is a 2026 related terminal-graph manuscript whose abstract was accessible; comprehensive comparison and priority are not asserted. This anchored positive-density theorem does not strengthen the classical density-one theorem for unrestricted Goldbach pairs, and does not bound the exceptional set for the full binary conjecture. It proves neither that almost every fixed-seed orbit reaches a prime complement nor that all inputs in a successful orbit do so along every directed branch.
