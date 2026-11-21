# A single missing even sum with all earlier sums present and every other large sum normal

This is a finite countermodel to possible **generic** least-exception propagation lemmas, not a construction of a counterexample for the actual primes. It strengthens an earlier fixed-target pair model of central weights in two ways: it is one set on the full interval rather than a central weight, and it gives complete coverage of *all* the other even targets plus their uniform weighted Hardy–Littlewood asymptotic at power scales. It does not impose the prime-generating sieve or any Euler product.

## Proposition

For every sufficiently large even N, there is a set A_N ⊂ [2,2N] ∩ Z such that:

1. Among the even integers 4≤M≤2N, exactly N is not in A_N+A_N. In particular the least missing even sum is N.
2. Set a(n)=(log n)·1_{n∈A_N}, and let r_N(M)=Σ_{n+m=M}a(n)a(m), counting ordered pairs. For every fixed ε>0,
   
       r_N(M)=(1+o_ε(1)) S(M) M
       uniformly on even N^ε≤M≤2N, M≠N.

   S(M)=∏_p β_p(M), with β_p(M)=(1−ν_p(M)/p)/(1−1/p)^2 and ν_p(M)=1 for p|M, 2 otherwise.
3. There is a primorial W=N^o(1) tending to infinity. Off O(N^o(1)) small chosen anchors, every selected integer is coprime to W. For every interval I⊂[2,2N], divisor d|W and reduced residue h mod d,

       Σ_{n∈I; n≡h mod d} a(n) = |I∩Z|/φ(d)+O(√N log N).

   Nonreduced classes contain at most total O(N^o(1)) weight. The same random choice can concentrate any predetermined polynomial-size family of bounded complex one-point tests against the deterministic wheel expectation at O(√N log N), with a constant depending on the polynomial exponent. In particular one may adjoin all additive Fourier tests of moduli up to N^C, for fixed C. This is a synthetic concentration statement about the wheel expectation, not an unconditional assertion about the Fourier main terms for primes.

## Construction

Write L=log N, z=L/√log L, W=∏_{p≤z}p, b=W/φ(W). Chebyshev’s estimate gives log W=O(z), and Mertens gives b≪log z. Choose the odd integer H immediately above 2 W L^10. Thus H=N^o(1), H/W≥L^10, log H≫log L; more precisely the lower Chebyshev bound log W≫z implies b/log H=o(1). For large N assume N>100H.

Put 2 and all odd integers from 3 to H into A_N. Ban every N−a with a in this anchored set and ban N/2. Apart from these fixed inclusions/exclusions and outside [2,2N], allow only integers n coprime to W, with prescribed marginal q_n=b/log n if n>H, zero otherwise. The active sites are the allowed integers n>H. Partition them into blocks by the involution n↦N−n if the other site is active, or use a singleton otherwise. On each pair block {n,m} choose the state “n only” with probability q_n, “m only” with probability q_m, “neither” otherwise. This is possible since each q_n=o(1), uniformly. Singletons are independently retained with probability q_n. Blocks are independent, all active one-site marginals are unchanged, and no pair with sum N exists. The fixed diagonal is excluded even if it were W-eligible.

## Every other target, including endpoints

The deterministic set already represents every even 4≤M≤2H, since 4=2+2 and 3,5,…,H is an interval in the odd lattice.

If 2H<M≤4H, take an odd p∈[H/2,H] and let q=M−p. One has H<q<4H, so no candidate q is near the reflection bans; the map p→q is injective. In the interval for q there is at least one reduced W-class per complete period, and a q in that class is odd, hence corresponds to an anchored p. This gives ≫H/W active sites for the M-pair tests in distinct reflection blocks (any two q are <4H). Each succeeds independently with probability ≥1/log(2N).

For 4H<M≤2N, M≠N, let n run over [M/3,M/2) and put m=M−n. Both sites exceed H; both lie in [2,2N]. The possible bans at [N−H,N] discard two intervals of n each of length at most H. They do not arise if M<N/2. If M≥N/2 starting with M/6 and discarding these intervals leaves at most three pieces, one with length ≫M; removing at most two points for N/2 still leaves a subinterval of length ≫M. Each complete W-period has at least one solution (n(M−n),W)=1, by CRT: at 2 only one class is excluded, at each odd prime at most two. Thus there are ≫M/W≥c H/W candidate unordered pairs, each with two distinct endpoints in distinct reflection blocks because M≠N. The graph joining candidate pairs which share a random block has maximum degree at most two: the edges for fixed M are disjoint as vertex sets, so each endpoint can touch at most its unique reflected endpoint in another pair. Greedy selection produces ≥1/3 of the pairs using disjoint blocks. Their successes are independent with probability at least 1/log²(2N). Hence the failure probability for any target in the full range M>2H, M≠N, is ≪exp(−c L^8), giving a vanishing total failure probability. This argument also handles M=2N: both endpoints are supported, without a boundary loss.

## Uniform weighted count at the other targets

Ignoring O(H) pairs incident to the deterministic anchors, banned sites, or the possible fixed diagonal, a summand a(n)a(m) for n+m=M involves distinct random blocks. Its expectation is then b²·1_{(n(M−n),W)=1}. The weighted deterministic omissions cost O(H L²). With each M≤2N, exact periodic counting gives

    E r_N(M)=M S_W(M)+O(H L²+b² W),  M≠N,
    S_W(M)=∏_{p|W} β_p(M).

The expected contribution of the lone M/2 diagonal is O(L²); subtracting or adding its model value is also harmless. For p>z, the total log tail of the p∤M factors is O(1/z); those dividing M contribute O(log(2N)/(z log z))=o(1), since there are at most log(2N)/log z distinct such primes. Thus S_W(M)=(1+o(1))S(M) on all even M≤2N, uniformly. The series is bounded away from zero on evens. The remainders are N^o(1).

Color the graph of unordered M-pairs by three colors (maximum degree ≤2), treating anchored one-site pairs similarly, or retaining them as a deterministic O(H L²) remainder. Ignore the diagonal. In each color the variables are independent and bounded by O(L²); Hoeffding gives deviation O(√M L^(5/2)) with failure probability O(N^−5), simultaneously for M≤2N by a union bound. Ordered pairs add the factor exactly by weighting each unordered non-diagonal pair twice. This and the expectation prove 2 for the same realization that gives 1, simultaneously for each fixed ε.

## One-point tests and scope

In each bounded one-point test, the centered random block contributes O(L), and the sum of its variances is O(NL). Indeed it is at most a constant times Σ E a(n)^2, and for the unfixed part this is ≪ b L (2N/b+W)≪NL. Bernstein gives centered deviation O(√N L) with failure probability O(N^−D) for arbitrarily large fixed D by adjusting the constant. This holds also for the real and imaginary parts separately. The expectation of a(n) on active sites is b·1_{(n,W)=1}; the anchor/ban changes are only O(H L) to every bounded test. For a reduced h mod d dividing W, a full W-period has φ(W)/φ(d) compatible units, so the interval discrepancy from the expected periodic main term is at most O(bW). Both H L and bW are o(√N). There are only polynomially many such intervals, divisors and residue classes, so all these events hold together with 1 and 2.

The congruence wheel is exact off the fixed small anchors; below H we have inserted composites on purpose. The weights agree with the ordinary expected local density and with Hardy–Littlewood first-order counts *at all other large even shifts in the window*, but they do not have the multiplicative and factorization constraints of the real primes. The known almost-all theory (e.g. [Grimmelt–Bhowmik](https://arxiv.org/abs/2607.27282v2)) is about real primes and is not derived from this construction. An additive propagation strategy based just on these observations and exact smaller-sum coverage cannot force the missing target to propagate. Extra prime-specific input remains possible.

### Dated comparison (21 November 2026)

The July–21 November primary and repository check distinguished this deliberately constructed finite additive model from genuine estimates. [Grimmelt–Bhowmik, arXiv:2607.27282v2](https://arxiv.org/abs/2607.27282v2) (13 August and subsequent journal publication) discusses a standard random congruence model and proves a major-arc result for the real primes. [Pintz–Althöfer, arXiv:2610.15559v1](https://arxiv.org/abs/2610.15559v1) and [Althöfer–Chen–Perelli–Pintz, arXiv:2611.09386v1](https://arxiv.org/abs/2611.09386v1) give bounds on genuine exceptional sets in global and polynomial-sampled ranges, under the hypotheses of each paper. None of those bounds gives the specific reflection-conditioned finite model here. The public [arithmetic two-weight parity example](ArithmeticTwoWeightParityWitness.md) addresses a different set of sieve statistics. The bounded keyword/code comparison found no duplicate; no claim of global priority or genuine-prime nonexistence is made.
