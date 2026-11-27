# A time–space lower bound for adaptive sequential-head factor output

The [fixed-pass result](FactorStreamingBlocks.md) can be strengthened for an input head that may choose directions adaptively. A single read-only head that can move only one cell per step must spend too many steps crossing a linear number of cuts when its workspace is small. The proof allows an uncharged append-only output tape.

**Result.** Let a uniformly random input be the product of two distinct n-bit primes, encoded as an ordinary padded 2n-bit word. For a classical randomized machine with at most 2^s possible internal configurations, fixed input-head starting position, and one adjacent-move read-only input head, there is an absolute c>0 such that
```
Pr[outputs a correct factor AND input-head moves < c n²/(s+1)] ≤ 2^(−Ω(n)).
```
For fixed positive success probability, the product of expected input-head moves and s+1 is Ω(n²). Thus the same product lower bound holds for ordinary elapsed step count on a model charging at least one step per head movement. The bound does not apply to random access, additional input heads, or writable input.

## Machine conventions and input distribution

Working storage includes all control state and persistent workspace information that can influence a later visit; the single current input-head position itself is excluded. At a specified cut, its position just after crossing is determined by the cut and the crossing direction, so it needs no transmitted bit. An ordinary bounded-workspace machine with a fixed number of work tapes can translate its space bound to this internal-configuration parameter, including the work-head locations. No writable or rereadable output, free time-of-computation clock, or other side channel is available. A run succeeds if its output is exactly the prescribed n-bit representation of either prime in a predetermined bit order. Fresh independent random bits are allowed; along a decomposition at any fixed cut, an equivalent simulation uses fresh tapes for successive visits to the two sides. Public randomness independent of the input may instead be conditioned on.

Write P=2^(n−1). There are M∼P/log P primes in [P,2P), and C=binomial(M,2)=Θ(2^(2n)/n²) equally likely distinct products, by unique factorization and the ordinary prime number theorem. The conclusion also follows for any public pool meeting the same growth bound, with an appropriate constant in the probability estimate.

## Local incidence at every contiguous cut

For an integer cut index k, split N as N=2^k H+L, 0≤L<2^k. As in the fixed-pass proof view the products as a simple bipartite graph of block values, with each edge labelled by each of its two prime factors. Let V_H=2^(2n−k), V_L=2^k bound the counts of high and low block values.

Put d=k−(n−1). At fixed L and a specified candidate factor p, its mate must lie in one residue class modulo 2^k, since p is odd. The interval [P,2P) thus gives at most
```
D_L=2^max(0,−d)
```
mates. At fixed H, the mate lies in the half-open interval [2^k H/p,2^k (H+1)/p), of length at most 2^k/P. So there are at most
```
D_H=2^max(0,d)
```
mates there. These integral bounds also hold at d=0. Their useful joint identity is V_H V_L D_H D_L=2^(2n+|d|).

## Count successful runs with few crossings

Fix the cut and fix the coin stream used during each visit, without conditioning on any input, giving a deterministic computation. For a successful run with j crossings, the head starts on a fixed side and visits the two sides in alternating order. Its sequence of internal configurations at handoffs takes at most 2^(js) values. This accounting is valid even when it chooses dynamically when to cross or halt: j is part of the class being counted, and a visit's next actions depend only on its initial state, the local input block, and its now-fixed coin stream. Assign bytes written by the transition leaving a side to that side. If a crossing is represented by separate movement and reading of the entering cell, the entering read is part of the next visit.

A successful length-n output is a concatenation of the j+1 strings written during the visits, and their lengths have at most binomial(n+j,j) schedules. For a fixed crossing transcript and length schedule, let a be the number of output bits written by high-side visits. At a given H these a bit values are fixed. Only 2^(n−a) factor labels match them, and each label is on at most D_H incident edges. The analogous count on the low side permits at most 2^a labels. Consequently each transcript and schedule can cover at most
```
min(V_H D_H·2^(n−a), V_L D_L·2^a)
≤ sqrt(V_H V_L D_H D_L·2^n) = 2^((3n+|d|)/2)
```
successful inputs. This also handles j=0 and does not assume the output schedule is input independent. If k, integer h≥0 and s are specified, division by C, followed by averaging over coins, proves
```
Pr[success and at most h crossings at cut k]
  ≤ min(1, (2^((3n+|d|)/2)/C) Σ_(j=0..h) 2^(js) binomial(n+j,j)).
```

For the cuts satisfying |k−(n−1)|≤n/4 there are linearly many choices and the leading capacity is at most 2^(13n/8). Take h=floor(n/[64(s+1)]). For any j≤h we have js≤n/64 and j≤n/64. When j≥1 the entropy estimate
```
log_2 binomial(n+j,j) ≤ j log_2(e(n+j)/j)
                      ≤ (n/64) log_2(65e) < n/8
```
uses monotonicity of x log(e(n+x)/x) for x>0; at j=0 the logarithm vanishes. Since C=Θ(2^(2n)/n²), the finite bound is exponentially small uniformly for each of the chosen cuts, even after summing over j. A union bound over cuts shows that, except on an exponentially small event, **every successful run** crosses each central cut more than h times. There are at least n/3 such cuts for large n, each requiring distinct input-head moves, giving at least n²/[192(s+1)] moves. No independence across cuts is needed. This establishes the claimed tail and expectation.

## Comparisons and checks

The use of a crossing transcript to constrain a computation is the classical method of [Hennie](https://ntrs.nasa.gov/citations/19660035639). Here the input is read-only, the machine may have external bounded workspace, and success is a relational factor output rather than recognition of a language. The arithmetic cut-incidence count and handling of output bits from both sides supply the lower bound in this model. See [the fixed-pass note](FactorStreamingBlocks.md) for related branching-program and communication references and [the permuted-bit result](FactorPermutedBits.md) for a different restriction. The prime pool uses the classical prime number theorem, for which [Rosser–Schoenfeld](https://doi.org/10.1215/ijm/1255631807) gives primary prime-count context. No priority claim is made for the crossing-sequence method.

[The toy checker](verify-factor-adaptive-head.js) checks cut degrees, the per-schedule bound, and finite crossing-schedule counts on artificial prime pools. The replay covers 81,952 degree increments over 1,266 generated prime-pair edges, 3,685 transcript/schedule classes, and 720 adaptive local-rule simulations. The checker has no factoring routine. This restriction on moving one input head is essential to the summation over cuts; the proof says nothing about the cost of machine steps that jump to arbitrary input positions.
