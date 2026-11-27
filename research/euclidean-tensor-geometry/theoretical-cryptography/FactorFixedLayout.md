# Factor-output lower bounds for every fixed binary layout

**Theorem.** Let the input be the padded $2n$-bit word of $N=pq$ for a uniformly random unordered pair of distinct $n$-bit primes. Fix any permutation of the input positions, potentially chosen adversarially before the input is drawn. A classical machine's successful output is the exact $n$-bit word of either factor in a prescribed bit order; it may append output without charge, but may not read that output back or retain its current length, its timing, or other side information for free.
 
1. With one pass in the fixed order and constant success probability $\delta>0$, workspace of at least
   $$
   \left(\frac{2}{\log_2 3}-1\right)n-O_\delta(\log n)
   $$
   bits is necessary. This holds even if the first and second half-views are each locally accessible for free during their visit. If output must be deferred to the second view, the lower bound is $n/\log_2 3-O_\delta(\log n)$.
2. If $r=o(n)$ passes repeatedly visit the same two half-views, in a prescribed alternating or per-pass order, with output interleaved arbitrarily, then $(2r-1)s\ge (1/\log_2 3-1/2)n-o(n)$ for an $s$-bit handoff state and constant success.
3. Let a single read-only head start at a fixed physical position and move only to adjacent positions, with directions chosen adaptively. Its input positions are laid out in any fixed permutation as above. If it has at most $2^s$ internal configurations, there is an absolute $c>0$ such that
   $$
   \Pr\big[\text{correct factor output and fewer than }c n^2/(s+1)\text{ head moves}\big]
   \le 2^{-\Omega(n)}.
   $$
   In particular the expected number of moves times $s+1$ is $\Omega_\delta(n^2)$ at constant success.

The constants are uniform over the fixed permutations. The layout is independent of the draw of $N$, the head position at a handoff is prescribed by the cut and direction, and internal state includes all persistent information besides that position. These statements do not cover input-dependent arbitrary read orders, random access, writable input, rereadable output, or multiple input heads.

## A modular injection for each fixed submask

For a set $J$ of $k$ positions from $\{0,\ldots,2n-1\}$, write each assignment on $J$ as its integer sum $\sum_{j\in J}b_j2^j$. Every nonzero formal difference between assignments has the form
$$
d_{\boldsymbol\epsilon}=\sum_{j\in J}\epsilon_j2^j,\qquad
\boldsymbol\epsilon\in\{-1,0,1\}^J\setminus\{\mathbf0\}.
$$
It is a nonzero integer: the largest present power of two exceeds the sum of all smaller powers, even if every lower sign is opposite. Its absolute value is $<2^{2n}$. It has at most two distinct $n$-bit prime divisors for $n\ge3$, since a product of three such divisors is at least $2^{3(n-1)}\ge2^{2n}$. Thus there are at most $2(3^k-1)$ exceptional primes modulo which two assignments on $J$ coincide. This counts formal signed sums and does not require different differences to have different integer values.

Let one view observe some positions and miss $w\ge k$ positions. Select any fixed $k$-subset $J$ of the missing positions. For a nonexceptional factor $p$, for each assignment of the other $w-k$ unknown bits the condition $N\equiv0\pmod p$ leaves at most one assignment on $J$. Hence for each observed word, the number of incident valid products carrying that factor label is at most $2^{w-k}$. The proof even bounds how many words divisible by $p$ have that view. The set of exceptional primes depends on the submask, but not on the observed word or on a machine.

For $L_0$ prescribed submasks of size $k$, with $M$ available $n$-bit primes, the fraction of prime-pair inputs meeting the union of exceptions is at most
$$
\frac{4L_0(3^k-1)}{M}. \tag{1}
$$
Each prime label is marginally uniform when the unordered pair is randomly ordered, so this follows by taking a union bound over the two labels. We discard those inputs for the degree arguments below. If $C=\binom{M}{2}$ is the original input count, the prime number theorem gives $M=\Theta(2^n/n)$ and $C=\Theta(2^{2n}/n^2)$; all success probabilities below use this original denominator.

## One pass and a fixed number of repeated views

Let $A,B$ be the first and second half-views. Think of each good input as an edge from its first observed word to its second, with the two prime labels. Take $k=\lfloor\log_3(M/n^3)\rfloor$ for all sufficiently large $n$. By (1) with $L_0=2$, the discarded probability is $O(n^{-3})$. The two degree bounds are both $D=2^{n-k}$, and each view has at most $2^n$ possible words.

Fix independent coin streams before counting. If output is deferred, each final view and incoming state of $s$ bits determines at most one output factor. There are at most $2^{n+s}D$ successful good edges, yielding $s\ge k-2\log_2 n-O_\delta(1)$.

For online output, choose a threshold $b$. If a first view writes at least $b$ bits, for any such view word the first $b$ bits are fixed. At most $2^{n-b}$ labels have that prefix. Thus there are at most $2^nD\,2^{n-b}$ successful good inputs of that type. If it writes fewer than $b$ bits, use the other side: each second view word has $2^s$ possible incoming states and at most $2^b-1$ possible earlier strings. Each combination determines a complete output and hence at most $D$ good edges. Taking
$b=\lceil\log_2 D+2\log_2 n+O_\delta(1)\rceil$ with the constant large enough makes the first case contribute at most $\delta/4$ of all inputs. The second case must then contribute constant probability, which yields
$$
s\ge n-2\log_2 D-4\log_2 n-O_\delta(1)
=2k-n-O_\delta(\log n).
$$
These counts apply to every fixing of the relevant random tapes, so averaging preserves the bound.

For a run with $2r$ visits to the prescribed two views, fix the transcript at its handoffs and the vector of the $2r$ output-piece lengths. If all visits on one side write a total of $a$ bits, then for any view word those bits are fixed on that side, and on the other side the remaining $n-a$ bits are fixed. Thus the number of successful good edges for this transcript and length vector is at most
$$
2^nD\min(2^{n-a},2^a)\le2^{(5/2)n-k}.
$$
For exactly $2r$ visits there are at most $2^{(2r-1)s}$ transcripts and $\binom{n+2r-1}{2r-1}$ length vectors. Early halting can be treated by silent padded visits using one additional halt bit; the cost $2r-1$ in the logarithmic transcript bound is $o(n)$. For $r=o(n)$ the logarithm of the length-vector count is $o(n)$. Division by $C$ and averaging over the random tapes prove the stated repeated-view bound.

## An adaptive moving head on any fixed layout

Take $k=\lfloor3n/5\rfloor$. For each physical cut after $j$ cells with $3n/4\le j\le5n/4$, select a $k$-subset of positions on each side, which is the submask of missing positions for the other side. The number of such subsets is $O(n)$. Equation (1) discards at most $O(n^2 2^{-(1-(3/5)\log_2 3)n})=2^{-\Omega(n)}$ of inputs for the entire layout. For a cut with side lengths $j,2n-j$, the good factor-label degrees have bounds $D_A=2^{2n-j-k}$ and $D_B=2^{j-k}$. Multiplying by the possible numbers of view words gives $2^jD_A=2^{2n-j}D_B=2^{2n-k}$.

Fix a cut, and partition a run into its visits to the two sides. Given initial state, the side's word and a fresh coin tape for a visit, its actions before the next crossing or halt are determined. Using independently fixed tapes per visit implements the same law as fresh coins during the run; a public random tape can instead be conditioned upon if a reusable position in it is charged to internal state. For a run with $m$ crossings, there are at most $2^{ms}$ handoff transcripts and $\binom{n+m}{m}$ schedules of output lengths. For any one of these choices, with total $a$ bits written on one side, the two sides bound the number of surviving successful input edges by the smaller of $2^{2n-k+n-a}$ and $2^{2n-k+a}$. This is at most $2^{(5/2)n-k}$, independent of $j$. It does not charge the time or amount of output as storage; it only counts schedules compatible with a successful length-$n$ output.

Put $h=\lfloor n/(256(s+1))\rfloor$. For $0\le m\le h$, $ms\le n/256$ and
$$
\log_2\binom{n+m}{m}\le (n/256)\log_2(257e).
$$
The latter follows from the usual binomial upper bound for $m\ge1$ and monotonicity in $m$; it is trivial at $m=0$. Because $k-n/2\ge n/10-1$, the log bound plus $ms$ is strictly less than $k-n/2$ by a positive constant times $n$ for sufficiently large $n$. Summing over $m\le h$, dividing by $C$, and averaging over the tapes gives an exponentially small probability of a successful good-input run with at most $h$ crossings of that cut. Union over the central cuts, and add the discarded input mass. Otherwise each successful run crosses every such cut more than $h$ times. An adjacent move crosses only one cut; there are at least $n/3$ central cuts for sufficiently large $n$, giving at least $n^2/(768(s+1))$ moves.

## Context and verification

- [Ablayev–Karpinski](https://theory.cs.uni-bonn.de/Zope/English/csreports/report_1998/paper_85184/abstract.html) study randomized ordered read-once branching programs computing **multiplication** and distinguish verification from computing that product. The task here is output of a factor of the supplied product. [Bourgain's prescribed-digit prime counts](https://arxiv.org/abs/1307.0398) concern the distribution of primes, not the number of divisible words with a prescribed projection and a specified prime label. The modular injection above is a direct finite bound and does not need a prime digit theorem.
- [Hennie's crossing-sequence method](https://ntrs.nasa.gov/citations/19660035639) supplies the classical transcript framework used in [the ordinary-layout theorem](FactorAdaptiveHead.md). The new point is the mask-uniform arithmetic input for every layout fixed before the random primes. The previous [random-permutation theorem](FactorPermutedBits.md) gives stronger quantitative workspace bounds for a typical layout, but did not give a linear online bound for the most evenly interleaved fixed layouts. No theorem here chooses a single prime pool that works simultaneously for all exponentially many submasks; the exceptional fraction is uniform but the exceptional set depends on the fixed layout.
- [The small exact checker](verify_factor_fixed_layout.js) tests the exceptional-prime lemma, local degrees and schedule bounds on fixed toy instances only. There is no algorithm for factoring arbitrary integers.
