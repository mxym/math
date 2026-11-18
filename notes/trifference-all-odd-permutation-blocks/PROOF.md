# All-odd blocks and permutation blocks for three-way zero-error hashing

**AI-assisted research note, November 2026.** This is a lower bound, not an exact solution of the trifference problem. See [the review](REVIEW.md) for the scope of independent internal checking; there has been no external peer review. Logs are base 2. For fixed integer `q≥3`, write `M(q,N)` for the largest size of a subset of `[q]^N` in which every **three distinct words** have at least one coordinate with three different symbols, and `R(q)=limsup_N (log M(q,N))/N`. The ternary trifference rate is `R(3)`. Put `b=(3q−2)/q²`, `B(q)=−(log b)/2`. These are rates in bits per symbol, not base-q rates.

## Statements

1. `R(3) ≥ (1/88) log(2546192880000/5441833) = 0.214043381779779… > 0.21404`.
2. For every `q≥4`, `R(q)>B(q)+1/350`. Furthermore `liminf_(q→∞) [R(q)−B(q)] ≥ (1/2)log(3/e)`. In the latter limit `N→∞` at *fixed* `q` first. These bounds do not determine any true rate.

## Sampling/alteration, and the ternary reduction (known steps)

For any finite nonempty block `C⊆[q]^n`, let `F` be the probability that three i.i.d. uniform draws from `C`, **with replacement**, have no separating coordinate. Assume `F<1`. In `k` independent block positions, a fixed unordered triple of distinct sample indices has failure probability `F^k`. Draw `M=floor(F^(−k/2))` independent words of `C^k`. The expected number of bad index triples is `binom(M,3)F^k ≤ M/6`. For some realization remove one index per bad triple; at least `5M/6` indices survive. For all large `k` there are at least three; duplicate surviving words are impossible, since these two indices together with any third would be bad. This proves

`R(q) ≥ −log F/(2n)`.

Padding with fixed symbols handles arbitrary large lengths too. For the ternary reduction identify the 9 letters with `F₃²`, and encode `(a,b)` as `(a,b,a+b,a+2b)`. These four linear forms have the four different possible kernel directions. For any three distinct points there are at most three pairwise-difference directions, so one form separates all three. Thus `R(3) ≥ R(9)/4`. These two reductions are not new: see Xing–Yuan's sampling method, Yuan–Zhu v2 Lemma 2.1, and Körner–Marton's Tetra concatenation (Yuan–Zhu v2 Lemma 2.5).

## The all-odd block, and counting bad triples

Take `n=q+2` and `C={words in which every one of the q symbols occurs an odd number of times}`. One symbol occurs three times and the other `q−1` appear once, so `S=|C|=q n!/6`. Let `D(q,n)` be the number of ordered triples in `C³` that have no separating coordinate.

For any word `x`, let `p(x)∈F₂^q` be its vector of count parities. The indicator `1[p(x)=1⃗]` is `2^(−q)∑_α (−1)^(α·1⃗+α·p(x))`, summed over all `α∈F₂^q`. Insert three copies, with masks `α,β,γ`. Each symbol `i∈[q]` has type `s=α_i+2β_i+4γ_i`; denote the type multiplicities by `c_0,…,c_7` and `h_j=∑_s c_s (−1)^popcount(s AND j)`. The row nonseparation indicator is `[x=y]+[x=z]+[y=z]−2[x=y=z]`. Its signed alphabet sum is

`L=h_3 h_4+h_5 h_2+h_6 h_1−2h_7`.

Rows factor, and there are `q!/∏c_s!` mask triples with the given type counts. Therefore, for arbitrary length `n`,

`D(q,n)=2^(−3q) ∑_{c_0+⋯+c_7=q} [q!/∏c_s!] (−1)^(∑c_s popcount(s)) L^n`.  (1)

Hence `F=D/S³`. At `q=9,n=11` equation (1) gives

* `S=59875200`, `D=458769821652172800`;
* `F=5441833/2546192880000` in lowest terms.

The associated nine-letter rate is `−(log F)/22`. Dividing by four proves statement 1. For a rounding-free comparison with `5351/25000`, multiply exponents: `2546192880000^25000 > 2^(88·5351) · 5441833^25000`.

An independent nonnegative recurrence calculates the same integer. After each row, store counts of alphabet symbols in each of eight parity states (one bit per word), starting `(q,0,…,0)`. In a nonseparating row either choose one symbol of state `i` (weight `c_i`) and toggle its bits by 7, or choose in order a repeated symbol of state `i` and a different singleton of state `j` (weight `c_i(c_j−[i=j])`), toggling their parities by `(3,4)`, `(5,2)`, or `(6,1)` depending on which pair agrees. Each possible labeled row appears exactly once; the number of choices depends only on the state counts. Combine sequences with equal resulting count vectors. The final entry `(0,…,0,q)` is `D`; after `k` rows the sum of all entries is `[q(3q−2)]^k`. These two exact integer approaches appear in `cert.py`; neither optimizes or uses floating point for a decision.

## A closed permutation formula for large alphabets

Now take the length-q block `C=S_q` in one-line notation. Relabel all symbols to fix the first of the three sampled permutations to be the identity. Let `σ,τ` be the others. For a nonseparating pair partition positions into `A` (only `τ` differs from identity), `B` (only `σ` differs), `C'` (both differ but coincide), `D'` (both fix the position). The common image of `C'` under `σ,τ` misses `A,D'` (fixed under `σ`) and `B,D'` (fixed under `τ`), hence equals `C'`. It follows that `σ` restricts to a derangement on `B`, `τ` to a derangement on `A`, and their common restriction on `C'` is a derangement. Each such set partition and three derangements conversely give exactly one nonseparating pair. Writing `!j` for derangements (`!0=1`), the count for fixed first permutation is

`∑_{a+b+c+d=q} q!/(a!b!c!d!) · !a !b !c = q! [z^q] e^(−2z)/(1−z)^3`.

Indeed inclusion-exclusion gives `!j/j!=∑_{u=0}^j (−1)^u/u!`, whose ordinary generating function is `e^(−z)/(1−z)`. With `H_q=[z^q] e^(−2z)/(1−z)^3`, this proves `F_perm=H_q/q!`, where `H_q=∑_{j=0}^q (−2)^j binom(q−j+2,2)/j!`.

A useful nonnegative estimate is `1≤H_q≤binom(q+2,2)`. Lower bound: take `σ=id` and any `τ`. For the upper bound allow every coordinate at which all letters agree to be assigned to any one of the three pair-equality types. For a prescribed partition `I,J,K`, impose `σ=id` on `I`, `τ=id` on `J`, `σ=τ` on `K` (no exclusion of fixed points). Then `σ(K)=τ(K)=K` by the same image argument; independent unrestricted permutations on the three sets determine exactly `i!j!k!` pairs. For each size triple there are `q!/(i!j!k!)` partitions. Summing gives an upper bound of `binom(q+2,2)q!` pairs, as desired. Hence `(log H_q)/q→0`. Stirling yields

`−(log F_perm)/(2q)−B(q) → (1/2)log(3/e)`.

Only the explicit achievable expression is asserted to converge. Applying the sampling bound proves the liminf assertion about `R(q)`.

## Explicit all-alphabet gap

For `4≤q≤19`, apply (1) at `n=q+2`. For `20≤q≤255`, take the permutation block at `n=q`. For each calculate `u/v=F/b^n` in lowest terms and check the integer inequality `v^350 > 2^(2n) u^350`. This is exactly the desired strict gap for the given block. The 252 finite cases are completely specified by the displayed finite sums and checked by `uniform.py`; the smallest gain among the first group is about `0.00287861057015` at `q=4`. A separately written implementation reproduces all finite checks; see [the audit](REVIEW.md).

For `q≥256`, `q!≥(q/e)^q` (for example integrate the increasing natural logarithm from 1 to q), and `H_q≤(q+2)^2`. The permutation gain is thus at least

`(1/2)log((3−2/q)/e) − log(q+2)/q`.

Use `e<11/4`, `(3−2/256)/(11/4)>17/16`, and `17^12>2·16^12` to bound the first term strictly above `1/24`. Also the function `ln(x+2)/x` decreases on `x≥256` since `x/(x+2)<1<ln(x+2)`. The exact inequality `258^30<2^256` then shows that the second term is `<1/30`. The resulting gap `>1/120` is more than enough. This proves statement 2.

## Verification/limitations

Run `python3 -B -O cert.py` and `python3 -B -O uniform.py` from this directory, standard library only. Numeric rates are for readability; the checks use exact integers/rationals and raise real exceptions, not removable `assert` statements. The random choices are only for the existence proof, not part of the verifier. The rate claim is not an efficient deterministic infinite construction and not a claim about linear codes. The upper bound, the exact exponential capacity and the maximum sizes at general finite lengths remain undetermined. Scope and prior-art comparisons: see `STATUS.md`.
