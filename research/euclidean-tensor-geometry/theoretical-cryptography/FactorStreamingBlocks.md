# Streaming lower bounds for outputting a factor of a balanced semiprime

A sequential algorithm receives **all ordinary input bits** here, not just bounded advice or hidden-ring probes. Working memory is limited and revisiting input is permitted only by prescribed sequential passes. Even with an append-only output tape excluded from workspace, producing one factor of a random balanced semiprime with constant success takes linear space in one pass, and has a linear space–pass product for sublinearly many passes. There is no bound here for ordinary random-access factoring.

## Model and finite theorem

Fix n≥3 and P=2^(n−1). Let S be any pool of M≥2 n-bit primes. Choose an unordered pair of distinct primes from S uniformly and input N=pq as a padded 2n-bit binary word. Write N=P H+L, where 0≤L<P. Each prescribed pass visits the high block H (n+1 bits) and the low block L (n−1 bits); either order is allowed as long as the order is fixed before the input. Within a pass the algorithm is sequential on the bits. The upper bounds on success below in fact allow **arbitrary local computation within each visit with the whole current block**, as long as the persistent state at each visit boundary has at most 2^s possibilities. This stronger allowance only weakens the lower bound against genuinely s-bit machines. There are r visits to each block and at most 2r−1 state handoffs. The output tape cannot be read, and its length, timing, or indices cannot serve as uncharged persistent state. Success means the tape holds exactly the n-bit binary representation of either p or q. Work after the final input bit may append further output using the final state, and is assigned to the last visit. The same fixed accounting covers public randomness or fresh private coins.

Write C=binomial(M,2), V_H=3P, and V_L=P/2. Tighter counts of the actually occurring blocks can replace these constants. Then the success probability σ of any such r-pass algorithm is at most
```
min(1, 2^((2r−1)s) / C ×
  Σ_(a=0..n) binomial(a+r−1,r−1) binomial(n−a+r−1,r−1)
              min(V_H·2^(n−a), V_L·2^a)).
```
If output is only appended after the last block is read, the sum can simply be replaced by V_B, the number of possibilities for the last block (bounded by V_H or V_L as appropriate).

For the full pool of n-bit primes, the prime number theorem gives M∼P/log P. Therefore, for any fixed target success σ≥δ>0,
```
(2r−1)s ≥ ceil(n/2) − 2 log_2 n − log_2 binomial(n+2r−1,2r−1) − O_δ(1).
```
In particular rs=Ω(n) for any r=o(n), since the last logarithm is o(n) by the usual binomial bound. With output deferred, the stronger bound (2r−1)s≥n−2 log_2 n−O_δ(1) holds for arbitrary r. For r=1 it is also a one-way communication lower bound where the receiver has free access to the retained half of the input at the time it produces the full answer.

## Arithmetic incidence

Think of a valid input as an edge between H and L, labelled by both of its prime factors. The graph is simple by uniqueness of N from the two blocks and uniqueness of its unordered prime pair. Each H lies in [P,4P), and each L is odd, giving V_H and V_L above. The key observation is that **at either endpoint, any fixed prime label occurs on at most one incident edge**.

* At a fixed H, a fixed factor p forces its mate into the half-open real interval [PH/p,P(H+1)/p), of length P/p≤1. It contains at most one integer.
* At a fixed L, every p in the pool is odd and hence invertible modulo the power of two P. Its mate is forced into one residue class modulo P, and [P,2P) contains exactly one integer of that class.

No uniformity of prime products across blocks is assumed.

## Counting the distributed output

Fix the random tapes for all visits. For fresh randomness this can be realized by an independent tape for each visit; length of earlier random use is then not information supplied to the next visit. A common random seed independent of the input can instead be fixed directly. Once the state handoff transcript is fixed, the output string of any visit depends only on that visit's local block (and its fixed visit index). The number of such transcripts is at most 2^((2r−1)s). This remains true if a prescribed reversal of directions makes two successive visits use the same block.

On every successful run the total output length is n. Fix additionally the vector of lengths written in the 2r visits. This determines which output positions come from each block. If a bits in total come from the high block visits, then for a given H those a positions have fixed bits. There are at most 2^(n−a) candidate integers with those bits. The incidence observation makes at most that many successful edges incident to H. Thus the number of successes with that transcript and schedule is at most V_H·2^(n−a). Using the low block gives the other bound V_L·2^a. Neither step assumes the pieces of output or block values are probabilistically independent. In particular the vector of output lengths may depend on the input; it is counted, not treated as free side information.

For given a, there are binomial(a+r−1,r−1) ways to distribute those bits among the r high visits and binomial(n−a+r−1,r−1) ways for the low visits. Summing proves the finite bound. For its simpler consequence replace each minimum by 3P·2^floor(n/2) and sum the schedule count to binomial(n+2r−1,2r−1). Divide by C and average over all tapes. If there is no early output, the completed factor for a given last block and transcript is unique; the incidence observation gives at most one success there. This proves the deferred-output version as well.

## Stronger one-pass bound with online output

Let V_A and V_B bound the counts of first and second blocks, respectively. For 1≤k≤n let W_k be the largest number of primes in S with a common prefix of length k in their ordinary n-bit representation. For one pass, every k gives
```
σ ≤ min(1, [V_A W_k + V_B·2^s(2^k−1)]/C).
```
Indeed fix the coins. For each first block that appends at least k bits before the cut, those first k bits restrict the candidate factor to at most W_k primes; the incidence property bounds the number of successes on that block by W_k. For a first block that appends fewer than k bits, the second block together with its starting state and the already written bits determine the final output. There are at most 2^k−1 such short strings and at most 2^s states. For any fixed second block, each state and string yields at most one successful adjacent edge. This counts also variable lengths and append-only output before or after the cut.

In the full prime pool, W_k≤2^(n−k) immediately. Taking k=ceil(2 log_2 n)+O_δ(1) makes the long-early-output term at most δ/2 for large n, giving s≥n−4 log_2 n−O_δ(1). This version does not use a theorem on primes in short intervals; it works for any common predetermined order of the factor output bits.

A refinement for ordinary most-significant-bit-first factor output uses the [Montgomery–Vaughan Brun–Titchmarsh bound](https://doi.org/10.1112/S0025579300004708) with modulus one. A k-bit prefix specifies one interval of length Y=2^(n−k); that theorem uniformly bounds its prime count by O(Y/log Y). The same estimate holds for least-significant-bit-first factor output by using the bound with modulus 2^k, interval length P, and Euler totient 2^(k−1) for the odd residues in question. For k=ceil(log_2 n)+O_δ(1), this gives W_k=O(P/(2^k n)), and the early-output term again costs at most δ/2. The memory lower bound in these usual output orders is consequently
```
s ≥ n − 3 log_2 n − O_δ(1).
```
The leading constant in this lower bound is expressed in terms of the bit length of one prime, approximately half the input length. The bound is on memory state, not runtime, and it never charges n bits merely for the existence of the write-only output tape.

## Scope and related work

The two-party state simulation is the standard communication-complexity method originating with [Yao](https://doi.org/10.1145/800135.804414); [Ablayev–Karpinski](https://eccc.weizmann.ac.il/eccc-reports/1998/TR98-011/) use one-way communication for lower bounds on ordered branching programs computing **multiplication**, a different function and direction. [Beame, Jayram and Saks](https://homes.cs.washington.edu/~beame/papers/branch.pdf) study time–space tradeoffs in broader branching-program models; the bound here specifically counts handoffs and the splitting of a factor output, not general adaptive input access. The prime pool asymptotic uses the ordinary prime number theorem; [Rosser–Schoenfeld](https://doi.org/10.1215/ijm/1255631807) is a reference for the classical prime-count context. No priority claim is made for the streaming/communication method. The two-block incidence statement and its append-only-output bound are the content of this note.

An input head that freely alternates between arbitrary input positions, a factor oracle, extra storage, reading the output, or externally visible timing are not part of the model. The statement does not rule out classical polynomial-time algorithms for ordinary factoring. The [exact toy checks](verify-factor-streaming-blocks.js) work only with products generated from explicitly small prime pools and check the proof's finite combinatorial steps, not an algorithm for factoring. The replay covers 13,357 generated prime-pair edges over eight tiny pools, 76,480 local bit-pattern checks, 80 exact schedule identities, and 768 local-rule simulations.
