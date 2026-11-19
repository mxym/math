# A length-64 counterexample to three-deletion entropy maximality

**Yongxian Zhang.** Given a fixed *received* binary word under three uniformly chosen deletions from a uniform longer input, the alternating observation need not maximize the posterior input Shannon entropy. Write
\[
A=(01)^{32},\qquad B=(01)^{16}(10)^{16}.
\]
Both have length 64. The two middle ones of $B$ form its only nonsingleton run.

**Proposition.** In the model of [Ma and Zhang, Conjecture 6.2, first assertion](https://arxiv.org/html/2611.01064v1),
\[
  45/383240 < H_{D,3}(B)-H_{D,3}(A)<46/383240\quad\text{bits}.
\]
Complementing all transmitted and received bits preserves every multiplicity, so $B$ strictly beats both alternating observations.

**Reduction to an integer comparison.** An input $x$ has length 67. Write $e(y,x)$ for the number of ways to retain 64 ordered sites of $x$ spelling the received $y$. Its posterior mass is $e(y,x)/Z$, where $Z=2^3\binom{67}3=383240$: each choice of three positions and their three bit values extends $y$ to one input with a specified deletion mask. This is Ma and Zhang's Lemma 2.1. If $h_y(j)$ counts inputs with positive multiplicity $j$, put $Q_y=\prod_{j\ge1}j^{j h_y(j)}$. Then
\[
 H_{D,3}(B)-H_{D,3}(A)=Z^{-1}\log_2(Q_A/Q_B).
\]

**Finite certificate.** The complete positive multiplicity histograms are:

|Multiplicity $j$|# inputs for $A$|# inputs for $B$|
|---:|---:|---:|
|1|4|10|
|2|192|372|
|3|128|189|
|4|4096|5735|
|6|4032|3908|
|8|41664|37820|
|9|0|62|
|10|0|1|
|12|0|1953|
|34|0|4|
|65|2|3|
|66|0|60|
|67|0|2|
|68|0|62|
|99|0|2|
|128|64|1|
|129|2|0|

Each column counts 50,184 positive-mass inputs and sums to 383,240 when weighted by $j$. The first column also follows from Ma–Zhang's Theorem 5.3. Canceling the prime factors from these columns gives
\[
 \frac{Q_A}{Q_B}=
 \frac{2^{76566}43^{258}}{3^{28089}5^{75}11^{4158}13^{65}17^{4352}67^{134}}.
\]
Integer division gives floor 49,091,150,926,384, between $2^{45}$ and $2^{46}-1$. This proves the strict bounds without numerical evaluation of logarithms.

Here is the complete logic of two enumeration methods:

1. **Insert at each final triple.** For each $0\le i<j<k<67$ and each of eight bit assignments, interlace the three assigned bits and the 64 bits of $y$, in order, then count the resulting 67-bit word. Each (input, mask) occurs exactly once. A frequency-of-frequencies gives the table. [verify.py](verify.py) does this by inserting bits at increasing positions from the low-bit end: a later insertion cannot move an earlier inserted position. All outputs have a known common length, so integer storage preserves leading zeroes unambiguously. The separately written [internal verifier](verify_integer_insertion.py) also checks the sign.
2. **Generate each host once.** Greedily match the letters of $y$ in $x$. Before each first matching position the skipped bits can only be opposite to the letter being matched; after the last match the tail is arbitrary. Distribute some $t\in\{0,1,2,3\}$ such skipped bits among the 64 pre-match gaps and choose the $3-t$ tail bits. This parametrizes all positive-mass hosts bijectively. To count their *entire* fibers (not just the greedy embedding), scan host sites left to right, retaining a state for each number $0\le d\le3$ of skipped sites. After processing $i$ sites that state has matched $i-d$ received letters. On the next site one can skip if $d<3$, or retain if the next required letter agrees; add path counts in each successor state. The final state $d=3$ counts all embeddings. [greedy.py](greedy.py) implements this second construction, recovers both histograms, and certifies the displayed integer quotient.

This is a counterexample to a universal maximizer conjecture, **not** a determination of which received word maximizes the entropy at length 64, or of the smallest length where alternation fails. It is consistent with the original exact three-deletion comparisons through length 12. It is separate from inferring a *shorter* input after three insertions.
