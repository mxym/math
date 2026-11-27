# Short factorial-divisor sums via controlled binary branching

Research note, 27 November 2026. For \(N=n!\), let \(h(N)\) be the smallest \(h\) such that each integer from \(1\) to \(N\) is a sum of at most \(h\) **distinct** positive divisors of \(N\).

**Theorem.** As \(n\to\infty\),
\[
                 h(n!)\ll (\log n)^4(\log\log n)^2 .
\]
In particular, in the strict-power formulation of Erdős #18(c), every fixed exponent exceeding \(4\) suffices.

[Howe, Huffman, Kohlmeyer and Kruer, *Harmonic dyadic shifts and short sums of factorial divisors*, §1](https://hexagonmath.org/2611.00748v1) already give the affirmative polylogarithmic conclusion, with \(h(n!)=O((\log n)^9)\). This is a quantitative improvement, not a new qualitative resolution. The local step below replaces entropy convolution by a binary branching identity and a support covering argument. The use of divisor digits, positive quotient lifting, binary carrying, and a factorial radix follows the approach credited in their §§3–6; we give the full transfer because the improved height of the local representative is needed. We do not assert a matching lower bound.

All logarithms are natural unless marked \(\log_2\). The argument uses the prime number theorem only in the weak form \(\pi(y)\ge y/(2\log y)\) for sufficiently large \(y\).

## 1. A binary branching identity

For \(D\subseteq\{0,\ldots,2^\ell-1\}\), read bits from the least to the most significant. Call \(I\subseteq\{0,\ldots,\ell-1\}\) controllable if there is a strategy that takes freely specified bits at positions in \(I\), chooses bits at positions not in \(I\) using only previously exposed bits, and always finishes in \(D\). Let \(\mathcal C(D)\) be the set of its controllable masks. Then
\[
                       |\mathcal C(D)|=|D|.
 \tag{1}
\]
Split the first bit into subtrees \(D_0,D_1\) on the remaining \(\ell-1\) bits. A mask omitting the first bit belongs to the union of their families, since one can choose that bit. A mask including the first bit has its remaining mask in the intersection, since either value must be handled. The two cases are disjoint, so their count is \(|\mathcal C(D_0)|+|\mathcal C(D_1)|\). In dimension zero the empty family has no masks and the singleton has the empty mask, proving (1) inductively.

For \(0<u\le1\), if \(\log |D|\ge c_0\ell u\) for a positive absolute constant \(c_0\), then (1) gives a mask of size
\[
                    |I|\gg_{c_0}\frac{\ell u}{\log(e/u)} .
 \tag{2}
\]
For clarity, if all masks have at most \(d\) marked positions, their number is at most \(\sum_{i\le d}\binom\ell i\le e^{\ell H(d/\ell)}\) for \(d\le\ell/2\), where \(H(s)=-s\log s-(1-s)\log(1-s)\). This binomial bound follows by weighting the binomial expansion with \(s=d/\ell\) (the case \(d=0\) is immediate). Since \(H(s)\le s\log(e/s)\), choose a sufficiently small \(a>0\) depending only on \(c_0\); at \(s=au/\log(e/u)\) this entropy is bounded by \(a(2+\log(1/a))u<c_0u\). Therefore \(d\) cannot lie below \(\ell s\). If \(d>\ell/2\) the desired bound already holds. The controlling strategy, not just an unrestricted coordinate projection, will allow us to sum binary digits in the presence of carries. See [Roland Walker, *Tree Dimension and the Sauer–Shelah Dichotomy*, Theorem 1.3](https://arxiv.org/html/2203.12211), for the corresponding binomial bound in leveled tree dimension; the short fixed-mask count above also specifies the strategy convention used here.

## 2. Many actual divisor digits at each scale

Fix a large integer \(k\), put \(m=64k\), \(T_k=\log k\), and set
\[
 D_\ell=\{0\}\cup\{d: d\mid m!,\ 1\le d<2^\ell\}.
\]
For \(4\log_2m\le\ell\le k/2\), define \(q_\ell=\log(ek/\ell)\). We have \(1\le q_\ell\le T_k\) for all sufficiently large \(k\) in this range, and
\[
              \log |D_\ell|\gg \frac{\ell}{T_k}\,q_\ell.
 \tag{3}
\]
Indeed, let \(v=\lfloor(\ell-1)/\log_2m\rfloor\). Then \(v\ge \ell/(2\log_2 m)\), and products of \(v\) distinct primes at most \(m\) are all distinct divisors of \(m!\) and at most \(2^{\ell-1}\). With \(P=\pi(m)\), one has \(P/v\ge 32k/(\ell\log 2)\ge ek/\ell\) for large \(k\). The estimate \(\binom{P}{v}\ge (P/v)^v\) gives (3). By (2), there is a controllable mask \(I_\ell\) for each such \(D_\ell\) with
\[
           |I_\ell|\gg \frac{\ell q_\ell}{T_k\,\log(eT_k/q_\ell)} .
 \tag{4}
\]

## 3. Cover every output position with single-divisor inputs

For an output bit \(j\in\{0,\ldots,k-1\}\), use the distance \(d(j)=\min(j,k-1-j)\) to the nearer end. Let \(\ell_0\) be the smallest dyadic power at least \(4\log_2m\), so \(\ell_0=O(\log k)\). Each position \(j\) with \(d(j)<\ell_0\) can use its own variable in \(\{0,2^j\}\); their total number is \(O(\log k)\).

For each dyadic \(\ell\ge\ell_0\), the positions with \(\ell\le d(j)<2\ell\) split into at most two consecutive intervals, one on each side of the midpoint, each of length at most \(\ell\). Only \(\ell\le(k-1)/2\) occur. Fix one such interval \([L,U]\). An input \(2^a D_\ell\) has controllable positions \(a+I_\ell\). We select its shift \(a\) from \(L-\ell+1,\ldots,U\). This range has at most \(2\ell\) shifts; every shift is nonnegative and satisfies \(a+\ell\le k\), because \(L\ge\ell\) and \(U\le k-1-\ell\). For every output \(j\in[L,U]\), there are exactly \(|I_\ell|\) shifts in the range such that \(j\in a+I_\ell\), namely \(a=j-i\) for \(i\in I_\ell\). Sample
\[
 r_\ell=\left\lceil\frac{2\ell}{|I_\ell|}\log(2\ell)\right\rceil
\]
independent shifts uniformly from that range. The probability of missing any particular output bit is at most \(1/(2\ell)\); the expected number missed in the whole interval is at most \(1/2\). Thus there is a fixed list of at most \(r_\ell\) shifted inputs covering it. We use a separate list for each interval. Repetitions of inputs are allowed at this stage.

Overall the bank of input variables has size
\[
 W(k)\ll T_k^2(\log T_k)^2 .
 \tag{5}
\]
To see this, (4) bounds each interval cost, including rounding, by \(O(T_k\log\ell\cdot \log(eT_k/q_\ell)/q_\ell+1)\). We have \(\log\ell\le T_k\) and the \(q_\ell\)'s are spaced by \(\log 2\) as \(\ell\) ranges over powers of 2. The function \(q\mapsto\log(eT_k/q)/q\) is decreasing on \([1,T_k]\); its sum over such a progression is \(O((\log T_k)^2)\) by integration. Counting the endpoint variables and both intervals gives (5).

**The bank realizes every residue modulo \(2^k\).** Fix a target output. Proceed in increasing order of output bit \(j\), exposing in every input the bit (if any) at that same output position. Every noncontrollable local bit can be chosen by its fixed strategy from previously exposed lower bits. At least one input has a controllable bit here. Assign all other controllable bits at this output position arbitrarily, then choose that remaining bit so that the parity of the sum of the current bits and the already determined carry agrees with the target. The carry is determined by all lower input bits, not by a choice at the current position. This fixes the output one bit at a time. The chosen input value lies in the corresponding shifted digit set, since its strategy handles all free-bit assignments. The single-bit endpoint variables work the same way.

Each selected nonzero input individually divides \(F(k)!=(66k)!\): the unshifted digit divides \(m!\), and at most \(k\) extra powers of 2 are needed, supplied by the \(2k\) integers after \(m\). Each input is also below \(2^k\) as an integer; here we use the restriction \(a+\ell\le k\), which is why the intervals were chosen by distance from **both** ends. Add \(2^k\) as one extra divisor (also a divisor of \(F(k)!\)) to guarantee positivity even for the zero residue. Thus every residue has a positive representative \(S\) with
\[
  0<S\le (W(k)+1)2^k,\quad
  S\text{ is a sum of at most }W(k)+1\text{ divisors of }(66k)!.
 \tag{6}
\]
Terms in (6) may repeat.

## 4. From residues to exact positive integers

Let a target \(R>0\) have bit length \(T=\lfloor\log_2R\rfloor+1\). For all sufficiently large \(T\), it is a sum of
\[
               O((\log T)^2(\log\log T)^2)
 \tag{7}
\]
distinct divisors of \((70T)!\).

For a current integer \(R_i\) of length \(T_i\) above a fixed large threshold, put \(k_i=T_i-\lceil\sqrt{T_i}\rceil\). Apply (6) to its residue \(R_i\bmod 2^{k_i}\). By (5) we may take the threshold so large that \(W(k_i)+1\le 2^{\sqrt{T_i}-2}\). Consequently \(S_i\le 2^{T_i-2}<R_i\). The next integer
\[
                 R_{i+1}=(R_i-S_i)/2^{k_i}>0
\]
has bit length at most \(T_i-k_i=\lceil\sqrt{T_i}\rceil\). Stop when \(T_i\) falls below the threshold, using a bounded number of copies of \(1\) for the final integer. For sufficiently large \(T_i\), \(\log T_{i+1}\le(3/4)\log T_i\). Thus summing the per-stage bound (5), with \(\log\log T_i\le\log\log T\) at all stages above threshold, proves the bound (7) on terms before making them distinct.

Let \(e_i=\sum_{s<i}k_s\). Lifting a term at stage \(i\) multiplies it by \(2^{e_i}\). The total \(e_i\) never exceeds \(T\), by telescoping \(T_{s+1}\le T_s-k_s\). Every unlifted term divides \((66T)!\). Hence the lifted terms, including terminal copies of \(1\), divide \(2^T(66T)!\). To make the resulting \(w\) terms distinct, group them by odd part and use ordinary binary carrying in each group. The number of terms does not increase. The exponent of 2 in any new term exceeds the allowed maximum for \(2^T(66T)!\) by at most \(\lfloor\log_2 w\rfloor\); this follows since a group has at most \(w\) copies of its largest allowed power of 2. Odd parts are unchanged. For large \(T\), \(T+\lfloor\log_2 w\rfloor\le2T\) by (7), and the \(4T\) integers after \(66T\) supply at least \(2T\) factors of 2. Thus all final terms divide \((70T)!\). They are positive and distinct, proving (7).

## 5. Factorial radix

Factorials are practical with the inclusive convention used here: inductively write a target \(\le n!\) as \(n a+r\), \(0\le r<n\), scale a representation of \(a\le(n-1)!\) by \(n\), and, if \(r>0\), append \(r\), which divides \(n!\) and is below every scaled term. The zero target uses the empty sum.

For large \(n\), put \(c=\log 2/(8\cdot 70)\), \(s=\lfloor cn/\log n\rfloor\), \(m'=n-s\), and \(Q=n!/m'!\). Write a target as \(Qa+r\) with \(0\le r<Q\) and \(0\le a\le m'!\). A positive \(r\) has bit length at most \(s\log_2 n+1\le n/(8\cdot70)+1\), so \(70T(r)\le m'\) for large \(n\). If \(T(r)\) is above the threshold for (7), represent \(r\) using distinct divisors of \(m'!\) of the number in (7); for bounded positive \(r\), use \(r\) itself, which divides \(m'!\) once \(n\) is sufficiently large. All these terms are below \(Q\), as they are positive and sum to \(r<Q\). The distinct divisors representing \(a\) can be scaled by \(Q\), all resulting terms divide \(n!\), and they are at least \(Q\). So there is no overlap and
\[
                h(n!)\le h(m'!)+O((\log n)^2(\log\log n)^2).
\]
At each such step the potential \((\log n)^2\) decreases by at least an absolute positive constant: \(\log(n/m')\ge s/n\) and \(s\ge cn/(2\log n)\). There are \(O((\log n)^2)\) steps, with bounded \(n\) handled by practicality. This proves the theorem.

## Finite checks

[verify_erdos18_branching_divisor_sums.js](verify_erdos18_branching_divisor_sums.js) checks the branching identity exhaustively on small binary families, then checks positive-height exact residue realizations for small explicit input banks and integer carrying identities. The asymptotic and prime-count estimates are proved above, not inferred from these checks.
