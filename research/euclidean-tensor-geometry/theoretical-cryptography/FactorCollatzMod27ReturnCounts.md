# Quantitative returns to 20 modulo 27 in Collatz trajectories

**Scope.** This is a quantitative refinement of a sufficient-residue theorem, not a proof of the Collatz conjecture. We count shortcut steps for
\[
T(x)=
\begin{cases}
(3x+1)/2 & x\text{ odd},\\
x/2 & x\text{ even}.
\end{cases}
\]
An occurrence is counted at a departure, not at the terminal endpoint. The principal input is an exact branch budget on the 18 units modulo 27, coupled to an integer valuation bound on its exceptional self-loop.

**Relation to prior work.** [Monks, Monks, Monks and Monks, Theorem 6.4](https://arxiv.org/abs/1204.3904) shows that a divergent positive orbit or a nontrivial positive cycle visits 20 modulo 27 at least once; its proof uses the odd-step density on a smaller graph after the target is deleted. An independent [September 2026 rank reconstruction](https://github.com/Sodelin/Collatz-Conjecture-Work/blob/main/proof-search/sources/Sufficiency_Rank_Audit_2026-09-05.md) bounds the exceptional stay at residue 26 via the valuation of \(x+1\), but stops at its first target. The result here assigns a budget to **every** target-to-target segment, establishes a logarithmic return-count bound, and constructs explicit positive rational witnesses showing why integrality matters. For a different marked-orbit inequality that uses a ternary potential, see the [November 2026 preprint on 7 modulo 8 and the \(-5\) cycle](https://rstation.ai/problems/collatz/papers/188/v1); it counts different residues and does not give the present return bound.

## 1. Finite-interval bound

Let \(x_0,x_1,\ldots,x_N\) be a positive integer shortcut orbit segment with \(N\ge1\), all states at least 3, \(3\nmid x_0\), and \(x_N\ge x_0\). Put
\[
J=\#\{0\le i<N:x_i\equiv20\pmod {27}\},\quad
\alpha=\log_2 3.
\]
Then
\[
\boxed{\quad N<7\alpha^J\left(25+3\log_2(x_0+1)\right).\quad} \tag{1}
\]
In particular, avoiding the target altogether can support a nondecreasing-endpoint interval of length at most logarithmic in its starting value. The order of this dependence at \(J=0\) cannot be removed: \(x_0=27\cdot2^k-1\) takes \(k\) consecutive odd steps at residue 26, until it first becomes even, and those \(k\) departures form a nondecreasing-endpoint interval with \(J=0\).

### A certificate on units modulo 27

If \(p\in\{0,1\}\) is the departure parity, write the projected edge as \(r\to s\); its two possible successors are \(14r\) and \(14(3r+1)\) modulo 27, respectively. Both stay in the units. Let \(e=1\) for the odd edge \(26\to26\), and \(e=0\) otherwise. The following function \(h\) satisfies a branch budget:
\[
2p-1\le h(r)-h(s)+2\,{\bf1}_{r=20}+e. \tag{2}
\]

| \(r\) | 1 | 2 | 4 | 5 | 7 | 8 | 10 | 11 | 13 | 14 | 16 | 17 | 19 | 20 | 22 | 23 | 25 | 26 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| \(h(r)\) | 3 | 2 | 1 | 2 | 3 | 1 | 3 | 2 | 1 | 2 | 3 | 1 | 3 | 0 | 1 | 2 | 3 | 0 |

This verifies by substitution on 36 edges. The coefficients 2 and 1 cannot be individually lowered in an inequality of the form (2) with any telescoping potential on this graph: sum around \(2\to17\to26\to13\to20\to10\to2\) with parities \(1,1,0,1,0,1\), and around the odd self-loop \(26\to26\), respectively. These are modular walks, not necessarily integer cycles.

Let \(q\) be the total odd departures and \(\ell\) the total number of the exceptional self-loop steps in the actual segment. By summing (2) and bounding the endpoint difference by 3,
\[
2q-N\le 2J+\ell+3. \tag{3}
\]

### Control of repeated loops between visits

On writing \(u=x+1\), odd steps multiply \(u\) by \(A=3/2\), and even steps give \(u'=(u+1)/2\le (5/8)u\) since \(u\ge4\). Put \(B_0=5/8\), \(K=\sqrt{A/B_0}=\sqrt{12/5}\), \(c=2\log_2 K\), and
\[
W(x)=(x+1)K^{h(x\bmod27)}.
\]
For a non-loop edge, (2) and \(AB_0=15/16<1\) imply
\[
\frac{W(T(x))}{W(x)}
 \le \sqrt{AB_0}\,K^{2p-1+h(s)-h(r)}
 \le K^{2{\bf1}_{r=20}}. \tag{4}
\]
Thus outside the exceptional loop, \(W\) can increase only on departure from the target and then by at most a factor \(12/5\).

Cut the interval immediately before every marked departure. There are at most \(J+1\) blocks, each contains at most one marked departure, and each has at most one maximal consecutive run of \(26\to26\) edges. In fact, leaving residue 26 by any other edge takes the even step to 13, and then either branch reaches 20. A second run cannot begin without a new cut.

If a block begins with \(z=\log_2 W\), the weight at the start of its loop run is at most \(2^{z+c}\). At residue 26, \(W=u\). A run of \(k\) consecutive odd steps requires \(2^k\mid u\): after it, the integer value of \(x+1\) is \(3^k u/2^k\). Therefore \(k\le z+c\). The run increases \(\log_2 W\) by \((\alpha-1)k\), so the next block starts with logarithm at most \(\alpha(z+c)\), whether or not there was a run.

Let \(z_0=\log_2 W(x_0)\) and \(B=z_0+\alpha c/(\alpha-1)\). Induction on the start of block \(i\), with \(i=0\) for the first block, gives \(z_i+c\le\alpha^i B\). Summing the geometric series shows
\[
\ell\le B\,\frac{\alpha^{J+1}-1}{\alpha-1}.
\]
Using \(J(\alpha-1)\le\alpha^J-1\) in (3), we obtain the useful intermediate form
\[
2q-N\le\alpha^J\left(3+\frac2{\alpha-1}
                              +\frac{\alpha B}{\alpha-1}\right). \tag{5}
\]

All odd inputs have \(3+1/x_i\le10/3\). Multiplying the true step ratios and using \(x_N/x_0\ge1\) gives \(q/N\ge\log 2/\log(10/3)\), so \(2q-N>N/7\), because \((10/3)^4<2^7\). Here \(3/2<\alpha\), \(c<4/3\), and \(0\le h\le3\), hence \(B<\log_2(x_0+1)+6\). Substitute these inequalities into (5) to get (1).

## 2. Consequences for genuine integer orbits

* **Divergent orbits.** Such an orbit tends to infinity: infinitely many returns to any fixed finite set would repeat a state and force periodicity. A positive orbit enters the units modulo 3 no later than its first odd step, and cannot subsequently leave them. Start the count on this tail. For all sufficiently long prefixes, the endpoint is at least the initial tail value and every state is at least 3. Equation (1) shows that the first \(N\) shortcut departures of the original divergent orbit would contain at least
  \[
  \frac{\log N}{\log\alpha}-O_{x_0}(1)
  \]
  visits to 20 modulo 27.

* **Nontrivial positive cycles.** For the least shortcut period \(N\), start at the minimum \(m\). It is at least 3, and all states in the cycle are units modulo 3. The cycle product and Rhin's estimate in [Simons–de Weger, Lemma 12](https://www.impan.pl/shop/en/publication/transaction/download/product/82263) give
  \[
  e^{-13.3(0.46057+\log q)}
   < N\log2-q\log3
   =\sum_{i\ {\rm odd\ input}}\log(1+1/(3x_i))
   < q/(3m).
  \]
  In particular \(m+1<256N^{15}\). For example, \(\log 2>56/81\) by the first two terms of the \(\operatorname{arctanh}(1/3)\) expansion, so \(e^{13.3(0.46057)}<2^9\), giving the stated loose constant. Equation (1) now yields at least
  \[
  \frac{\log N-\log\log N}{\log\alpha}-O(1)
  \]
  distinct visits to 20 modulo 27 in one least lap. The asymptotic statement does not use any computational convergence range.

* **Concrete bound using the published range.** [Bařina (2025), §6](https://doi.org/10.1007/s11227-025-07337-0) reports verification below \(2^{71}\) and ordinary period lower bound \(355{,}504{,}839{,}929\). Thus \(m\ge32\) (much weaker than that verification gives) and \(N\ge N_0=177{,}752{,}419{,}965\), using ordinary period \(N+q\le2N\). The inequality \((97/32)^5<2^8\) gives \(2q-N>N/4\) at \(m\ge32\). Use \(\alpha>11/7\) and \(B<14+15\log_2 N\) in (5) to obtain
  \[
  N<\alpha^J(180+165\log_2N).
  \]
  The function \(N/(180+165\log_2 N)\) increases for \(N\ge2\). At \(N_0<2^{38}\) its value exceeds \(N_0/6450\), and
  \[
  N_0\,29^{37} > 6450\,46^{37},\qquad 3^{29}<2^{46}.
  \]
  So \(J\le37\) is impossible. With these published inputs, any nontrivial positive integer cycle must contain **at least 38 distinct values** equal to 20 modulo 27. This does not improve the quoted lower bound on its total length.

## 3. One-visit rational cycles despite arbitrary fixed modular precision

The cutoff \(2^k\mid x+1\) and real size imply \(k\le\log_2(x+1)\) for positive **integers**. This last implication fails for positive rationals with odd denominator. In fact, for every fixed positive integer \(M\) there are positive rational shortcut cycles with denominator coprime to \(54M\), least periods \(N\to\infty\), \(q/N\to\log_3 2\), and minima \(m\to\infty\) satisfying \(m=O(N^2)\), but with **exactly one** departure from residue 20 modulo 27.

For the construction, use the closed modular walk based at 2 from §1. Insert \(k\) odd self-loop steps at 26; after completing the marked walk, append \(l\) copies of \(2\to1\to2\) (parities \(0,1\)). It has exactly one marked departure and \((N,q)=(6+k+2l,4+k+l)\). Conversely, \(k=2q-N-2\) and \(l=N-q-2\) are nonnegative whenever \(N,q\) are large and \(N/q\) is close to \(\alpha\).

Write \(Q\) for the factor of \(54M\) left after deleting all factors of 2 and 3. Choose \(L\) divisible by the orders of both 2 and 3 modulo \(Q\), with \(L=1\) permitted if \(Q=1\). Restrict \(N,q\) to \(1\bmod L\). The irrationality of \(\alpha\) makes \(\{\alpha v\}\) dense as \(v\) runs through the positive integers (fractional parts). Therefore, for each \(j\ge2\), there are arbitrarily large pairs in these progressions with
\[
1/(j+1)<\varepsilon=N-\alpha q<1/j .
\]
Indeed these pairs amount to \(N=1+Lu,\ q=1+Lv\) and \(\varepsilon=1-\alpha+L(u-\alpha v)\). Choose \(q\ge j\) and increasing. The denominator \(D=2^N-3^q>0\) is odd and not a multiple of 3; also \(D\equiv 2-3=-1\bmod Q\).

For a word of parities \(p_i\) (positions \(i=0,\ldots,N-1\)), let \(q_i\) count the odd letters **before** \(i\). Its unique periodic root under the indicated affine maps is
\[
x=\frac{\sum_{i:\ p_i=1} 2^i3^{q-1-q_i}}{D}. \tag{6}
\]
Every rotated root is positive. The numerator of that rotation has parity equal to its first letter because only a contribution at position zero can be odd; \(D\) is odd. Thus the indicated branches are the actual shortcut branches on rationals, interpreting parity by reduction modulo 2, and the affine maps take one rotated root to the next. Modulo 27 the same fixed equation has a unique root since \(D\) is invertible, so their residues are exactly the prescribed walk. Since precisely one position is marked, the rational period cannot be a repetition and is least.

In any rotation the first odd contribution in (6) is at least \(3^{q-1}\), which yields \(m\ge 1/[3(2^\varepsilon-1)]\) and \(m\to\infty\). On the other hand, cut at a maximum of the periodic centered prefix \(i-(N/q)q_i\). The restarted prefixes are all nonpositive, so \(2^i/3^{q_i}\le2^\varepsilon\) there. Summing (6) gives
\[
m\le \frac{q\,2^\varepsilon}{3(2^\varepsilon-1)}
 =O(qj)=O(N^2).
\]
Together these inequalities imply \(N/\log(m+1)\to\infty\). The one-visit cycles therefore violate (1) if rationals are allowed. For all large \(j\) they cannot have integral entries, by the proven integer bound.

For any fixed modulus \(M\), reduction of the entire rational lap is valid. More explicitly, a positive integer chosen to agree with its starting rational modulo \(2^{t}54M\) shadows the first \(t\) steps modulo \(54M\), for any finite \(t\), by induction: each step divides the difference by at most 2, and agreeing modulo 2 gives the same branch. This does not close the integer orbit, even when the rational word repeats. The examples exclude a multiple-visit theorem based merely on arbitrary fixed modular walks together with positivity and near-critical parity ratios. They do not exclude arguments using archimedean size together with integrality, or modulo conditions with genuinely increasing precision enforcing equality over the integers.

## Reproduction

Run the companion file with Node.js (BigInt, no dependencies). It verifies all 36 branch inequalities, fixed-integer comparisons for the constants and the 38-visit cutoff, and examples of integer loop bursts. It checks marked counts on integer segments and verifies four exact rational witnesses with different prescribed moduli, including a full positive-integer modular shadow of each lap. These are exact arithmetic checks for the finite certificate and illustrative witnesses, not a search for integer cycles or a formalization of the analytic proof.
