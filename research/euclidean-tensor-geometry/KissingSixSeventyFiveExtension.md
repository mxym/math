# The 75-point strict-pair obstruction extends to 76 points

Call a pair of distinct unit vectors **strict** if their inner product is below $-1/2$. A kissing code has all distinct inner products at most $1/2$.

**Theorem.** A 75-point kissing code in $\mathbb R^6$ has 36 disjoint strict pairs, or else **all** of the following hold:

* Its strict-pair graph has exactly five connected components: one isolated vertex $x$ and four nontrivial odd factor-critical components. It has no antipodal pair. There are just ten candidate multisets of component sizes (below).
* The code extends to a 76-point code by adjoining $-x$. No other antipode of an existing vertex can be adjoined. The enlarged code has exactly one antipodal pair, exactly 36 disjoint strict pairs in a largest matching, and hence needs exactly 40 singleton-or-strict-pair parts.

The alternatives are disjoint if “has 36 disjoint strict pairs” means **at least** 36, as here. In particular, every 75-point code that is maximal by inclusion, or already has an antipodal pair, has 36 disjoint strict pairs. If any six-dimensional code needs 40 parts, there is a **76-point** code needing 40. In particular if the six-dimensional kissing number is at most 75, every code has a 39-part cover. These are conditional structure statements: neither 75 nor 76 is excluded or constructed.

## Why the isolated vertex is forced

Use the [six-dimensional strict-pair cover and its component charge bounds](https://github.com/mxym/math/blob/70aeadbd0f6859eda06452177fb39cebd763eec1/research/euclidean-tensor-geometry/KissingSixStrictPairCover.md). With $G$ the strict-pair graph, choose a Tutte–Berge barrier $T$ of maximum cardinality among the maximizers of $o(G-T)-|T|$. Its components are odd and factor-critical, of orders $1$ or odd $k\ge5$. Write $t=|T|$, $n=75-t$, $o$ for their number and $s$ for the singleton count. Adding the antipodes of the singletons *after removing* $T$ gives $n+s\le76$ by [Tomar's cardinality bound](https://www.mefyi.com/papers/kissing-numbers-five-seven/). The number of parts needed by $G$ is $(n+o)/2$; if a 36-matching is absent then $n+o\ge80$.

The preceding paper also gives charges $w_k$ with $\sum w_k\le48{,}000{,}000$. We change just the order-27 charge. The [new rational source row](kissing-six-seventy-five-extension-chart.json) proves the following bound for the uniform measure on *any* 27-point code, not just the factor-critical case:
\[
 27\,\mathbb E[(X\cdot Y)^4-(X\cdot Y)^2/4]\ \le\ 
 \frac{652948043974739}{400000000000000}.
\]
Here $X,Y$ are independent with replacement. The row gives explicit positive factors for the dimension-six three-point kernel, uses slack $1/130000$, and is certified on the entire sorted Gram domain by 977 tensor-Bernstein boxes. As in the preceding proof the charge is rounded **down**, $w_{27}=\lfloor 27\cdot10^6/U_{27}\rfloor$.

Enumerate nondecreasing lists of allowed orders, tracking $(n,o,s)$ and charge. Each ordering is visited once: start empty and append any allowed order at least as large as the previous order. Reject $n>75$, $n+s>76$ and charge above 50 million (all charges are positive, and an exhibited minimum below 50 million is unaffected). Among lists satisfying $n+o\ge80$ and $n+s\le75$, the smallest charge is **48,006,104**, at $(7,7,7,27,27)$. Of the remaining lists, precisely the following ten stay within the 48-million budget. We omit the leading 1 in each:
```
7,7,27,33   7,7,29,31   7,9,27,31   7,9,29,29   7,11,25,31
7,11,27,29  7,13,25,29  7,13,27,27  9,9,27,29   9,11,27,27
```
All ten have $n=75$, $o=5$, $s=1$. In particular $T$ is empty; a singleton after deletion is genuinely isolated in the original graph. We do not claim that the ten numerical templates are realizable.

The matching number is $(75-5)/2=35$. Since $x$ is isolated, $|x\cdot y|\le1/2$ for every other $y$. Adding $-x$ replaces an isolated vertex by an isolated edge and changes neither the other components nor the number of parts. Conversely, any antipodal pair in a kissing code is an isolated two-vertex strict component: the two upper bounds against a third vertex force absolute product at most $1/2$. Hence the original graph had none and the larger graph has exactly one. The other corollaries use the previously proved 39-part bound for size at most 74 and the unconditional 40-part bound through size 76.

**Replay.** Run `node verify-kissing-six-seventy-five-extension.js` in this directory (standard Node). It checks the new source, pins both inherited input files by SHA-256, enumerates the full budget, and prints all ten lists. Earlier source charts can be replayed independently by the verifier linked in the preceding paper.
