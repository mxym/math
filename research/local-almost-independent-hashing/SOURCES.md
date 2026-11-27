# Sources and exact scope

Yevgeniy Dodis, Shachar Lovett, and Daniel Wichs, *Locally Computable
High Independence Hashing*, STOC 2026, [ePrint 2026/622](https://eprint.iacr.org/2026/622),
[ECCC TR26-059](https://eccc.weizmann.ac.il/report/2026/059/),
[March 30 author PDF](https://cs.nyu.edu/~dodis/ps/twise.pdf).
Printed pp. 7–8, Definitions 3.1–3.2 define the adaptive-query
statistical model and adaptive key probes. Definition 5.8 and Lemma 5.9
(pp. 16–18) organize the known word-local construction into word
chunks, independent selector descriptions and a sampler within
each selected word. Lemmas 5.5–5.6 (pp. 14–15) give the
rank-robust extraction and adaptive H-coefficient argument.
The present construction uses that overall template, not a new
rank-extraction or statistical-distance proof technique.

The source's §6 (printed pp. 18–19) asks to “close the logarithmic gaps
between the lower bounds and explicit constructions of almost-independent
hashing” for equal input/output size and error \(2^{-n}\).
It separately asks for one construction spanning all word sizes.
[AICR c/0066](https://aicr.info/c/0066/) makes the first goal precise for
“at least one such \(w\)” where the original construction is available,
by improving on \(n/\sqrt w\) or proving that scale necessary.
Its statement does not specify an optimal-key requirement; its lower
bound is in the polynomial-key setting. The [separate AICR proposal](https://aicr.info/projects/proposals/index.html)
is titled *Unifying bit-local and word-local hash constructions*.

| Claim | Word locality | Key length and scope |
| --- | --- | --- |
| DLW Theorem 5.1, pp. 10–11 | \(\Omega(\min\{m/\log\ell,\sqrt{m\log(1/\varepsilon)/(w\log\ell)}\})\) | Lower bound if \(k>(tw+\log(1/\varepsilon))/m\). At \(m=n,\varepsilon=2^{-n},w=n\) with polynomial key, the exact formula gives \(\Omega(\sqrt{n/\log n})\). The weaker specialized expression printed after the theorem is not used for matching. |
| DLW Theorem 5.7, p. 15 | \(O(n)\) bits | \(O(kn)\) bits for \(w=1\) and error \(2^{-n}\). |
| DLW Theorem 5.10, p. 18 | \(O(\lceil n/\sqrt w\rceil)\) | \(O(\lceil kn/w\rceil)\) words for \(w\ge\Omega(\log^2 k+\log^2 n)\), \(k=\operatorname{poly}(n)\); theorem states \(2^{-\Omega(n)}\) error, abstract presents the \(2^{-n}\) instantiation. |
| Present main result, \(w=n\) | \(O(\sqrt{n/\log n})\) | \(O(nk)\) words and error at most \(2^{-n}\); \(n\le k\le\operatorname{poly}(n)\). It matches the polynomial-key lower bound and is not a linear-size-key improvement. |
| Present supplementary template, \(u=1\) | \(O(\lceil n/\sqrt w\rceil)\) | \(O(\lceil kn/w\rceil)\) words and error at most \(2^{-n}\), including intermediate \(w\). |

The distinct ingredient here is using an outer expander walk on the
entire selector space instead of independently storing one selector
description per chunk. The first uniform selector can be long; the
short edge labels generate all remaining states. An inner walk with
one position from each disjoint stripe gives an exact-width sampler
with no duplicate positions and a useful per-state error bound.
This permits both a linear-size key at intermediate word lengths and
a selectable memory versus locality tradeoff. The analysis counts
distinct previous digests, which may coincide among themselves, and
does not require them to be independent at repeated field arguments.

Background primitives and adjacent work:

- Ofer Gabber and Zvi Galil, *Explicit Constructions of Linear-Sized
  Superconcentrators*, JCSS 22 (1981), 407–420,
  [DOI](https://doi.org/10.1016/0022-0000(81)90040-4). We use their
  standard eight-move graph; [Wigderson's text](https://www.math.ias.edu/~avi/BOOKS/expanderbookr1.pdf)
  Construction 8.1 reproduces that exact multigraph.
- David Gillman, *A Chernoff Bound for Random Walks on Expander Graphs*,
  SIAM J. Comput. 27 (1998), 1203–1220,
  [DOI](https://doi.org/10.1137/S0097539794268765). Expander walk
  concentration is classical; §2 proves directly the particular
  fixed-sets, nonconsecutive-times estimate needed here.
- Salil P. Vadhan, *On Constructing Locally Computable Extractors and
  Cryptosystems in the Bounded Storage Model*,
  [author manuscript](https://people.seas.harvard.edu/~salil/research/localext.pdf),
  §8 and especially Lemmas 8.3–8.4, gives earlier distinct-sample and
  matrix-domain ideas in a different extractor model. We instead
  choose one entry per stripe via a walk and exploit small marked
  sets within each stripe. That work does not provide the present
  adaptive almost-independent hashing locality/memory result.
- Amnon Ta-Shma, *Explicit, Almost Optimal, Epsilon-Balanced Codes*,
  STOC 2017, [author PDF](https://www.cs.tau.ac.il/~amnon/Papers/T.STOC17.pdf),
  Theorem 1.1 at fixed bias \(1/8\) supplies the public binary matrix
  columns of linear count. This is the same general rank-robust
  route used by DLW. Victor Shoup, *New Algorithms for Finding
  Irreducible Polynomials over Finite Fields*,
  [author PDF](https://www.shoup.net/papers/detirred.pdf), supplies
  deterministic polynomial-time binary field construction.
- Larsen et al., *Optimal Non-Adaptive Cell Probe Dictionaries and
  Hashing*, [ICALP 2024](https://doi.org/10.4230/LIPIcs.ICALP.2024.104),
  concerns perfect rather than statistical almost-independence.
  *Fast Bounded-Independence Functions and Their Duals*,
  [ITC 2026](https://doi.org/10.4230/LIPIcs.ITC.2026.8) /
  [arXiv:2606.07009](https://arxiv.org/abs/2606.07009), treats
  circuit size, degree, and related fast codes at bounded
  independence, not this word-probe tradeoff.

Bounded search, 2026-11-27: read the author's manuscript and public
ECCC metadata and checked exact title/author follow-ups, “word-based
overlap avoiding” with “expander walk,” “intermediate word sizes,” and
“almost k-wise” with “unified” or “word locality.” No matching
word-local all-range construction or standard-word improvement with
polynomial keys was located. This does not establish priority over
all unpublished or unindexed work. Only the positive abstract family
and its parameters are asserted; no claims about a concrete protocol
or implementation follow.
