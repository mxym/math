# Local almost-independent hashing at all word sizes

**Main result (word size \(w=n\)).** For \(n\)-bit inputs and outputs,
\(n\le k\le\operatorname{poly}(n)\), there is an explicit
\(2^{-n}\)-almost \(k\)-wise independent family with \(O(nk)\) seed words
and \(O(\sqrt{n/\log_2 n})\) word probes per evaluation (\(n\ge2\)).
This holds for adaptive oracle queries. With arbitrary polynomial key
length this locality has the same order as the lower bound of
Dodis–Lovett–Wichs, and is \(o(\sqrt n)\), positively answering the
one-word-size question of AICR c/0066 in its polynomial-key setting.
It does **not** resolve the log gap at linear-size key length.

**Supplementary generality.** The same proof gives a tradeoff over
\(1\le w\le n^2\), \(1\le k\le2^n\), and integers
\(1\le u\le\lceil\log_2(2n)\rceil\): key
\(O(2^u\lceil kn/w\rceil)\) words and locality
\(O(\max\{1,n/w,n/\sqrt{wu}\})\). Taking \(u=1\) gives
the linear-size key and the source's large-word locality bound
throughout the intermediate range as well. With \(u\) near
\(\log n\), the proof also gives the corresponding matching
polynomial-key order over the full range.

The construction uses one stationary expander walk to generate sequential
chunk selector states and another, within each selected word, to choose
one distinct position per stripe. Only the initial outer state and edge
labels are stored. See [PROOF.md](PROOF.md) for explicit finite parameters,
the adaptive transcript proof and word accounting, and [SOURCES.md](SOURCES.md)
for the exact scope relative to the two questions of
[Dodis–Lovett–Wichs](https://cs.nyu.edu/~dodis/ps/twise.pdf) and
[AICR c/0066](https://aicr.info/c/0066/).

Run `sh replay.sh | diff -u RESULTS.txt -` with Python 3. The finite
checkers test the algebra and accounting, not the asymptotic conclusions
by extrapolation. This is a positive theorem for the abstract hashing
model, not an evaluation of an implementation or a deployed system.
