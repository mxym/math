# Two-bit shares for weakly private \((n-1)\)-out-of-\(n\) secret sharing

This gives an affirmative answer to the final question in the
“Open Problems” list of [Beimel–Ishai–Kushilevitz–Li,
ePrint 2025/1978, p. 7](https://opencryptology.org/2025/1978.pdf):
one bit can be shared among \(n\) parties, any \(n-1\) reconstruct
perfectly, and the max share size is \(o(\log n)\) under weak
privacy. In fact, for every \(n\ge4\) the shares are **two bits**
and the worst likelihood ratio between the two secrets is exactly
three: the scheme is \(1/3\)-weakly private. The construction uses
a fixed number of fair random bits, with no rejection. At \(n=2,3\)
the corresponding boundary is achievable with perfect privacy.

There is no such scheme with at most two symbols per party for
\(n\ge3\), even if the required weak-privacy parameter is arbitrarily
small and positive. Thus two is the optimal integer number of
bits needed for a share in the worst case. We do not rule out a
three-symbol alphabet, nor claim that \(1/3\) is optimal among
all two-bit-share schemes.

The key step is a coloring of the double-parity code: on every
four-element completion of an \(n-2\) view, the two colors have
multiplicities \(1\) and \(3\); globally they have equal
cardinality.

This is weak privacy in the paper's information-theoretic,
pointwise sense, not standard perfect privacy or an assertion
that an unauthorized set learns nothing. See [proof](PROOF.md),
[sources](SOURCES.md), and [independent replay results](RESULTS.txt).
