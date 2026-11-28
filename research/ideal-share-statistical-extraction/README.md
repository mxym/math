# A sharp statistical extraction converse for ideal-size shares

In ordinary threshold secret sharing with exact reconstruction, suppose each unauthorized coalition's entire view changes by at most \(\varepsilon\) in total variation between any two secrets. If one share has an alphabet of the same size \(q\) as the secret, then computing that share at **one fixed secret** is a deterministic \(q\)-symbol extractor from the dealer input, with worst-case error at most
\[
 2(1-1/q)\varepsilon.
\]
The guarantee holds for the same extractor on every source of the permitted class. For \(q=2^b\), the extractor outputs \(b\) bits.

For \(0\le\varepsilon\le1/[8(q-1)]\), this constant is exact over all deterministic \(q\)-output extractors: a two-out-of-two finite example forces the displayed error even if an extractor can inspect the whole dealer input and is computationally unbounded. The proof does not just find a bad fixed share. It classifies all output maps that are too accurate to detect a four-corner coupling change, then proves the lower bound for each remaining coordinate permutation.

This is a restricted statistical strengthening of the known perfect-privacy, equal-alphabet case. It neither asserts extraction for larger share alphabets nor contradicts the existing \(b+1\)-bit-share separations. Sharpness is for \(q\)-symbol output and arbitrary finite key length, not for one-bit extraction at every \(q\), short keys, flat-source-only classes, or faulty reconstruction. See [PROOF.md](PROOF.md) and [SOURCES.md](SOURCES.md). Run `sh replay.sh` for the exact finite checks.
