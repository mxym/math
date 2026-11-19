# Prescribing the total number of cycles in a simple planar cubic graph

Every integer **k ≥ 2679** occurs as the total number of simple cycles of a simple, planar, 2-connected cubic graph. The proof constructs a graph on O(√k) vertices. It does not rely on enumerating all graphs up to a given order.

The construction uses three small two-terminal graphs. Their terminal-path counts can be increased one at a time without changing a second quantity, the difference between the number of pairs of terminal paths and the number of internal cycles. Joining two pieces in parallel adds their differences. This lets us choose the difference first, then set the path count to hit the prescribed cycle count exactly.

McCulloch, McKay, Salahshoori and Zaslavsky report finite positive occurrences through 4000 for the simple planar subclass in §6(d). With those reported occurrences, the construction shows that every count outside the **(d) list** occurs in a simple 2-connected planar cubic graph, and hence also without requiring planarity. It does **not** verify the smaller printed (b) list for the general class: taken literally, (b) asserts an occurrence at 16, which the same paper’s Theorem 1 rules out. We do not use (b) as a complete finite positive list. The status of 17–21 in the general simple cubic class is not determined here. We do not prove all listed exclusions, claim optimal size or threshold, or address 3-connectivity.

* [Constructive proof and all 22 residue classes](PROOF.md)
* [Published formulation, earlier results and search scope](SOURCES.md)
* [Separate internal proof review](REVIEW.md)
* [Exact graph verifier](verify.py) and [expected output](CHECKS.txt)

Reproduce with standard Python 3:

    python3 verify.py
    sha256sum -c SHA256SUMS

The checker builds four literal graphs and counts cycles by enumerating paths without using the composition formulas. It also checks the arithmetic on 97,322 consecutive inputs. The universal conclusion comes from the proof, not these test cases.

AI-assisted research note, including proof development, source checking, code and a separate internal audit. That audit is not external peer review. No claim of certified priority. All third-party rights and attribution remain with their respective holders.
