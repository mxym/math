# The factor-t randomness penalty for minimal sources is not universal

For even n≥2t+2 and t≥3, let n parties each hold one bit and ask every party to learn the single bit

    F_n(x) = (x_1 AND x_2) XOR x_3 XOR ... XOR x_n.

This functionality requires an honest majority for perfect private computation, even though it has an explicit perfectly t-private protocol using exactly t fixed random sources and O(t² log n) fair bits. The protocol uses no trusted setup, additional parties, or computational assumptions. The same source set contains both inputs of the AND gate, and the protocol never opens the AND value separately.

Unrestricted t-private randomness complexity is at least (t−2)²/2 by reduction to the XOR lower bound of Goyal–Ishai–Song. Along, for example, n=2t², the ratio of t-source cost to t times unrestricted cost is O(log t/t), which tends to zero. Thus the uniform lower-bound half of Couteau–Rosén's Conjecture 13, under the standard minimum over protocols using at most t predetermined sources, is false. For any one prescribed source set D, relabel the two nonlinear owners into D to get a counterexample F_D. This is not one fixed labelled functionality proved cheap simultaneously for all placements. Nor does it settle an O(t)-overhead compiler or a worst-placement variant.

The proof uses an ordinary Shamir double sharing to open a masked product, and then combines its remaining additive shares with the XOR inputs rather than opening that product. It gives the exact joint view, including the case where every source is corrupt. [PROOF.md](PROOF.md) gives details and [SOURCES.md](SOURCES.md) separates prior building blocks from the counterexample.

Run sh replay.sh with Python 3 and a POSIX shell. The two checkers validate finite field fibers, full conditional transcript cases and the lower-bound restrictions; the counterexample is analytic.
