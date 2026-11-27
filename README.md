# Ordinary strong seeded extractors give multi-instance extraction

Guan–Wichs–Zhandry ask in ePrint 2023/409 §1.3 whether ordinary strong seeded extractors suffice for their multi-instance definition. There is a general affirmative result with explicit single-instance entropy and error parameters. No list-local decoding, hinting, linearity, universality or seed-length increase is needed.

Let Ext take n input bits, output m bits, and be an ordinary strong (k,η) seeded extractor. Let X have t arbitrarily correlated n-bit blocks and H∞(X)≥αtn. Take independent fresh public seeds, independent of X. For target 0<ε≤1, assume

    η ≤ ε² / (4 t 2^m),
    r = k + m + log₂(4t/ε²) < n.

A deterministic set I(X), chosen before the seeds, then has size at least

    max{0, t − floor(((1−α)tn + log₂(2/ε))/(n−r))}.

Replacing the extracted outputs on I(X) by independent uniform m-bit strings, while retaining every other output and every seed, changes the complete joint distribution by at most ε in total variation. The guarantee remains true if I(X) and the raw input values outside I(X) are included in both compared distributions. The set selection is existential and need not be efficient. [PROOF.md](PROOF.md) proves a more general finite-alphabet, nonidentical-extractor theorem and quantifies the parameter restrictions. No guarantee for shared seeds, quantum side information, or a concrete encryption implementation is claimed.

The new step is using the ordinary extractor's known list-decodability consequence as a collision-neighborhood bound inside dense-source extraction. It extends the dense-source collision argument of Dinur–Stemmer–Woodruff–Zhou, who used universal hashing. Density restoration itself is established prior machinery. See [SOURCES.md](SOURCES.md) for both exact attributions and limits of the result.

Run `sh replay.sh` with Python 3 and a standard POSIX shell. The checkers are finite arithmetic validations, not a substitute for the analytic proof.
