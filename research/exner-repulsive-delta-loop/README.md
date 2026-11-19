# Equal repulsive barriers on a loop: Exner's spacing conjecture

Place a fixed number of identical repulsive delta barriers on a one-dimensional loop. Which placement gives the largest lowest energy? For every positive strength the barriers must be equally spaced, uniquely up to a rotation. This is the positional comparison asked in [Pavel Exner's 2019 Conjecture 5.1](https://arxiv.org/html/1906.01229v2#S5). It does not concern a particle moving in the plane or in space, or the related delta-prime problem.

[PROOF.md](PROOF.md) gives the short variational argument. On the unequal gaps, use cosine trial functions taking the same value at every barrier. Their endpoint contributions are tangents of the half-gap angles, so strict convexity favors equal spacing. A gap too long for that construction provides a Dirichlet trial function instead. The result also follows readily from an earlier fixed-edge comparison with a flower graph plus Jensen's inequality; see [SOURCES.md](SOURCES.md). No new spectral machinery is needed.

The analytic proof stands independently of computation. For an arithmetic check of the cases, run `python3 -B -O check.py`; [CHECKS.txt](CHECKS.txt) records the output. [REVIEW.md](REVIEW.md) identifies the scope of the internal check. AI-assisted research note, not externally peer reviewed; no claim of priority.
