# Near-Singleton conflict-checkable codes at length four

For each real \(\varepsilon>0\), there are arbitrarily large alphabet
sizes \(q\) and length-four codes of minimum distance exactly two
with dimension \(k=\log_q|C|\ge3-\varepsilon\). The codes are both
conflict-checkable and local-to-global consistent in the sense of
Applebaum–Kachlon (SODA 2024, ePrint 2023/627). In particular, they
meet \(k>2\), exceeding the comparison-based bound in their
non-endpoint range and answering the existence conjecture recorded
as [AICR c/0096](https://aicr.info/c/0096/).

Each symbol is a vector over a prime field. A word evaluates an
integer vector quadratic whose two nonconstant coefficient vectors
lie on one fixed Euclidean Gram level, plus an arbitrary field
offset. Pair projections reveal short secants. Three compatible
pairs determine the Gram data of a common interpolant, and a
primitive-spacing identity gives it integral coefficients. For
all four observations, Gram positivity forces the fourth to fit
that same interpolant.

This note treats only \((n,d)=(4,2)\); it does not assert a property
of the authors' original construction, a general \((n,d)\) theorem,
or an efficient high-rate decoder. See [PROOF.md](PROOF.md) and
[SOURCES.md](SOURCES.md). Run `sh replay.sh` using Python 3 for the
exact finite corroborations. No external inputs are used.
