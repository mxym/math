# Fixed-rate guessing for rank-one measurements

We extend the domain of Curran's fixed-rate-of-inconclusive (FRIO) theorem from full-rank states and projective measurements to arbitrary finite-dimensional states and a prescribed number of rank-one POVM outcomes. The clipping formula and weighted-diagonal equality criterion in the full-rank projective case are Curran's; the symmetric discrimination construction has earlier precedents. The direct proof below handles the singular Naimark dilation, repeated eigenvalues, and both endpoint rates.

For an informationally complete measurement, a separate distinction appears. A rank-one minimal informationally complete POVM (MIC) can attain the optimal guessing probability at each fixed rate. Unless the state is proportional to its support projector, no single such MIC attains it at all rates. The worst relative loss over rates can nevertheless be made arbitrarily small. A positive lower tomography frame bound forces a quantitative loss at two rates.

- [Proof and exact scope](PROOF.md)
- [Primary sources and overlap](SOURCES.md)
- [Reproduced checks](RESULTS.txt)

Run `bash replay.sh` with Python 3, NumPy and SciPy. The scripts are independent checks of the algebra and examples, not substitutes for the proof.

This is an unconditional correct-guessing objective with a prescribed reject probability and side information purifying the state. It is not a statement about a protocol's security, a device known to Eve beyond the stated model, or the optimization over effects of unrestricted rank.
