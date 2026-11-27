# Private randomness from mixed probes and an untrusted detector

A dimension-independent one-round certificate for the mixed-probe direction
in §V of [Ishihara et al., PRA 114, 052413](https://doi.org/10.1103/d7pg-hjgs),
using the text of [arXiv:2210.13608v3](https://arxiv.org/html/2210.13608v3).
It treats an independent trusted source: on each input label the signal and
detector memory have product marginal with common memory state. Eve may hold
a purification of both and measure her systems jointly.

- For a finite-dimensional input and binary effective effect \(M\), the
  guessing probability in generation on \(\rho\) is bounded by
  \((1+\sqrt{1-\|[\rho,M]\|_1^2})/2\), uniformly in detector and Eve
  dimension. With arbitrary partial-probe data, minimizing the commutator
  over consistent effects is an SDP and gives an exact test for *whether*
  positive randomness is certifiable, not generally its exact amount.
- For \(\rho=(I+rZ)/2\) on a qubit, two probes in the \(X\) basis suffice.
  With contrast \(t=p(+|X+)-p(+|X-)\), the sharp worst-case guessing
  probability from the contrast alone is \((1+\sqrt{1-r^2t^2})/2\).
  Equality holds also when both calibration probabilities sum to one and the
  generation probability is given, and for each fixed unbiased effective
  qubit effect with the complete transverse Bloch vector in place of \(t\).
- Approximate source/device product marginals with declared trace-distance
  bounds have an explicit robust certificate. A coarse-graining corollary
  gives an exact positivity test also for finite-output detectors when the
  generation density matrix has simple spectrum.

This is a single-round conditional min-entropy result. It does not assert
a finite-size protocol, security without a bound on signal/device correlations,
or a conclusion about the original coherent-state homodyne experiment.
See [PROOF.md](PROOF.md) for assumptions and [SOURCES.md](SOURCES.md)
for distinctions from earlier models.

Replay with Python 3 and NumPy: `bash replay.sh`. One checker uses only exact
rational arithmetic and the standard library; the other uses direct
complex matrices, Schmidt purifications, and the anticommuting observables. They are checks, not proofs.
