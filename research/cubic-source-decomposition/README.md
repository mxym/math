# A cubic-source decomposition by second-derivative entropy

This is a quantitative cubic instance of the first structural question in
Section 11 of Chandrasekaran–Goodman–Zuckerman, *Quadratic Extractors*
(arXiv:2611.07266v1). It is not a construction of a new cubic extractor.

Let f be a degree-at-most-three map over F_2 with arbitrarily many
uniform input bits. For every integer m >= 16 there is L_m = O(m^4 / log m)
such that:

- If f is injective and has at least L_m input bits, its distribution
  is exactly a mixture of injective m-bit affine restrictions, all of
  one of the two kinds below.
- Without injectivity, assume its output min-entropy is at least
  L_m + m + log2(1/epsilon), with 0 < epsilon < 1. Its distribution is
  within epsilon in total variation of such a mixture.

Either every retained restriction has degree at most two, or every
retained restriction has second-derivative min-entropy at least
floor(m/2) along **every linearly independent direction pair** on
its m-dimensional generating space. Over F_2, a dependent direction
pair always gives a zero second derivative, even for high-entropy
sources, so it is not included. In both branches each retained
restriction itself has output min-entropy exactly m.

The direction space is the same for every coset. For fixed error, or
more generally log2(1/epsilon) <= a fixed fraction of the entropy,
the resulting scale m is Omega((k log k)^(1/4)). The structural conclusion
does not imply a new disperser without more work.

See PROOF.md, SOURCES.md and RESULTS.txt. Replay the independent
standard-library checks:

    bash replay.sh
