# Exact low-rate trace-distance decay for random affine hashing

For an i.i.d. source with classical symbols and arbitrary finite quantum
side information, we determine the low-rate mean trace-distance error of
a random binary affine hash. The answer comes from the norms of the
one-symbol operator-valued Fourier coefficients. In the strict low-rate
regime the error is asymptotic to an explicit finite expression, with
exponentially small relative error, not just the same logarithmic rate.

For a binary source the decay exponent in that regime is
\(H_{\min}(X|E)-R\), with an explicit rate threshold in terms of the
optimal binary guessing bias. A two-dimensional noncommuting example
at positive rate has a larger exponent than that of every
four-wise-exact collision ensemble. For uniformly distributed binary
symbols encoded into a pair of pure states, this also realizes the
sandwiched conditional Rényi counterpart of Regula–Cheng's
[Equation (144)](https://arxiv.org/html/2611.33270v1) in the stated
low-rate interval. It answers a structured case of their side-information
question, not the unrestricted problem.

For a uniform binary full-rank quotient, we also give matching
low-rate decay. A finite bound in the pure-state example
\(P_X=(9/10,1/10)\), \(R=1/100\) contradicts Lemma 39 in
[Hayashi's public v6 preprint](https://arxiv.org/html/1202.0322v6)
(HTML Eq. (151), v6 PDF Eq. (150)). This finding concerns the
stated ensemble exponent, not a device or the final IEEE typeset text.

The hash seed is independent of the source and public, the metric is
trace distance to a uniform output with the real side marginal, and
the ensemble includes every binary matrix (including rank-deficient
ones). Theorems are not claimed at rates above the explicit threshold,
or for a hash law chosen adaptively from the input.

See [PROOF.md](PROOF.md) for the theorem and [SOURCES.md](SOURCES.md)
for how it differs from prior bounds. The small finite verification
examples do not replace the proof.

~~~sh
sh replay.sh | diff -u RESULTS.txt -
~~~
