# A uniform visibility gap for the pooled qutrit Werner-state steering witness

**Yongxian Zhang.** AI-assisted research draft; internal independent AI review only, not external peer review.

Yang and Qiao asked whether their direct-sum majorization steering test for qutrit Werner states can attain the critical visibility \(2/3\) as the number of settings grows. For **every** list of complex qutrit projective bases, the visibility required by their pooled witness is at least \(1486/2223=2/3+4/2223\). No sequence of settings can close this gap. The proof keeps track of the fact that the witness selects outcomes globally, not one from each basis. It applies to arbitrary weighted settings with fractional ties.

This is not an optimality claim for the numerical lower bound, does not alter the known physical projective-steering threshold, and does not address the companion isotropic prediction. It concerns the specified aggregation and measurement alignment, not every steering test. See [the proof](PROOF.md), [sources and overlap checks](SOURCES.md), and [the independent internal review](REVIEW.md). No claim of worldwide priority is made.

Both checks use standard-library Python with exact rational arithmetic. From this directory:

~~~sh
sha256sum -c SHA256SUMS
python3 -O -B verify.py
python3 -O -B rational_check.py
~~~
