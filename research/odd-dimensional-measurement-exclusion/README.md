# Entanglement-assisted exclusion of three measurements in odd dimension

For every prescribed pure entangled state on $\mathbb C^d\otimes\mathbb C^d$, including odd $d\ge3$, the proof constructs three ordered rank-one projective measurements with the following properties. A device applies one unknown measurement **once** and returns its classical outcome label, not the measured quantum system. Using the prescribed input and the retained reference, the observer can always name a measurement the device did **not** apply. No product input can do this with certainty. And no input whatsoever, even a mixed one with an arbitrary reference, can always name the measurement it **did** apply.

These are different statements. The three measurements may depend on the prescribed pure state. All outcome labels have positive probability under each measurement; conditional on any label, even a pair of the three prescribed-probe reference states is never orthogonal. The impossibility for *arbitrary* probes concerns identifying the triple, not identifying a chosen pair. The result does not extend the positive assertion to every entangled mixed input or address repeated uses.

[Manna](https://arxiv.org/abs/2510.26255v2) gave the even-dimensional construction and asked about odd dimensions in §V. The [proof](PROOF.md) builds the missing three-dimensional block using a rational path of real rotations. Distinct points on the path certify independent conditions for ruling out product exclusion and assisted identification. A block construction then deals with all Schmidt ranks, including ranks smaller than the input dimension. The two-dimensional block and the conditional three-state exclusion threshold are prior results; see [sources and scope](SOURCES.md).

### Reproducing finite checks

From this directory, with Python 3 and SymPy (tested at 1.14.0):

~~~sh
sha256sum -c SHA256SUMS
python3 -B verify.py
python3 -B -O independent.py
~~~

The first checker needs only the standard library. The second is an independent exact implementation checking three spectra, a rank-three input in dimension five, and the marginal-conjugation identity. [Expected output](CHECKS.txt) · [Independent mathematical review](REVIEW.md). The theorem for arbitrary dimension and Schmidt coefficients rests on the proof, not extrapolation from these checks.

**Status:** AI-assisted research with independent internal AI review, not external peer review or formal verification. No claim of worldwide priority.
