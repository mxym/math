# A regular polygon from a constant powered-distance sum

Let N distinct sites lie in the plane. If the sum of the (2N−2)-th powers of their distances from a moving point stays constant on a test circle, must the sites be the vertices of a concentric regular N-gon? This is Nikolov and Rafailov's single-power inverse question. The test circle is fixed, and the sites need not lie on it.

We prove the conclusion (i) for **every N≥2 if the sites are in the closed disk bounded by the test circle**, and (ii) for **every planar site configuration with 2≤N≤18**, with no constraint on radii or angles. The first proof is analytic: a nonnegative trigonometric polynomial with a peak of height N stays nonnegative when moved into the disk via the maximum principle. The second uses an exact integer certificate for positivity over a continuous three-parameter domain. The original authors had already announced the cases N=3 and N=4, and the antipodal-pair case is elementary. No new claim is made for these small cases.

For Bosuwan's shift h≥0 inside the squared distances, the analytic proof also gives the result for site radii at most √(1+h) when the test radius is 1. The finite certificate is **unshifted**. No result here establishes the original conjecture in general for N≥19.

* [Proof](PROOF.md) and [prior work](SOURCES.md).
* [Independent mathematical review](REVIEW.md). [Why the pointwise test fails for every N≥19](WITNESS-LIMIT.md): a limitation of this certificate, **not** a counterexample to the conjecture ([separate review](WITNESS-REVIEW.md)).
* With standard Python 3, run `python3 -B -O verify.py` and `python3 -B -O independent.py`; compare the two [author](CHECKS.txt) and [independent](INDEPENDENT-CHECKS.txt) transcripts. Each implementation proves strict positivity on the closed angular interval for all 65,399 coefficient polynomials. No floating-point or sampling inference is used.
* `sha256sum -c SHA256SUMS` checks the package integrity.

This is AI-assisted research with internal AI proof review, not external peer review, formal proof-assistant verification or a guarantee of priority.
