We prove the sharp prescribed-mass Gaussian centroid ellipsoid inequality

`tr(B^T H_p^+ B) <= I(p)`

for every positive mass vector p, every k >= 2, and every measurable or fractional Gaussian partition with those probabilities. Here I(p) is the established k-cell Gaussian perimeter profile in dimension k-1, H_p is its model interface-area Laplacian, and -Hess I(p)=H_p^+ on the label tangent space. Equality holds precisely for the translated regular-simplex winning partition in dimension at least k-1, extended cylindrically. Below dimension k-1 the bound is strict, with no sharp low-dimensional value claimed.

The complete seven-page proof also establishes a global covariance tangent bound and exact nonnegative deficit integral. It generalizes our [equal-mass immutable theorem](https://github.com/mxym/math/releases/tag/gaussian-balanced-simplex-all-k-v1) using the generally nonzero initial radial derivative. The uniform corollary is not counted as another independently solved conjecture. This result uses a mass-dependent matrix metric and does not assert the false arbitrary-mass ordinary squared-centroid conjecture, the full functional multi-bubble isoperimetric inequality, or positive-noise stability.

## Author and frozen files

Yongxian Zhang, School of Computer Science and Engineering, South China University of Technology, Guangzhou, China. Correspondence: mxymmxym1@gmail.com. ORCID: https://orcid.org/0009-0000-3864-3536. No external funding. Actual AI-assisted proof/manuscript/code/review work is disclosed in the paper; the reviews are internal model reviews, not external human peer review.

Frozen commit: `c60ad6762017d7bea56e9eef849f5b9c2331722c`.

- [Seven-page PDF](https://github.com/mxym/math/blob/c60ad6762017d7bea56e9eef849f5b9c2331722c/research/gaussian-prescribed-mass-centroid-ellipsoid/paper.pdf), SHA-256 `35be8aea53bd949039e65077fbf171a218e188502bccb7eea4f328feee4b3436`.
- [Complete editable proof](https://github.com/mxym/math/blob/c60ad6762017d7bea56e9eef849f5b9c2331722c/research/gaussian-prescribed-mass-centroid-ellipsoid/paper.md), SHA-256 `bef41c3cdf68e11ee5b4d8eb31742952170e1dcca1d510f336f31b497e156126`.
- [Reproduction instructions](https://github.com/mxym/math/blob/c60ad6762017d7bea56e9eef849f5b9c2331722c/research/gaussian-prescribed-mass-centroid-ellipsoid/README.md), [manifest](https://github.com/mxym/math/blob/c60ad6762017d7bea56e9eef849f5b9c2331722c/research/gaussian-prescribed-mass-centroid-ellipsoid/MANIFEST.json), [checksums](https://github.com/mxym/math/blob/c60ad6762017d7bea56e9eef849f5b9c2331722c/research/gaussian-prescribed-mass-centroid-ellipsoid/SHA256SUMS).
- [Partial Lean proofs](https://github.com/mxym/math/blob/c60ad6762017d7bea56e9eef849f5b9c2331722c/research/gaussian-prescribed-mass-centroid-ellipsoid/formal/README.md), [recorded verification](https://github.com/mxym/math/blob/c60ad6762017d7bea56e9eef849f5b9c2331722c/research/gaussian-prescribed-mass-centroid-ellipsoid/results/lean.json), [internal reviews](https://github.com/mxym/math/blob/c60ad6762017d7bea56e9eef849f5b9c2331722c/research/gaussian-prescribed-mass-centroid-ellipsoid/review), [limited literature screen](https://github.com/mxym/math/blob/c60ad6762017d7bea56e9eef849f5b9c2331722c/research/gaussian-prescribed-mass-centroid-ellipsoid/LITERATURE_STATUS.md).

The actual frozen Git archive passed integrity checks and fresh Lean replay: nine proved algebra/abstract-real-analysis exports, 18,016 used declarations replayed in an initially empty kernel at trust level zero, and a false initial-derivative control rejected. The entire Gaussian analytic endpoint and the imported Milman–Neeman geometric theorem are not fully formalized.

The complete package, PDF and logs are committed in this immutable tag. There are no separately uploaded assets because the managed connection returned HTTP 401 at the upload host; use the fixed-commit links and the source archives generated for the locked tag.

The perimeter theorem and profile Hessian identity are explicitly credited to Milman–Neeman. The bounded source screen found no equivalent all-function first-moment theorem in the checked sources; this is not an exhaustive search or worldwide priority claim.
