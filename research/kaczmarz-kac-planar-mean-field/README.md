# The planar Kaczmarz–Kac mean field

**Yongxian Zhang.** AI-assisted mathematical research note. Independently reviewed internally; not externally peer reviewed. No claim to worldwide priority.

At fixed finite particle count, the planar walk eventually chooses one orthogonal cross. If the number of particles first tends to infinity at fixed scaled time, it does something different: from any iid initial angular density, the limiting density converges to the average of that density and its three right-angle rotations. It does **not** concentrate into four atoms. The exponential relaxation rate $1-2/\pi$ is sharp, attained by a smooth initial density with a single cosine perturbation.

The [proof](PROOF.md) identifies the gain from the actual projection, proves fixed-time convergence for both the Poisson clock and the discrete walk, and then solves the long-time problem. It also treats the different equation proposed in Steinerberger's arXiv §2.3: that equation itself has an explicit smooth limiting profile, which in general differs from the particle limit. The particle approximation is not claimed uniform over all times. This is not a model of the classical random-rotation Kac walk.

See [sources and scope](SOURCES.md), [internal review](REVIEW.md), and the separate [finite-particle result](../kaczmarz-kac-absorption/README.md). The public proof adds a separately checked paragraph on fixed discrete step counts to the frozen internally reviewed proof. Reproduce the finite consistency checks with `sha256sum -c SHA256SUMS` and `python3 -O verify.py`, comparing [expected output](CHECKS.txt).
