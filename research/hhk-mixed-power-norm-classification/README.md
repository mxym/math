# Which norms are monotone under the Hayajneh–Hayajneh–Kittaneh mixed powers?

Fix a dimension $d\ge2$ and just **one** pair of exponents $1/2\le s<t<1$. Write $M_u=A^uB+BA^{1-u}$ for a positive semidefinite matrix $A$ and a Hermitian matrix $B$. The inequality $N(M_s)\le N(M_t)$ holds for all such matrices in that dimension **if and only if** the unitarily invariant norm $N$ is a positive multiple of the Hilbert–Schmidt norm.

The positive direction is the original authors' theorem. The all-norm conjecture was already refuted by trureturing using the trace norm. This note classifies the norms for each fixed interior pair; it does not claim the original refutation or the classical corner-erasure phenomenon. For every Schatten exponent other than 2, including the operator norm, a real two-dimensional counterexample suffices. For example, one pair of rational matrices puts the two operator norms strictly on opposite sides of $79/20$.

The case $t=1$ is outside this classification. The pair $(s,t)=(1/2,1)$ is known to work for all unitarily invariant norms. No analogous high-exponent result is claimed if $B$ is required to be positive.

- [Proof and explicit examples](PROOF.md)
- [Original question and prior results](SOURCES.md)
- [Independent AI mathematical review](REVIEW.md) and [exact check transcripts](CHECKS.txt)
- Reproduce: run `python -B -O verify.py` (Python 3 and SymPy), then `python -B -O independent.py` (Python 3 standard library only); check the seven payload files with `sha256sum -c SHA256SUMS`.

**Status:** research draft, internally AI-reviewed, not externally peer reviewed. No worldwide priority claim. The scripts verify finite identities, not the theorem's universal quantifiers.
