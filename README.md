# Sharp reverse Minkowski inequality for Gaussian mass through rank 55 and even rank 72

[New proof and exact certificate](unimodular-gaussian-mass-rank-55-72.md): all integral unimodular lattices through rank 55, equality only for the standard integer lattice, and strict inequality for even unimodular lattices through rank 72. The new ranges are ranks 42–55 for the general integral class and rank 72 for the even class. The inequality holds at every positive Gaussian parameter. No claim is made for arbitrary rank or for every stable lattice.

- New work is fixed at 1e52cdb36e96b18acd0522ccf0cdd518e271d56f. This incorporates the zero-inner-product correction in the even rank-72 certificate.
- The [earlier rank 41 / even rank 64 proof](unimodular-gaussian-mass-rank-41-64.md) is included unchanged from 48a51a51a60c50473259f4aae37ba16c6e9404d3; its [separate archive DOI](https://doi.org/10.5281/zenodo.24593239) remains unchanged.
- Run `node verify-unimodular-gaussian-mass-rank-55-72.js` for the new checks, `node unimodular-gaussian-mass-rank-41-64.js` for the earlier checks, and `sha256sum -c SHA256SUMS` for archive integrity. No external input is needed by the checkers.
