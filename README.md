# The seven-dimensional kissing number under irreducible symmetry is 126

A kissing configuration in seven dimensions whose orthogonal symmetry group acts irreducibly on the ambient real space has at most 126 points. The known E7 root configuration attains the bound. Irreducibility means that no nonzero proper linear subspace is preserved by all the symmetries; it does not require the points to form one orbit. No conclusion is asserted about the unrestricted optimum or uniqueness among all irreducible maximizers.

- [Main theorem](KissingSevenIrreducible.md), including the final affine-group case and its explicit positive-definite polynomial.
- [Many-orbits theorem](KissingSevenManyOrbits.md), including equality only for the narrower classes covered there.
- [Point-transitive bound](KissingSevenVertexTransitive.md) and [equality proof](KissingSevenTransitiveUniqueness.md), included as dependencies and previously archived at [DOI 10.5281/zenodo.24606356](https://zenodo.org/records/24606356).
- Rerun the main certificate with `python3 verify-kissing-seven-irreducible-coefficients.py`, `node verify-kissing-seven-irreducible.js`, and the same Node command with `--alternate`. The separate test is `node verify-kissing-seven-irreducible-independent.js`.
- Rerun the many-orbits certificate with `python3 verify-kissing-seven-many-orbits.py`, and again with `--vertices`. The separate test is `python3 verify-kissing-seven-many-orbits-independent.py`.
- The two point-transitive checkers take no arguments. Run `sha256sum -c SHA256SUMS` for payload checks.

[Tomar](https://www.mefyi.com/papers/kissing-numbers-five-seven/) supplies the unrestricted upper bound 132, and [Anstreicher](https://optimization-online.org/wp-content/uploads/2001/01/248.pdf) supplies the antipodal case. The finite linear and permutation group inputs are [Wales](https://msp.org/pjm/1970/34-1/pjm-v34-n1-p21-p.pdf) and [Butler–McKay](https://doi.org/10.1080/00927878308822884).

Research source: [42d1ae0](https://github.com/mxym/math/commit/42d1ae0e4e77312d8fb4afdf4dbaee6b3aed505d).
