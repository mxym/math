# Exact spectral gap and unique crossover in Hagendorf’s odd twisted deformed t–J chain

Yongxian Zhang, ORCID [0009-0000-3864-3536](https://orcid.org/0009-0000-3864-3536).

Full Hamiltonian spectral gap for every odd chain length, twist pi and real |zeta| > 1, given by the smaller of an explicit pure-background wave and the lowest eigenvalue of an (N-1)-dimensional one-minority matrix. The two branches cross exactly once, with transition t_*(N)/N^2 tending to 4/pi^2. AI-assisted and internally checked; no peer review or priority claim.

- [Main theorem and proof](ODD-PI-TJ-ALL-LENGTHS.md)
- [Kernel and earlier elementary gap cases](DEFORMED-TJ.md)
- [Cycle partition and single-hole reduction](CIRCULAR-EXCLUSION-CYCLES.md)
- [Finite small-length comparisons and analytic even-sector bound](ODD-PI-TJ-FINITE-CERTIFICATES.md)

Run `node verify-odd-pi-gap-three-minority.js` to replay the 36 required exact finite interval inequalities. The broad `verify-odd-pi-gap-finite.js` cross-checks 1,475 comparisons and can take longer. The scalar certificate in `verify-odd-pi-gap-all-lengths.js` is supplementary, not required for the uniform analytical argument.

Research branch source: [29f588b1](https://github.com/mxym/math/commit/29f588b16edfa76f7f60e53793f4625cb73fdfbe).
