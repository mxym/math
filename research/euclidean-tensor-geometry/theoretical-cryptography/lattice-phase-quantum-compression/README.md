# The lattice phase of classically assisted quantum compression

Farber–Gour [arXiv:2610.14785v1](https://arxiv.org/html/2610.14785v1) find a limiting assisted/unassisted communication-dimension ratio of \(2/e\) for nonlattice spectra. Their §VI.3 leaves the positive-variance lattice constant as a bounded, potentially cutoff-dependent correction.

For every finite positive-variance lattice log-spectrum and fixed root-fidelity target \(F\in(0,1)\), we give the two individual \(O(1)\) logarithmic terms up to \(o(1)\) and the exact continuous periodic function for their ratio. The phase comes from the fractional mass of the cutoff shell. The LO term is the classical lattice correction of Strassen; we rederive it to compare with LOCC. A first-order lattice Edgeworth calculation gives the phase directly from the source and block length. Except for a stated rational-phase median case, the phases are equidistributed and the ratio does not converge. In the exceptional case the formula gives the finite list of subsequential limits; already \((1/2,1/4,1/4)\) at \(F=1/2\) gives limits \(17/24\) and \(3/4\).

The result uses the known one-shot optima and covers compression preserving a purification, with one noiseless quantum transmission and, for LOCC, free classical communication without preshared entanglement. It does not solve the separate state-merging problem with nontrivial side information at Bob. A final classical corollary uses a uniform-alternative hypothesis test to show exactly why a later single-constant formula cannot include the lattice case; it is not needed for the LOCC result.

Run ./replay.sh for two independently implemented checks (exact rational shell arithmetic and numerical tilted-shell convolution/bisection). They check finite examples, not the proof.
