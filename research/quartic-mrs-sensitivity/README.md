# Two exact nonconsecutive quartic sensitivity laws

The two smallest nonconsecutive rotation-symmetric quartic shapes, up to reflection, have different large-size behavior. The shape `{0,1,2,4}` has bounded periodic sensitivity deficit. The shape `{0,1,3,4}` has a linear deficit: only a fraction approaching 10/11 of coordinates can simultaneously be sensitive.

[PROOF.md](PROOF.md) gives exact formulas for all admissible (n), their dilations and reflected copies, and a finite-width theorem. The two infinite exact formulas use rigorous integer dynamic programming with a repeat certificate for the full transition matrix. They do not follow from fitting an observed sequence and do not claim to settle every arbitrary quartic support in the source paper's open problem. The earlier consecutive results are not re-proved here.

Run `python3 -B verify.py`. No network, external data, or third-party dependencies are needed. The small-dimension truth-table check uses the distinct orbit convention, including the genuine three-term short orbit at (n=6) for `{0,1,3,4}`.

For a transcript generated directly by the verifier, see [RESULTS.txt](RESULTS.txt). It prints both formulas from its model constants, the small lengths and orbit sizes, the full matrix checks, and an independent optimum check for every length used in the preperiod or residue proof. Two deliberately false controls are rejected.