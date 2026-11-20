# Four collective local turns do not discriminate the two-copy Watrous basis

**Main theorem.** The ensemble in [Bandyopadhyay, arXiv:2610.16138v2](https://arxiv.org/abs/2610.16138v2), Eq. (6), cannot be discriminated perfectly by A–B–A–B or B–A–B–A LOCC, even if each local turn acts jointly on both copies. The first operation counts as a turn and the last laboratory makes the decision. **Five or more turns are not excluded.** A collective separable measurement was already explicitly constructed in the cited source. This is not the different two-qutrit instance for which two copies fail even under PPT.

Read **watrous.pdf** for the four-page proof. **watrous.tex** is its LaTeX source (compile twice using pdfLaTeX). No SDP or computer calculation is required as a premise. The optional script **gram_check.py** independently constructs the complex Gram matrix from the two local coefficient matrices using SymPy Kronecker products and checks its real and imaginary reductions symbolically:

    python3 -O gram_check.py

[Full paper and code ZIP](Watrous_Four_Local_Turns.zip) (SHA-256 `f63c0c51035ab29b5c7dbba91344f3f6848e563ab5160d1ea28409cbd1679afe`). This is the specific two-qubit example of Watrous, documented by [Bandyopadhyay](https://arxiv.org/html/2610.16138v2), and not the [two-qutrit counterexample](../two-copy-collective-ppt/README.md). Four or fewer alternating local turns are excluded; five or more and unrestricted collective LOCC for this two-qubit example are not settled.
