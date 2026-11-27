# When the plateaued restriction hierarchy is strict

The six nested classes in the abstract, introduction and conclusion of Carlet–Thornburgh's ePrint are all distinct for \(n\ge6\), not \(n\ge5\). At \(n=5\), the quadratic and partially-bent classes coincide, and every plateaued function is the restriction of a six-variable partially-bent function. See the complete dimension table in [PROOF.md](PROOF.md).

The proof also determines the four- and five-variable plateaued-extension classes \(RP_4,RP_5\), the six-variable partially-bent-extension class \(RPB_6\), and gives an odd core obstruction for arbitrary dimension. The principal statement of the source about functions whose restrictions are **all** plateaued is not challenged.

Run `python3 -B verify.py` (Python 3.10+, no dependencies, catalogue, or network); see [RESULTS.txt](RESULTS.txt). The verifier enumerates the small finite cases from alternating-form normal forms with no external classifications, runs two independent Walsh transforms, checks the explicit strictness witnesses, and tests a deliberately invalid extension.
