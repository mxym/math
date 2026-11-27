# Fernando–Kousik Question 6.7

For each integer \(e\geq4\), let
\[
 n_e=1+3\cdot4+3\cdot4^2+2\cdot4^3+4^e+4^{e+1}.
\]
Then the defining polynomial \(g_{n_e,4}\) permutes \(\mathbb F_{4^e}\) **if and only if \(e=4\)**. This answers the exact one-parameter Question 6.7 of Fernando–Kousik, not the other questions in §6. The positive triple \((1469,4;4)\) is already listed by Fernando–Hou; the result excludes all other extension degrees.

The proof derives a simple trace expression from the defining four-translate sum. A nonzero kernel excludes every degree divisible by 3. Otherwise, a character-sum count gives a trace-layer collision for every \(e\geq10\); the three remaining negative cases have explicit small certificates. The positive case is an exhaustive check on 256 inputs in two polynomial bases. The displayed expression in the question is a functionally correct representative on the target field; the proof records its precise formal difference from the defining polynomial.

- [PROOF.md](PROOF.md): theorem, proofs, and exact small-case certificates.
- [SOURCES.md](SOURCES.md): primary sources, previous finite cases, and scope.
- Run `sh replay.sh | diff -u RESULTS.txt -` with Python 3, assertions enabled, and a POSIX shell. Two standalone implementations check the finite cases; the second directly evaluates the original four translates with the original integer exponent and independently checks the formal coefficients. No downloads are required.
