# Simplex and Hamming codes maximize Shannon equivocation on the erasure wiretap channel

**Question.** At a given blocklength and randomization dimension, can another linear coset code hide more of a uniform message than the simplex code, at even one i.i.d. erasure probability? [Harrison and Bloch (2018)](https://doi.org/10.1109/ALLERTON.2018.8635841) conjectured that the answer is no, both for the binary simplex code and for its dual, the Hamming code.

**Result.** The answer is no in the specified model. More generally, let $q$ be a prime power, $d\ge2$, $L=(q^d-1)/(q-1)$ and $n=tL$ for an integer $t\ge1$. A dimension-$d$ randomization code with $t$ generator columns from each projective direction in $\mathbb F_q^d$ uniquely maximizes Shannon equivocation up to coordinate permutations and nonzero scalings, at *every* erasure probability $0<\varepsilon<1$. Its **dual** has the same optimality among dimension-$(n-d)$ randomization codes. At $t=1$ these are the simplex and Hamming families. At the two endpoints all codes with the same parameters tie.

**Model.** Bob receives the whole transmitted word. The message is a uniform coset, its representative is uniform conditional on that coset, and Eve observes the surviving positions and symbols after independent erasures at a common rate. The comparisons run over all linear randomization codes of the same length and dimension, including codes with repeated or zero generator columns. The result does not compare nonlinear or nonuniform encoders, prescribed numbers of *distinct* revealed coordinates, adversarial patterns, general channel models, or other secrecy metrics.

**Why it works.** Remaining message uncertainty is an affine function of the expected rank of the surviving generator columns. Expected rank is concave in the Poisson intensities assigned to the projective directions. Averaging over changes of basis balances those intensities. The positive probability of sampling no point makes that concavity strict; hence any imbalance loses.

- [Proof](PROOF.md): rank identity, strict concavity, comparison among all codes, quantitative gap, and duality.
- [Second derivation](FIXED_DRAWS.md): Dughmi's bounded-lottery argument applied after conditioning on the number of clock arrivals, **not** the number of distinct revealed positions.
- [Prior work and scope](REFERENCES.md): original conjecture, earlier partial results, the two matroid concavity arguments, and related objectives.
- [Verification](CHECKS.md): independent finite tests and the limits of the review.

**Status.** AI-assisted mathematical research and drafting, with separate internal AI adversarial review and exact finite checks. This is not external peer review, a formal proof-assistant verification, or a guarantee of priority. The classical codes, earlier coding results and matroid tools belong to their cited sources. No third-party papers or source code are reproduced in this package.
