# Exact TDSS for a uniform target and an arbitrary key law

A one-ciphertext, perfectly correct symmetric cipher protects a fixed uniform
message source on \(N\) symbols. The independent key has a prescribed finite law
\(\pi\), not necessarily uniform and not necessarily supported on at most \(N\)
keys. The exact minimum target-distribution semantic-security advantage against
all fixed Boolean predicates is
\[
\frac{2}{\binom N a}\sum_{|A|=a}\left(w(A)-\tfrac12\right)_+,
\qquad a=\lfloor N/2\rfloor.
\]
Here \(w\) is \(\pi\) sorted and padded with zeros if the key support fits, and
otherwise its least \(N\)-coordinate majorant \(R_N(\pi)\): retain the largest
key masses and equalize the remaining mass over the available entries.

The optimal randomized cipher attains the same posterior multiset \(w\) on
every ciphertext, with labels uniformly permuted. This also minimizes every
symmetric convex posterior cost, not only the half-subset hinge. For example,
two key laws with the same largest mass \(0.4\) and the same six-key support
give different exact advantages, \(1/10\) and \(2/15\), for four messages.
For even \(N\), zero advantage is possible exactly when
\(\|\pi\|_\infty\le 1/N\); for odd \(N\) the exact zero criterion uses half
of the largest entries rounded down.

This addresses the nonuniform-key direction in Su–Cheng–Wang, ePrint
2026/1899, §6, for uniform targets and all Boolean predicates. The majorant
was already defined and proved minimal by Cicalese–Gargano–Vaccaro, and the
uniform-key TDSS specialization was previously proved in this repository.
The new result is exact attainability and optimality of the majorant profile
for arbitrary key laws in the stated cipher model. An appendix records how
to use the known decryption-vector LP with a TDSS objective for general
finite priors, without claiming an explicit solution for such priors.

No key-reuse, auxiliary-information, chosen-plaintext, bounded ciphertext
length, or fixed private-coin budget guarantee is asserted. Run
**bash replay.sh** with Python 3 and sha256sum. The rational transport checker
and independent integer-grid exhaustive checker are finite tests of the proof.
