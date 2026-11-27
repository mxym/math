# A fourth-moment criterion for the quantum leftover-hash converse

Regula and Cheng's [Theorem 11](https://arxiv.org/html/2611.33270v1)
uses equality of two-, three-, and four-input collision probabilities
to prove a tight one-shot trace-distance bound for privacy amplification.
Their §IV.5 asks how far one can weaken that requirement. We show:

1. Exact two-/three-input collision probabilities plus an upper spectral
   bound on the Gram matrix of centered **pairs** of bin indicators suffice.
   If the spectral bound is \(C\), the converse coefficient is
   \(1/\max\{3,\sqrt{2+4C}\}\). In particular, fourth-order collision
   probabilities may all be bounded above by the independent value, rather
   than equal to it. Bounded positive fourth-order deviations can also
   be permitted. Explicit families over every finite output alphabet
   show that the criterion is strictly weaker than exact fourth-order
   collision probabilities.
2. Three-wise independence alone does not suffice. On a flat input of
   size \(N=mb\), the smallest mean trace-distance error among such
   families is of order \(m/N\), rather than \(\sqrt{m/N}\), with leading
   coefficient \((m-1)/(2N)\) as \(b\to\infty\); exact formulas hold for
   \(m=2,3,4\) and for \(m\ge 2b+1\). This separates the exponents at positive
   rates, and identifies order four as the minimum in the usual
   hierarchy of **strong** \(k\)-wise independence guarantees. This
   does not say that every ensemble needs to be four-wise independent.
3. In the known binary affine family, the pair Gram matrix and the
   source's error can both be evaluated exactly (the error by a finite
   rank sum). This family proves the optimal inverse-square-root order of
   the converse coefficient's dependence on \(C\).

The finite-dimensional quantum theorem permits noncommuting side states.
It concerns an independent public seed, average trace distance to a
uniform output with the real side marginal, and a *converse* (an error
lower bound at the stated benchmark). It is not an assertion that an
algorithm or implementation is insecure. The least possible hypothesis
among all hash ensembles, and the side-informed balancing question at the
end of §IV.5, are not settled here.

See [PROOF.md](PROOF.md) and [SOURCES.md](SOURCES.md) for the
mathematics, scope, and attribution. The verifiers use only the Python
standard library and finite toy examples; they do not replace the proofs.

~~~sh
sh replay.sh | diff -u RESULTS.txt -
~~~
