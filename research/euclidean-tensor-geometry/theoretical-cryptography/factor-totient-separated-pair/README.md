# One totient value for a separated pair and a close cluster

This is a promise theorem about integers, not a claim that the extra totient is computable from the integer alone. Fix k>=4. A squarefree N has k comparably sized prime divisors of order X, two of them in one cluster and k-2 in another. The geometric centers are separated by a fixed positive multiple of X. If the two diameters have respective exponents strictly below min(1/2,4/k) and min(1/2,2/(k-2)), its complete factorization follows deterministically in polynomial bit time **from N and the single exact value phi(N)**. The groups, means, and their order are not given. The four-factor case has a lattice-free proof.

The useful observation is that fitting two multiplicative moments makes the unknown pair's *integer sum* recoverable, while its product differs from one quarter of that sum squared by only one quarter of its squared gap. The subsequent arithmetic uses an existing linear small-root theorem, not a new lattice algorithm. The proof includes the noncoprime input branch, a positive shell lower bound, and explicit limitations. No hypotheses about deployed keys, systems, or protocol security are made.

Read PROOF.md for the theorem, UPSTREAM.md for the bounded comparison, and RESULTS.txt for actual finite replay output. The checkers use only Python 3 standard library and hard-coded labelled mathematical fixtures. They are not factorization software and do not instantiate or test the cited all-input asymptotic lattice theorem.

    python3 -B check_centers.py
    python3 -B check_identities.py
    sha256sum -c SHA256SUMS
