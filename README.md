# Graphical progression-free subset sums

**Yongxian Zhang** (ORCID: [0009-0000-3864-3536](https://orcid.org/0009-0000-3864-3536)). Version 1.0.0. AI-assisted mathematics and internal verification; no external peer review claimed.

This archive gives an exact graph feasibility criterion for avoiding a nonconstant (k)-term progression in the subset sums of distinct positive edge distances, and an exact minimum cardinality for every simple cactus in the four-term case. Companion notes give sharp large-(k) entropy for injective projection and the no-radix critical-clique product corollary of the cited prior work. This is not an unrestricted solution of Erdős problem 817.

- [General graph criterion](Erdos817GraphCutClassification.md)
- [Exact cactus formula](Erdos817CactusMinimum.md)
- [Sharp injective graph entropy](Erdos817InjectiveForestEntropy.md)
- [Critical clique factorization](Erdos817CriticalCliqueFactorization.md)

Run `c++ -std=c++17 -O3 erdos817-clique-projection.cpp -o verify && ./verify` for the independent finite checks. Verify the archived file bytes with `sha256sum -c SHA256SUMS`.
