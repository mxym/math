# Odd cycles and odd-population solvability in random stable roommates

When a random roommates instance has no stable matching, how many people are on the odd cycles that obstruct one? With independent, uniform, strict and complete rankings, the conditional mean is asymptotic to **$\sqrt{\pi n/8}$**. This holds for both even and odd populations. Mertens (2005, Conjecture 2) proposed the smaller order $\sqrt{n/\log n}$ for even populations; Glitzner and Manlove (arXiv:2505.06717v3, Conjecture 3) proposed that order for odd populations.

### The odd-cycle mass

Tan proved that stable cyclic partitions exist and all have the same odd cycles for a given instance. Let $X_n$ count the people on them, including a possible singleton. It is an **instance statistic**: we do not sample a stable partition or weight instances more heavily when they admit many partitions. The result is the distributional limit
$$
\frac{X_n}{\sqrt n}\ \Longrightarrow\ R B,
\qquad
R\sim\operatorname{Rayleigh}(1),\quad
B\sim\operatorname{Beta}(1/2,1/2),\quad R\perp B.
$$
All positive integer moments converge, both unconditionally and given nonsolvability. Here $R$ has density $x e^{-x^2/2}$ on $x>0$ and $B$ has the arcsine law on $[0,1]$. In particular the mean gives the constant above.

### The probability of a stable matching for odd populations

For odd $n$, a solution leaves one person unmatched. That person ranks everyone above being alone and **still counts in a blocking pair**. This differs from removing a person from the market before testing for stability. Under this convention we find
$$
\Pr(\text{solvable})\sim C n^{3/4} e^{-\sqrt n},
\qquad
C=\frac{e^{1/4}}{2\sqrt\pi}
\int_0^\infty \frac{1-e^{-t-2t^2}}{t^{3/2}}\,dt.
$$
In particular the decay is not of order $1/n$ as proposed in Glitzner–Manlove Conjecture 1. The even-population solvability asymptotic of Young and Studebaker is prior work, not a result claimed here.

### Proof and verification

1. [Invariant mass: reduction, integral estimates, and moment calculation](PROOF.md). Fix the odd cycles before cancellation; this turns a signed sum over partitions into a count of instances. Mark their total length, then take a Gaussian-scale sum of the signed coefficients.
2. [Odd populations and the rare solvability probability](ODD.md). The unmatched person introduces a factor that changes the integral even after normalization. Its dependence on the cycle length matters for the leading constant.
3. [Primary sources, attribution and limits of the search](SOURCES.md). In particular, the stable-partition machinery, signed solvability formulas, and common-kernel estimates used here are prior contributions.
4. [Exact finite checker](check.py) and [output](CHECKS.txt). Run `python3 -BO check.py` with the standard library. It checks all labeled profiles for three and four people, samples larger profiles, compares 259 marked coefficients and 5,775 parity multipliers, and recovers Mertens's exact odd solvability probabilities at $n=3,5,7$. These checks do not prove the asymptotics.
5. [Internal check of the mass proof](REVIEW.md) and [of the odd-population proof](ODD_REVIEW.md). To verify the exact reviewed files, run `sha256sum -c SHA256SUMS`.

This is an AI-assisted research draft, with separate internal AI checking. It has not received external peer review or formal verification. It makes no priority guarantee, does not address other ranking distributions, and does not claim to settle different stable matching or partition-counting questions.
