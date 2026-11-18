# Lower bounds for trifferent codes from all-odd and permutation blocks

A ternary code is **trifferent** if every three distinct words have a coordinate at which all three symbols are different. How large can such a code be? This research note improves an **achievable exponential rate**, not the upper bound or the exact capacity.

Writing rates in bits per coordinate, the ternary result is
$$
R(3)\ \ge\ \frac{1}{88}\log_2\frac{2546192880000}{5441833}
 =0.2140433817797796879\ldots .
$$
For comparison, [Yuan and Zhu, Theorem 3.2 (v2)](https://arxiv.org/html/2611.11262v2) give $0.2120639581206728346\ldots$ by an earlier block construction. The improvement here is in the exponent, not a polynomial prefactor. The nine-letter block consists of all length-11 words in which each of the nine symbols occurs an odd number of times.

For a fixed alphabet of size $q$ and separation of **three** words, set $B(q)=-\tfrac12\log_2((3q-2)/q^2)$. The same note proves $R(q)>B(q)+1/350$ for every $q\ge4$. A permutation-block construction gives
$$
\liminf_{q\to\infty}\big(R(q)-B(q)\big)\ \ge\ \tfrac12\log_2(3/e).
$$
Length goes to infinity first at each fixed alphabet size. No exact limiting gap, improved upper bound, result for linear codes, or efficient construction is claimed.

* [Proof and exact constants](PROOF.md)
* [Prior work and scope](STATUS.md)
* [Independent counting derivations and audit](REVIEW.md)

### Reproduction

From this directory, with Python 3.11 or later (standard library only):

    python3 -B -O cert.py
    python3 -B -O uniform.py
    python3 -B -O independent.py

The decision checks use integers and rational numbers; displayed decimals are not certificates. The main count is checked by parity characters, a nonnegative dynamic program, and a separate conditioned-first-word calculation. The uniform bounds are also independently rechecked by a cycle-coloring recurrence for permutations.

**Status and attribution.** AI-assisted research and independent internal AI review; no external peer review, formal proof certification, or global priority claim. The sampling and Tetra concatenation steps are prior work. Third-party research is cited, not relicensed. No third-party code or article is redistributed here; existing repository notices and third-party rights remain unchanged.
