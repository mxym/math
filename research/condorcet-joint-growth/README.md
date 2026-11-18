# The probability of a strict Condorcet winner when both election sizes grow

If each voter independently picks a uniform ranking, how likely is one candidate to beat **every** other candidate in head-to-head votes? With $m$ voters and $n$ candidates, let $Q(m,n)$ be this probability, requiring a strict majority in each contest.

**Result.** Along every sequence for which both $m$ and $n$ tend to infinity,
$$
\frac{\log Q(m,n)}{\log n}\longrightarrow -1.
$$
No relative growth assumption is required: the electorate may grow more slowly than $\log\log n$, or faster than any power of $n$. Even electorates are covered, with a tied contest not counted as a win. This determines an exponent, not a leading constant or a multiplicative equivalent. It does not supersede the sharper known results at fixed numbers of voters or in the iterated electorate limit.

The proof uses the classical conditional score representation of impartial culture. A change of measure on a candidate's scores supplies the lower bound. A different change of measure on that candidate's pairwise votes gives a matching upper exponent; a deterministic grid is needed because the second tilt is chosen after seeing the scores.

**Application to a different notion of winner.** Among the $2^d$ alternatives on the binary issue cube, a *local* winner need only beat its $d$ immediate neighbors. With sincere independent uniform full rankings, the probability of at least one local winner tends to one, uniformly over odd electorate sizes. The corresponding known limit for independent fair edge orientations is $1-e^{-1}$. This gives the comparison proposed by Conitzer, Lang and Xia for sufficiently large dimension, not for every finite dimension.

- [Proof](PROOF.md), including bounds uniform in the two parameters.
- [Prior results and scope](SOURCES.md) and [independent internal review](REVIEW.md).
- Run `python -O verify.py` and `python -O independent.py`; both use only Python's standard library. The [expected output](CHECKS.txt) documents exact finite regressions, not a computational proof of an asymptotic theorem.

AI-assisted work, independently rederived internally. No external peer review or priority claim.
