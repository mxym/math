# Exact worst-case cost of best-first OR trees

For \(n\ge2\) leaves, the exact supremum of the approximation ratio of
Etemad–Mahmoody–Evans Algorithm 1 is \(\lfloor n/2\rfloor\) for the
sum of internal costs. Including the root visit, the exact ratio supremum for
expected nodes visited is \((2\lfloor n/2\rfloor+1)/3\). Both upper
bounds hold for **every** tie-breaking and arbitrary distributions on
monotone Boolean queries. Instances with just two queries and one keyword
per leaf approach both bounds **for every tie-breaking**. For a
particular legal tie-breaking, one query attains both bounds exactly.

This refutes the unrestricted constant-factor conjecture as formalized
by [AICR c/0015](https://aicr.info/c/0015/) and answers the worst-case
best-first part of the [source paper](https://eprint.iacr.org/2018/052.pdf)
§5. It does not contradict that paper's empirical observations, settle its
hybrid heuristic, or establish any security claim. The arbitrary monotone
queries used for sharpness are not single-keyword or disjunctive queries.
For that restricted workload the related logarithmic approximation is
already known from BINARYMERGING; see [SOURCES.md](SOURCES.md).

[PROOF.md](PROOF.md) gives the threshold comparison and explicit extremal
families. Run `sh replay.sh | diff -u RESULTS.txt -` with Python 3
and no dependencies. The first checker explores partition states and
computes optimal trees by subset dynamic programming. The second enumerates
binary tree topologies and legal greedy histories separately, evaluating
the original root-to-child visit rule directly.
