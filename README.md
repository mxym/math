# Fifty-Eight Disjoint Obtuse Pairs at the Seven-Dimensional First Excess

Any 127 points of a seven-dimensional 60-degree spherical code, if such a configuration exists, have at least 58 pairwise disjoint pairs at angles strictly greater than 120 degrees. The result does not determine the kissing number.

Start with the [main proof](KissingNinePointCapacityAnd127Matching.md) and the [previous barrier argument](KissingOddComponentBarriers.md). Their pinned research commits are `1a6fdc1dc8d4a4a1df7aef313b34e9c21b472400` and `c36c642c5f6984e670f9ba2368f4bfafb5b966d7`. The archive includes the earlier five-point dependency and the newer Gram and barrier checks. The author-external auditor independently wrote the graph census and budget checks; the separate Fraction leaf checker shares the original search engine, but re-verifies all certified leaf inequalities with separately implemented exact arithmetic. This is not a completely independent search algorithm or a journal peer review.

Run `bash replay.sh` with Node.js and Python 3.10+ with NumPy, SciPy and threadpoolctl. The 170-class search can take a while. Optionally run `python3 127_fraction_width_replay.py 9` on a system supporting the multiprocessing fork context for the author-external leaf rerun.
