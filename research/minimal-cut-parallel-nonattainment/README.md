# No finite parallel template attains the growth rate of minimal vertex cuts

How many inclusion-minimal sets of vertices can disconnect an $n$-vertex graph? Erdős and Nešetřil asked about the exponential growth rate. Its existence and the fact that it is below two are known, but the exact value is not. Some of the best lower-bound constructions replicate a single graph many times, identifying just two terminals of every copy. **No fixed finite collection of such graphs, mixed and repeated in parallel in any order, reaches the extremal exponential rate.**

Write $c(n)$ for the maximum number of inclusion-minimal disconnecting sets among simple undirected graphs on $n$ vertices. In a connected graph with two distinct marked vertices, call a minimal separator of them *clean* if deleting it leaves exactly two components. If $h(p)$ is the largest clean count on $p$ internal vertices, the proof gives
$$
\lim_{n\to\infty}c(n)^{1/n}=\sup_{p\ge 1}h(p)^{1/p},\qquad h(p)^{1/p}<\sup_{q\ge 1}h(q)^{1/q}\quad(p\ge 1).
$$
The strict inequality follows from an explicit construction that takes any fixed cell and improves its normalized clean count. For any parallel assembly from a fixed finite menu, the count of **all** global minimal cuts differs from the product of the cells’ clean counts by at most a linear term in the number of cells. Thus ordinary rooted separators and global cuts need not coincide on an individual graph.

**Scope.** Each cell is finite, connected, undirected, with distinct terminals and at least one internal vertex. This result does not determine the constant, establish a new decimal lower bound, or exclude growing cells, infinite dictionaries, or general recursive constructions. The two-terminal repetition, limit framework, connected-set counting lemma, and middle-layer gate idea all have precedents; see [sources and search limits](SOURCES.md).

[Proof](PROOF.md) · [Independent mathematical review](REVIEW.md) · [Test output](CHECKS.txt). Both programs below use only Python's standard library. The finite checks support, but do not prove, the universal statement.

```sh
python3 verify.py
python3 independent.py
sha256sum -c SHA256SUMS
```

This is an AI-assisted research draft with an independent internal AI check, not external peer review. No assertion of priority is made. References remain the work of their respective authors.
