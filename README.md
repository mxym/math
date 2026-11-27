# Constant-success weak lossless rank extraction over a fixed field

We construct labelled families of linear maps from \(\mathbb F_q^k\) to
exactly \(\mathbb F_q^r\), \(1\le r\le k\). Every \(r\)-subspace is mapped
injectively by at least \(1/8\) of the seeds (at least \(23/48\) for
\(q\ge3\)). For each fixed prime power \(q\), the seed counts are at
most \(k2^{6r+o(r)}\) for \(q=2\) and \(kq^{2r+o(r)}\) for \(q\ge3\).
Construction time is polynomial in \(k\) and \(q^r\) for fixed \(q\).
Thus the seed count and construction time are polynomial in \(k\) when
\(r=O(\log k)\).

This answers the success-proportion question of Guo–Raj–Shangguan–Zhang,
arXiv:2604.13431v2, §7 item 5, at the stated seed sizes. It does not give
polynomial size in \(k,r\) for all \(r\), solve their separate
introductory question at a fixed field in all parameters, or assert
distinct matrices, strongly explicit random access, or the strong
rank-loss guarantee. A seed is an index. No cryptosystem claim is made.

- [Proof and parameters](PROOF.md)
- [Sources and related work](SOURCES.md)
- [Expected verification output](RESULTS.txt)

Run from this directory with POSIX sh and Python 3.8 or later, without
dependencies or downloads:

    sh replay.sh

One checker enumerates small matrix spaces and counts killed lines
and triples. The second calculates directly in polynomial-coordinate
extension fields, including over a non-prime field. These computations
test finite cases and bookkeeping, not the general theorem. The general
algorithm invokes the cited small-bias and field-construction algorithms;
the upstream implementations are not vendored.
