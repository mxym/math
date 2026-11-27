# Bounded-order covering for flat conditional quantum outputs

This note gives a restricted answer to the noncommuting covering question in
[Wilde, arXiv:2611.25496v1, §7.2](https://arxiv.org/html/2611.25496v1#S7.SS2).
It concerns **normalized trace distance with the table register retained**,
not secrecy under any unspecified device or implementation model.

* For any finite classical alphabet and conditional outputs $P_x/r$ with the
  same projection rank $r$, a spectral-row estimate removes the extra
  half-logarithmic covering cost, both for ordinary uniform placement and
  against the actual marginal in the row/whole-table comparison. Neither
  independent triples nor a common diagonal basis are needed.
* For **all pure** conditional outputs, and more generally fixed-rank flat
  outputs for which the average-state spectral projections commute after
  compression to each individual support, a regularized Gram test gives a
  matching ordinary uniform-placement converse. In the Gaussian window the
  error differs from the spectral upper tail by $O(n^{-1/2})$; the least
  $\log_2 K$ differs from its Gaussian quantile by $O(1)$ bits. No matching
  row/whole-table converse is claimed.
* The positive bound improves the covering term in Wilde's private-code and
  one-way key achievability proofs with the same Eve marginal and the same
  joint half-trace-norm error criterion. It is not a coding converse.

One noncommuting rank-one example uses probabilities $2/5,3/5$ on
$|0\rangle$ and $(3|0\rangle+4|1\rangle)/5$. Tensoring that example
with $I_r/r$ gives noncommuting rank-$r$ examples with compatible
compressions for all $r$.

See [proof](PROOF.md) and [source comparison](SOURCES.md). Run
`sh replay.sh` with Python 3 and NumPy to reproduce [the log](RESULTS.txt).
The first checker is exact rational arithmetic. The second is an independent
spectral/numerical diagnostic. Neither replaces the proofs.
