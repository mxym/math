# Two-copy contraction controls every finite copy number

For an independent identically distributed ensemble of finite-dimensional quantum channels, average the tensor power of the same sampled channel across \(r\) copies. The resulting channel has exactly the same subleading spectral radius for every \(r\ge2\). Thus checking two copies is necessary and sufficient to check convergence to a replacement channel at all finite copy numbers.

For conjugation of one channel by any exact unitary 2-design measure, the subleading radius is exactly \(\max\{|\alpha|,u\}\), where \(\alpha\) is the one-copy depolarizing parameter and \(u\) is the channel unitarity. This applies to finite groups, finite weighted designs and Haar measure, even though higher moments of a 2-design need not equal Haar. In particular, the all-copy twirl contracts precisely for nonunitary channels (for \(r\ge2\)).

The proof is about the entire operator space, not just a symmetry-invariant sector. It uses a trace-adapted tensor decomposition and a uniform trace-norm bound on every path of composed channels. A separate diamond-norm estimate has a prefactor linear in \(r\), and an optional covariance criterion works without an exact design.

The prior TrureTuring solution of the Wallman–Flammia two-copy conjecture in the finite exact-design subgroup case is credited. We do not claim a result for correlated sequences or arbitrary experimental gate-dependent randomized benchmarking.

Reproduce the finite checks with Python 3 and GNU sha256sum:

~~~sh
sh replay.sh | diff -u RESULTS.txt -
~~~
