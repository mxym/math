# Superlinear edge necessity for near-linear Ryser equality families

We prove that if \(r_j\to\infty\), \(H_j\) is finite, simple,
intersecting, \(r_j\)-partite and \(r_j\)-uniform, and
\[
 \tau(H_j)\ge r_j-1,\qquad
 I(H_j)=\sum_{\{A,B\}}(|A\cap B|-1)=o(r_j^2),
\]
then \(|E(H_j)|/r_j\to+\infty\). In particular,
\(f_{\rm lin}(r)/r\to+\infty\), taking an empty extremal class to
have minimum \(+\infty\).

A quantitative consequence is that a linear family with at most \(Cr\)
edges, for fixed \(C\ge1\), has
\(\tau(H)\le(1-1/(2(C+1)))r+O_C(1)\). Thus a bounded edge budget
forces a positive fractional gap from the Ryser equality cover number.

The [complete deduction](paper.md) and [PDF](paper.pdf) establish a
degree-parameter inequality for every fixed \(D\ge4\). Its lower
coefficient \(1/2+\sqrt{2D}\) is unbounded. Each retained size-\(d\)
incidence block is replicated \(d-3\) times, aligning weighted matching
gain and star saving. All excess penalties and fixed-parameter errors are
included; the limit keeps \(D\) fixed before taking the rank to infinity.

Kahn's published small-codegree edge-colouring theorem is the explicit
external input. Its convention permitting parallel edge copies was checked
in the primary manuscript. The degree-three preprint lemma and OpenAI/math
are not needed for this theorem. Peeling and matching/star tools are
attributed to their methodological sources.

```sh
python3 verify.py
./formal/bootstrap.sh
ELAN_HOME="$PWD/formal/.elan" PATH="$PWD/formal/.elan/bin:$PATH" python3 verify.py --lean
./build.sh /tmp/superlinear-partite-paper
```

Exact standard-library checkers replay polynomial identities, weighted
deletion, copied incidences, proper colour-class averaging and cover
diagnostics, including damaged-copy rejection. Six partial Lean exports
check the general scalar identity and implications. See [audit scope](AUDIT.md).
The colouring theorem and finite combinatorics are not fully formalized.

This is a structural continuation of the [same research programme](../partite-intersection-defect-cover/README.md).
It gives no explicit superlinear rate, existence at every rank, resolution
of Ryser, disproof of the full nonlinear \(f(r)=O(r)\) conjecture or
priority claim. The [dated literature comparison](../../research/novelty-assessment/2026-10-07-ryser-linear-superlinear-screen.md)
is limited to the sources searched.
