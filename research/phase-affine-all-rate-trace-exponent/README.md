# Exact all-rate trace-distance exponent for phase-pure affine hashing

For a uniform input over a fixed finite field alphabet, consider
quantum phase states with an optional readable flag that is
independent of the input. Uniform random full-rank linear
hashing has the exact average trace-distance exponent
\[
 \min_{Q\ll P}\big\{ D(Q\|P)
          +(k\log_2 q-R-H_Q(T|Y))_+\big\}.
\]
Here \(P\) is the joint law of the flag and phase label,
\(q\) is the field size, and \(k\) is the input alphabet
dimension over \(\mathbb F_q\). The same exponent holds for
uniform unrestricted matrices, with the single-phase
degeneracy stated separately. This is the classical additive
Gallager random-coding formula, now for the average quantum
trace distance to the **true** side marginal in this model.

The proof reduces each rank-one phase block to a pair-mass
statistic, then bounds its average through finite random
quotient occupancies. It does not assume independent bin
assignments or infer the exponent by taking a square root
of a classical error bound.

In the binary unflagged case this is twice the exponent
displayed in Hayashi's arXiv:1202.0322v6 Lemma 39 at
\(0<R<1-H(\lambda)\). The phase-block decomposition
and type ingredients already appear in v6; the matching
pair-occupancy estimate is the step that gives the exact
trace exponent. The comparison is with that public
preprint (with its positive-rate quotient sequence), not an
unverified typeset version, not arbitrary
quantum states, and not the best or typical hash seed.

[Proof](PROOF.md) · [Sources and scope](SOURCES.md) ·
[Deterministic verification output](RESULTS.txt)

~~~sh
sh replay.sh | diff -u RESULTS.txt -
~~~

The first checker enumerates field-subspace incidences and
uses exact rational square-root enclosures. The second
directly enumerates character averages and computes rational
spectral enclosures. It also checks the variational formula
numerically for several rates and readable flags. Neither
checker supplies a step in the all-parameter proof.
