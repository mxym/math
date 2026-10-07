# Rank-six counterexamples require at least twenty edges

[Complete proof](paper.md) · [PDF](paper.pdf) · [Audit scope](AUDIT.md)

Every finite simple intersecting six-partite six-uniform hypergraph
with at most nineteen edges has a five-cover. There is no width bound
in this theorem. It strengthens the repository's prior nineteen-edge
necessary condition and leaves the unrestricted rank-six case open.

The proof explicitly imports the **known f(6)>=13 theorem**:
at most twelve edges admit a four-cover. This earlier result is proved
by Abu-Khazneh–Pokrovskiy and independently by Aharoni–Barát–Wanless.
Here `f(6)` concerns `tau>=5`; our new necessary bound concerns
`tau=6`. They are different minimization problems. The known theorem,
whose full elementary proof is reproduced with attribution in Appendix A,
forces maximum degree at most six at nineteen edges. A small excess
budget and all four-vertex cover budgets then give the contradiction.

The next case has a complete finite search scope: a twenty-edge
counterexample would have degrees at most seven, at most eight active
vertices in each part, and a disjoint five-cover after deleting each
edge. No exclusion of that case is asserted.

```sh
python3 verify.py
cd formal
./bootstrap.sh
cd ..
export ELAN_HOME="$PWD/formal/.elan"
export PATH="$ELAN_HOME/bin:$PATH"
python3 verify.py --lean
```

Use an existing elan installation by setting `ELAN_HOME` before
bootstrap. Mathlib and its dependencies are pinned. Nine scalar Lean
exports accompany the written proof; hypergraph covers and the full
f(6) appendix are not formalized here. The exact finite checker is a
diagnostic companion, not a SAT certificate or a substitute for the proof.

The optional `search20.py` is an exploratory SAT discovery tool. Install
the pinned `requirements.txt` in a virtual environment, then run:

```sh
python search20.py --edges 20 --vertices-per-part 8 --root-flower \
  --label-precedence --private-neighbours --edge-critical --seconds 240 \
  --output candidate20.json
```

The recorded bounded run in `results/experiment.json` found no candidate.
It supplies no UNSAT certificate or mathematical exclusion. Any candidate
must be checked independently with the earlier `verify_witness.py`.

`./build.sh` writes a PDF to `/tmp/rank-six-twenty-paper`. The published
nineteen-edge package is preserved. No general nonpartite g(6)>=20,
priority, outside peer review or complete Lean proof is claimed.
