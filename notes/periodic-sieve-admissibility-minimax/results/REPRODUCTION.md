# Exact reproduction of the 197 instantiation

The structural minimax theorem in `../paper.md`, Sections 2–3, is a self-contained written proof and does not depend on running any program. Its CRT and rooted connected-shape arguments apply to **arbitrary** local sieve predicates.

For the concrete equality `197` in `Z[sqrt(-2)]`, the **lower** witness consists of the complete 197 integer point list and the 45 small-prime shifts in the frozen adjacent directory `../../sqrt-minus-two-universal-sieve-barrier/`. The checker additionally establishes all-prime admissibility by the rigorous large-prime splitting argument from that paper. Run:

```sh
(cd ../../sqrt-minus-two-universal-sieve-barrier && python3 code/check.py)
(cd ../../sqrt-minus-two-universal-sieve-barrier && python3 -O code/check.py)
(cd ../../sqrt-minus-two-universal-sieve-barrier && python3 code/check_projection.py)
(cd ../../sqrt-minus-two-universal-sieve-barrier && python3 code/self_test.py)
```

The **upper** witness is the frozen complete period-1122 partition followed by six exhaustive layered congruence refinements, max component `197`, in `../../sqrt-minus-two-exact-sieve-optimum/`. Its independent checker pins source-data hashes and recomputes all literal filtered adjacency components. Run:

```sh
(cd ../../sqrt-minus-two-sqrt6-period && python3 code/check_exact.py)
(cd ../../sqrt-minus-two-exact-sieve-optimum && python3 code/check_exact.py)
(cd ../../sqrt-minus-two-exact-sieve-optimum && python3 -O code/check_exact.py)
(cd ../../sqrt-minus-two-exact-sieve-optimum && python3 code/self_test.py)
```

The full checks were previously replayed in both modes and their logs and SHA256 file lists remain bundled in those directories. This minimax manuscript does not mutate any of those certificates.
