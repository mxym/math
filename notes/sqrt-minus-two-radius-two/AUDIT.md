# Scope, proof dependencies and reproducibility audit

8 October 2026. This is an internal model-assisted correctness audit,
not an external referee report or priority assessment.

## Proof interface

1. **Infinite-graph theorem.** Factorization and unique-factorization
   of `Z[sqrt(-2)]` are proved by the norm-Euclidean rounding
   argument. Irreducibles not divisible by the three factors of 6
   lie in `V_6={gcd(N(z),6)=1}`. A direct mod-six congruence analysis
   partitions this *entire infinite set* into disjoint two-point
   lattice components under the ten steps of squared norm at most
   four. No spatial search window or finite-only extrapolation is
   used.
2. **Exceptional global component.** The finite set `W=V_6 union E`
   contains every irreducible, where E is the six associates of the
   ramified/split prime factors of 6. A 16-vertex finite set is
   directly proved closed under all allowed W-neighbors and reachable
   from E, hence is the **full** exceptional closure. Literal
   norm-bounded trial division shows fourteen are irreducible,
   decomposing into exactly two seven-vertex components; the other
   two points are the units. Every remaining prime component lies
   inside one of the periodic two-point components of V_6.
3. **Sharp scalar period.** Every nonunit generator g of common scalar
   period Q has `g|Q` and `N(g)|Q^2`. Hence all norm-coprime
   points V_Q survive every such ideal. For Q=1,...,5, explicit
   admissible lattice walks produce nonzero Q-translation, and
   their periodic repetition is an infinite component. The three
   prime ideals over 2,3 yield a successful period-six sieve.
4. **Complete generator classification.** Factorization
   `6 ~ t^2(1+t)(1-t)` yields exactly eleven nonunit divisor ideals.
   Any list of scalar period six selects a subset of them, including
   composite generators. The three-prime list succeeds. If any of
   its prime ideals is missing, the surviving graph contains that of
   a **maximal ten-ideal negative list**, for which an exact nonzero
   six-period walk is supplied. Thus precisely the lists containing
   all three prime ideals succeed. This argument is universal over
   every list, not merely the 2,048 explicit subfamilies.

## Independent exact evidence

The four positive quotient pairs, sixteen closure points, three
maximal-failure walks and five smaller-period walks are frozen in
`code/certificate.json`. The independent verifier
`code/check_exact.py` imports **neither** the witness generator nor
any third-party solver. It checks integral ideal divisibility by
`N(g) | ac+2bd,bc-ad`; all neighbors of every finite component;
uniqueness and completeness of quotient residues; exceptional
reachability, primality by complete norm-bounded divisors, and all
per-step admissibility/nonzero-period displacements. A second
independent BFS exhausts all 2,048 subsets of 11 ideals, finding
256 successes exactly as the mathematical classification predicts.

Replay:

```sh
python3 code/check_exact.py
python3 -O code/check_exact.py
python3 code/self_test.py
python3 -O code/self_test.py
sha256sum -c SHA256SUMS
```

All program branches use explicit exceptions (not language `assert`)
so `-O` does not suppress certificate checking. The tamper suite
corrupts positive classes, closure points, maximal negative paths and
lower-period witnesses and confirms rejection, plus performs small
irreducibility regression tests.

**Formal boundary:** The proof of norm-Euclideanity, the analytic
infinite pairing, the periodic-lift argument, and the universal ideal
classification are written mathematics rather than full Lean
formalizations. Python's exact integer operations and the public
checker are the computational trust dependencies. Human independent
review remains to be done.

## Relation to prior work and open extension

The earlier [D<2 paper](../sqrt-minus-two-sharp-moats/paper.md)
remains a fixed historical statement with its own checker. This
note adds the genuinely new threshold `D=2` and persists until the
next possible step norm `sqrt(6)`. The idea of periodic prime sieves
comes from OpenAI/math result 028, and the broader quadratic-order
transfer appears in mxym/math entry 002. These dependencies and
version scopes are explicit; no historical priority claim is made.

Further classification at `D=sqrt(6)` or beyond and extension to
additional norm-Euclidean fields remain open within this programme.
