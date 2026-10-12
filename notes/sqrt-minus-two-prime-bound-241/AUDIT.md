# Audit: layered norm-19/norm-5 finite partition refinement

Internal model-assisted proof review, 8 October 2026. Not an
external mathematical referee or novelty-certification record.

## What is proved without numerical extrapolation

1. **Parent finite proof.** The published period-1122 research note
   has a complete proof that 6,688 explicitly listed connected
   finite lattice sets, covering 204,800 allowed residues, trap
   *every* allowed component of the infinite norm-coprime lattice
   \(V_{1122}\). The parent checker's two raw source files are
   pinned here by their literal SHA256 hashes. The parent analytic
   periodic-lift lemma is an explicitly imported theorem,
   not a numerical solver assumption.
2. **General two-layer finite-to-infinite lemma.** A lattice
   component of an original q-periodic graph is a translate
   \(C_i+qw\). Decomposing the translation vector as
   \(w=u+p_1v+p_1p_2r\) reduces each additional periodic
   predicate to exactly \(p_1^2\) first-stage and
   \(p_2^2\) second-stage finite graphs. Deleting vertices
   cannot enlarge a connected component. Thus it suffices
   to refine only intermediate components above the target
   threshold. The full quantifier argument is written in
   Section 2 of `paper.md`.
3. **Independent exact stage check.** The new checker verifies
   **every** one of 68,590 mod-19 translation configurations
   for the 190 base components exceeding 241. Only eight
   connected filtered components exceed 241. For those eight
   it checks all **200** mod-5 translation configurations.
   Every final connected component has at most 241 vertices,
   and one of cardinality 241 is attained. Graph connectivity,
   literal node membership and cutoff assertions all use exact
   Python integer arithmetic and complete adjacency traversals.
4. **Exceptional irreducibles.** Rational 5 is inert in this
   quadratic ring: the congruence \(a^2+2b^2=0\) modulo 5
   forces \(a=b=0\). At 19 the norm factors as
   \((a+6b)(a-6b)\); the two irreducible generators are
   \(1\pm3\sqrt{-2}\). Their six associates (including
   \(\pm5\)) all occur in the **old exact 90-prime connected
   component**. This is checked against the parent's immutable
   closed exceptional overgraph. Every other irreducible is
   in the refined norm-coprime sieve, yielding \(B\le241\).

## Reproduction commands

```sh
(cd ../sqrt-minus-two-sqrt6-period && python3 code/check_exact.py)
python3 code/check_exact.py
python3 -O code/check_exact.py
python3 code/self_test.py
python3 -O code/self_test.py
sha256sum -c SHA256SUMS
```

The program uses only Python standard-library integer operations,
not floating point, external solvers, or an untrusted generator.
It does not merely load a claimed `max=241`: it recomputes every
necessary finite component under every modular translation.
Independent negative controls exercise the parent hash pinning,
the exact exceptional-set coverage, duplicate-point rejection,
and connected-component BFS behavior in both Python modes.

**Trust boundary.** The written periodic refinement lemma and
inherited complete partition proof remain ordinary mathematics;
this continuation has not been kernel-formalized in Lean.
Correctness of the standard-library integer Python execution
is part of the computer-assisted proof trust. External human
referee review and comprehensive literature comparison remain
outstanding. No historical first-priority claim is made.

## Exact nonclaim

The constant 241 is **sharp for the particular two-prime refined
allowed sieve** but is not established as the true largest
connected component of the graph induced on irreducible
numbers. The known lower witness has 90 irreducibles. More
sieves or a structural prime-only argument might improve the
upper bound further; an equality theorem for the prime graph
is not presented here.
