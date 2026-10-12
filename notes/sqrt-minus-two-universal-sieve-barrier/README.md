# A universal 197-point obstruction to every finite principal-ideal sieve

Research note, 8 October 2026. [Full written proof](paper.md) ·
[197-point exact configuration](code/connected_shape.json) ·
[45 complete local shift certificates](code/local_shifts.json) ·
[independent exact checker](code/check.py) ·
[second projection checker](code/check_projection.py) ·
[replay evidence](results/replay.txt) · [scope audit](AUDIT.md).

## Theorem

Let \(R=\mathbb Z[\sqrt{-2}]\), with the genuine Euclidean
14-step graph on coefficient lattice differences of squared
norm at most 6 (equivalently, radius \(\sqrt6\le D<\sqrt8\)).
There is an explicitly recorded set **S of 197 distinct, connected
lattice points** satisfying the striking universal condition:

> For **every finite set** of rational primes, some integer
> translation of S has norm not divisible by any of those primes
> at **any** of its 197 vertices.

It follows by an explicit CRT and norm-divisibility argument that
**every finite principal-ideal sieve**, regardless of the scalar
period or arbitrary composite/redundant generators, leaves a
connected allowed lattice subset of **at least 197 vertices**.

The separately published [two-layer exact sieve](../sqrt-minus-two-prime-bound-241/README.md)
attains a maximum allowed-lattice component size **241**. Hence the
optimal such certificate bound lies in the rigorous interval

\[
\boxed{197\le\inf_{\text{successful finite principal sieves}}
       \max|\text{allowed component}|\le241}.
\]

**Crucial distinction:** This is a **barrier for the finite
principal-ideal sieve method**, **not** evidence for 197
neighboring irreducible elements. The true *prime-only* graph
continues to satisfy the separate certified interval
\(90\le B_D\le241\); its exact maximum remains open.

## Why a finite certificate proves a universal result

The core is a general **admissible connected-pattern lemma** for
integral lattices with multiplicative norms. To avoid a given
finite principal-ideal list, only its finitely many rational
prime divisors of the common scalar period matter. A
Chinese-remainder translation of the pattern avoids all of
those prime factors simultaneously.

For the norm \(N(a,b)=a^2+2b^2\), the paper proves that for any
pattern of m points **every rational prime p>m** automatically
admits a norm-avoiding translation: inert primes forbid at most
m points in \(\mathbb F_p^2\); split primes reduce to two
incomplete linear projections. Thus the finite certificate only
needs to handle **the 45 primes p≤197**. Every one of those has
an explicit integer translation in the bundled JSON file.

## Independent reproduction

From this note's directory:

```sh
python3 code/check.py
python3 -O code/check.py
python3 code/check_projection.py
python3 -O code/check_projection.py
python3 code/self_test.py
python3 -O code/self_test.py
sha256sum -c SHA256SUMS
```

Two **different** implementations check the small-prime
feasibility: one tests all 197 norm values against all 45
literal proposed translation vectors; the other verifies the
split/inert/ramified projection conditions **without even
reading** the translation table. The graph checker independently
tests exact 14-step connectivity, full cardinality, and lack
of duplicate vertices. Mutation tests reject tampered paths,
points and prime-index sets under ordinary and optimized Python.
No closed-source solver, float or external database is needed.

`code/generate_local_shifts.py` is a nontrusted deterministic
producer. The mathematical proof is the written local-prime
lemma plus the independently verified finite inputs, not the
producer's success message.

## Provenance and nonclaims

This note continues the quadratic-order sieve research of
repository entry 002, drawing on the finite prime-sieve approach
of OpenAI/math family 028, pinned at
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The earlier
specific sharp-period theorem, 90-prime lower witness and 241
upper sieve are linked and kept unchanged. The 197 configuration
is **not** asserted optimal, and the optimal finite-sieve bound
is not determined exactly. The note is AI-assisted, not an
external referee review, full Lean proof or novelty-first claim.
