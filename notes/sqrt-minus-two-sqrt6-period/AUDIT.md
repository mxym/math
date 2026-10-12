# Exact certificate validation and mathematical scope audit

Internal model-assisted audit, 8 October 2026. This is not a human
referee report, a formal kernel certificate for all analytic proof
steps, or a priority investigation.

## Mathematical closure dependencies

1. **Number theory.** Norm \(N(a+bt)=a^2+2b^2\) is Euclidean;
   an explicit nearest-integer argument proves unique factorization
   for \(t^2=-2\). Factoring 2,3,11,17 supplies seven prime-norm
   generators. Formula (2.1) proves their exact integer ideal
   membership; the modular factors of \(a^2+2b^2\) over each
   rational prime identify the union of their ideals with the
   complement of the norm-coprime sieve. The checker also tests
   this literal equivalence for every one of \(1122^2\) residues.
2. **All lower periods.** For any principal generator \(g\),
   \(g\mid Q\) forces \(N(g)\mid Q^2\), hence the norm-coprime
   lattice \(V_Q\) survives every principal-ideal sieve with
   common period Q. Since \(V_Q=V_{\mathrm{rad}Q}\), it suffices
   to rule out all squarefree q below 1122. A finite explicitly
   recorded path for each of 682 q consists entirely of points
   with gcd(N,q)=1 and has endpoint shifted by a **nonzero**
   multiple of q. Translating and concatenating it proves an
   infinite component. Independent checker verifies **every**
   step and the exhaustive index set, not just one solver verdict.
3. **Successful period 1122.** An explicit integer-point partition
   provides 6,688 connected sets, total cardinality 204,800, all
   residues modulo 1122 unique, with every allowed 14-neighbor
   inside its own set. The independent checker enumerates **all
   1,258,884** quotient residues and verifies literal neighbor
   closure and connectedness. The written periodic-lift lemma
   proves these local finite predicates certify **every** infinite
   allowed component, with largest size 2,283.
4. **Prime exceptional handling.** Every irreducible outside V1122
   is associate to one of seven listed prime elements (14 signs).
   A 92-point integer closure is verified reachable from those
   exceptions and closed under all permitted overgraph moves;
   norm-bounded exhaustive trial divisibility proves exactly 90
   of those points irreducible, all 90 connected. Other prime
   components live in V1122, giving the global [90,2283] interval.
5. **Radius stability.** The represented positive norms up to
   (but not including) eight are exactly 1,2,3,4,6. Hence all
   conclusions hold over the whole real-radius interval
   \(\sqrt6\le D<\sqrt8\), not just one endpoint.

## Frozen public data

| File | Literal finite evidence |
| --- | --- |
| `code/lower_cycles.json.gz` | 682 explicit q-dependent step-index walks, maximum length 561 |
| `code/positive_q1122.json.gz` | 6,688 exact connected point lists, 204,800 vertices in total |
| `code/exceptional_closure.json` | 92 exact lattice points around all 14 exceptional prime elements |
| `code/check_exact.py` | Independent all-integer verifier; does not call producer |
| `code/self_test.py` | Malformed-data rejection and primality regression |

From this note's directory run:

```sh
python3 code/check_exact.py
python3 -O code/check_exact.py
python3 code/self_test.py
python3 -O code/self_test.py
sha256sum -c SHA256SUMS
```

The checker has explicit `raise ValueError(...)` verification
conditions rather than Python assertions. No commercial solver,
random test, untrusted numeric optimization, floating-point
rounding or analytic continuation is substituted for the proof.

The separate **untrusted production** utilities may be compiled
or run to regenerate witnesses, e.g.:

```sh
g++ -O2 -std=c++17 code/generate_negative.cpp -o /tmp/sqrtm2_gen_neg
/tmp/sqrtm2_gen_neg > /tmp/sqrtm2_lower.json
g++ -O2 -std=c++17 code/generate_positive.cpp -o /tmp/sqrtm2_gen_pos
/tmp/sqrtm2_gen_pos > /tmp/sqrtm2_positive.json
python3 code/generate_exceptional.py
```

For each JSON stream, gzip its raw JSON with a deterministic gzip
implementation to reproduce the semantically identical compressed
witness. The independent checker consumes the **committed** witness
files; it never relies on producers being invoked or trusted.

## Historical work and exact nonclaims

The smaller-step \(D<2\) graph is treated in the earlier
`notes/sqrt-minus-two-sharp-moats/`, and the \(2\le D<\sqrt6\)
sharp phase in `notes/sqrt-minus-two-radius-two/`. Neither older
proof file is overwritten by this note. Prior prime-sieve methods
are attributed to OpenAI/math 028 and the existing 002 research.

The exact periodic sieve component bound 2,283 is **not** asserted
as the exact prime-component maximum; the separate prime graph
bound is only \(90\le B_D\le2283\), with a proved ninety-point
exceptional component. No minimum-generator classification at
period 1122, optimality among nonprincipal blocking approaches,
novelty certification, human peer review or full Lean formalization
is claimed.
