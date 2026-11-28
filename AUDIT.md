# Independent proof audit and provenance

## Frozen object

This release candidate copies the mathematical manuscript and finite replay from the unified research-tree commit `6ba62a486a30228586da4987093d20a4d06fba7f`, directory
`research/euclidean-tensor-geometry/theoretical-cryptography/abundant-roughness-critical-endpoint/`. The files `PROOF.md`, `README.md`, `RESULTS.txt`, `UPSTREAM.md`, and `verify_finite.py` are byte-for-byte copies of that audited object.

- Research authoring: AI-assisted mathematical research under the repository steward `mxym`
- Independent proof review: a separate author-external OpenAI research worker
- Repository and release steward: `mxym`
- Audit date: 2026-11-28
- Audit verdict: **PASS**, with no outstanding mathematical correction.

The two workers were separate. The reviewer did not author the proof and did not push or modify the audited result. The release steward is responsible for publication and archival metadata.

## What was checked

The independent audit reconstructed the complete argument rather than relying on the finite checker. In particular it checked:

1. the Chebyshev-cost interpolation and its one-sided derivative behavior at prime knots;
2. the abundance budget inequality, including the square-Euler-factor tail and the uniform (O_A(p^{-1/2}/\log p)) comparison between (B_p) and (p^2);
3. the global-maximum/contact argument, including exclusion of knots, the displacement (delta=O(vz+1/p)), uniformity for (C\geq1), and use of only the ordinary prime number theorem;
4. transfer of the Diamond--Pintz negative oscillation from a real `x` to the next-prime left limit `M(p-)`;
5. the exact scope and page locations in Shunia, Eriksson, and Diamond--Pintz recorded in `UPSTREAM.md`; and
6. the raw finite replay output recorded in `RESULTS.txt`.

A final clarification `0<z<-f(v)=o(1)`, hence `vz=o(1)` at contact points, was included before the frozen audit. The AIRR direct-PDF link was also corrected before freezing.

## Exact scope

The audited theorem is an unconditional **arithmetic existence theorem** for infinitely many odd squarefree abundant consecutive-prime products at the critical roughness constant. It does not prove an abundance-oracle reduction at `c=1`, an effective first-witness bound, or a general integer-factorization algorithm. The finite replay verifies identities and one tiny witness only; it is not a numerical proof of the asymptotic theorem.

## Replay

On a POSIX-like system with Python 3 and GNU-compatible `sha256sum`:

```sh
./replay.sh
```

The replay first verifies every listed byte digest, then requires the checker output to equal the first PASS line in `RESULTS.txt`.
