# Complete seven-generator rigidity at the sharp norm-six period

Research note, 8 October 2026. [Complete written proof](paper.md) ·
[exact obstruction paths](code/obstructions.json) ·
[independent integer checker](code/check.py) ·
[replay evidence](results/replay.txt) · [audit and scope](AUDIT.md).

The predecessor [sharp norm-six period theorem](../sqrt-minus-two-sqrt6-period/README.md)
proved that every successful principal-ideal sieve for the fourteen
Euclidean steps in `Z[sqrt(-2)]` must have scalar period at least
`1122`, and exhibited one seven-generator successful sieve.
This continuation resolves its open **optimal-period generator
classification**, not just another finite experimental example.

Let `t=sqrt(-2)`. At the optimal scalar period `1122`, a finite
principal-ideal list is successful **if and only if its list of
ideals contains each one** of:

```text
(t), (1+t), (1-t), (3+t), (3-t), (3+2t), (3-2t).
```

This is an unconditional classification within the principal-sieve
framework: arbitrary composite nonzero nonunit generators and any
number of redundant generators are permitted. Consequently **seven
is the exact least generator count**, and the only successful
seven-generator list at optimal period is the displayed list, up to
units and ordering.

The proof introduces a **general saturated-prime rigidity lemma for
unique-factorization domains**. It reduces the infinite family of
possible composite generators to seven maximal omitted-prime
sieves, including the special ramified square `(t²)` case.
Eight explicit integer nonzero-voltage paths rule them out.
Their lengths are `624, 567, 567, 669, 669, 759, 759, 854`.

## Independent reproduction

From this note's directory:

```sh
python3 code/check.py
python3 -O code/check.py
python3 code/self_test.py
python3 -O code/self_test.py
sha256sum -c SHA256SUMS
```

No network, external solver or floating point is required.
`code/check.py` never imports the untrusted `code/generate.py`,
and checks actual exact ideal divisibility at **each step** of all
eight paths, nonzero period displacement, complete omission-case
coverage, and the factorization of `1122` into the seven primes
with the ramified factor repeated. A fresh generator replay
reproduced the identical certificate-file SHA256. Deliberate
certificate mutations are rejected even under optimized Python.

## Provenance and limitations

The positive optimal-period existence theorem and the universal
lower-period theorem are imported **from the already published
complete proof and independent checker** in the predecessor note,
not treated as numerical assumptions. The present note proves and
certifies precisely the remaining **minimal-generator rigidity**.
The quadratic prime-sieve methodology has roots in OpenAI/math
family 028 and mxym/math entry 002, cited and distinguished in
[the paper](paper.md).

We do not claim a world-first result, external referee review,
Lean formalization, or the exact maximum prime-component size
at the norm-six step threshold. Historical manuscript sources
are preserved as separate records.
