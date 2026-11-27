# Fixed dimensions 4–7 for ternary Walsh-support cardinalities

For scalar functions `f : F_3^n -> F_3`, every support size from `1` to
`3^n` occurs in each of the dimensions `n=4,5,6,7`, except the six globally
impossible sizes

```
2, 4, 5, 8, 10, 11.
```

This supplements the frozen parent result, which proves those six global
exclusions and the exact classifications in dimensions 1, 2 and 3.  It also
determines the least positive dimension for every attainable size at most
2187, and gives a constructive initial interval in every larger dimension.
See [PROOF.md](PROOF.md) for the exact statements and scope.

`witnesses-fixed.json.gz` contains all 3,216 new truth-table witnesses.  The
gzip stream is deterministic (mtime zero); its decompressed JSON has 5,392,002
bytes and SHA-256
`e9e412fef8bd17fb8b91d8e944b04ec0137dd90ec9157e4c0d00509f609b5076`.
`generate.js` regenerates every byte with four fixed searches and refuses a
mismatch.  `verify_fixed.py` independently checks every witness with both
roots of `X^2+X+1` in `F_65521`, and directly checks the three bridge pairs.

Reproduce with Node.js and Python 3:

```sh
sh replay.sh | diff -u RESULTS.txt -
```

The randomized-looking generation is only a deterministic way to locate
explicit tables.  Correctness rests on the frozen tables and exact verifier,
not on a probabilistic inference or an exhaustive search of all functions.
