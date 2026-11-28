# Cogentic descent divisibility-sign audit

This directory isolates one exact internal inconsistency in the fixed v1 of
*Unconditional Integer Factorization in Time* \(L_N[1/3,O(1)]\).

At an algebraic node, Lemma 4.4(1) assumes
\[
q\nmid R_{\rm anc},
\]
and its proof uses that hypothesis. Definition 4.5 instead instructs
`AlgNode` to verify
\[
q\mid |b_{t_1}^*a_{t_2}^*-a_{t_1}^*b_{t_2}^*|
\quad\text{for every ancestor pair.}
\]
For a history containing at least two distinct primitive ancestors, the printed
guard forces \(q\mid R_{\rm anc}\), the exact negation of the local lemma's
hypothesis.

The surrounding construction identifies the intended one-symbol repair:
replace the divisibility guard in Definition 4.5 by nondivisibility for every
ancestor pair. This agrees with the definition of \(Y_{\rm forb}\), the
bad-child event, and the application of Lemma 4.4 in Lemma 4.6.

This is a proof-scope audit. It does **not** claim that the paper's factoring
theorem is false, and it does not independently verify the full paper. It says
that the printed algorithm and the printed path-telescoping proof are
incompatible until the guard is corrected.

Run:

```bash
python3 verify_logic.py
```
