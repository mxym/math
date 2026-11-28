# Exact character-conjugation correction for KeyBreak Eq. (C.46)

This note audits one finite Fourier identity in the public manuscript
**“Provable Integer Factorization via Multilevel Descent: Approaching Heuristic Bounds”**
(The KeyBreak Cryptanalysis Agent, 26 November 2026), Eq. (C.46).

## Result

With
\[
\mathcal V_{j,\delta}(\chi)=
\sum_{\substack{m\in I_j/\delta\\(m,K/\delta)=1}}
v_j(\delta m)\chi(m),
\]
the manuscript prints a summand proportional to
\[
\overline{\chi(\ell)}
\mathcal V_{1,\delta}(\chi)
\mathcal V_{2,\delta}(\chi).
\]
That expression detects a **product** congruence, not the stated ratio congruence.
The exact correction is
\[
\overline{\chi(\ell)}
\mathcal V_{1,\delta}(\chi)
\mathcal V_{2,\delta}(\overline\chi).
\]
When \(v_2\) is real-valued, the last factor is
\(\overline{\mathcal V_{2,\delta}(\chi)}\).

A four-character counterexample is given in `PROOF.md` and replayed exactly by
`verify_c46.py`.

## Scope

This is a local proof repair, not a factorization algorithm and not a
refutation of the paper's main factoring theorem. In the immediately
subsequent use, the tested functions are real and the estimates take absolute
values and apply Cauchy–Schwarz. Replacing the second transform by its
conjugate preserves its magnitude and character \(L^2\) energy, so those local
bounds keep the same constants. Any downstream step that retains phases would
need its own check.

The finite identity, counterexample, and repair were independently rederived
by a second non-author reviewer. No implementation, real modulus, key, or
cryptographic target is involved.
