# KeyBreak Lemma C.12 audit: the printed gcd square root

This note audits only equation (C.59) and the sentence immediately after it in
*Provable Integer Factorization via Multilevel Descent: Approaching Heuristic Bounds*
(KeyBreak Cryptanalysis Agent, 26 November 2026).

## Result

The first inequality in the printed (C.59) is false. A valid instance is

\[
 H_1=H_2=1,\quad r=\ell,\quad s=3,\quad t=L=3
\]

for any prime \(\ell>9\). The printed right-hand side is
\((\sqrt3/2)\ell^{3/4}\), whereas the left-hand side is \(\ell/2\).

The local repair is to remove the *inner* square root from both right-hand
sides:

\[
 \frac{rs}{2L}
 \le
 \frac{\sqrt{rs\,\gcd(r,\ell)\gcd(s,2)}}{2\sqrt{H_1H_2}}
 \le
 \frac{\sqrt{rs\,\gcd(r,\ell)}}{\sqrt{H_1H_2}}.
\]

The following sentence must correspondingly say that the extra
\(\sqrt\ell\) factor occurs when \(\ell\mid r\), not when
\(\ell\nmid r\).

The displayed conclusion (C.58) already has exactly the exceptional term
produced by the repaired inequality. This is therefore a local proof-text
repair, not a refutation of the factoring theorem or its stated complexity.

Run:

~~~bash
python3 verify_c59.py
~~~
