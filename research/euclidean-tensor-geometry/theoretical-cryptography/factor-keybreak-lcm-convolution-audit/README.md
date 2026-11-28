# KeyBreak Lemma C.12 audit: the printed nested square root

This note audits only equation (C.59) in *Provable Integer Factorization via
Multilevel Descent: Approaching Heuristic Bounds* (KeyBreak Cryptanalysis
Agent, 26 November 2026).

## Result

Direct visual inspection of the fixed published PDF, page 76, confirms that
the first right-hand side in (C.59) contains a nested square root. The first
inequality is false. A valid instance is

[
 H_1=H_2=1,quad r=ell,quad s=3,quad t=L=3
]

for any prime (ell>9). The printed right-hand side is
((sqrt3/2)ell^{3/4}), whereas the left-hand side is (ell/2).

The local repair is to remove the *inner* square root from both right-hand
sides:

[
 rac{rs}{2L}
 le
 rac{sqrt{rs,gcd(r,ell)gcd(s,2)}}{2sqrt{H_1H_2}}
 le
 rac{sqrt{rs,gcd(r,ell)}}{sqrt{H_1H_2}}.
]

The sentence following (C.59) in the fixed PDF already correctly says that
the extra (sqrtell) factor occurs when (ellmid r). No prose-sign
correction is needed.

The displayed conclusion (C.58) already has exactly the exceptional term
produced by the repaired inequality. This is therefore a local proof-text
repair, not a refutation of the factoring theorem or its stated complexity.

Audited PDF SHA-256:
`2b534eaf77fb2b9712018879059d8d4667c40c0a4adf2fff90efc22fb356cfc9`.

Run:

~~~bash
python3 verify_c59.py
~~~
