# Sharp two-layer projection spectrum and a certified nesting-depth gap

**Entry-005 continuation, 8 October 2026.**

[Full written proof](paper.md) · [Exact standard-library checker](code/check.py) · [Rational replay](results/check.txt).

Consider affine joins of arbitrary points and simplex products \(B_{p,q}=T_p\times T_q\), with no product taken above a join. The theorem determines **two distinct sharp universal constants** for all positive integer \(p,q\):

- Spectral block optimum \(\sup \log Q(B_{p,q})/(p+q+1)=\log(189/128)/11\), achieved uniquely by \((5,5)\).
- Affine-defect optimum \(\sup\log Q(B_{p,q})/(p+q+1-H(B_{p,q}))=\log(175/128)/4\), achieved uniquely by \((4,4)\).

Consequently, the exact asymptotic projection-volume root growth in this entire **two-layer join-of-products** class is \(e(189/128)^{1/11}\). These are infinite-parameter results: the proof closes the full tails \(p+q\ge16\) and \(p+q\ge40\) analytically, with 56 and 380 finite rational checks respectively.

The same two bounds prove a **strict depth separation already in dimension 85**. Starting from \(T_5\), form \(K_1=(T_5\times T_5)^{*2}\), then \(K_2=(K_1\times K_1)^{*2}\). Its exact \(R(K_2)/c_{85}\) exceeds that of *every* 85-dimensional two-layer body. Repeating it by joins proves the superiority persists at the asymptotic exponential growth level. This is not an exact optimum claim in dimension 85 for the unrestricted point-generated class, and the earliest crossover dimension is unknown.

From repository root:

```sh
python3 notes/two-layer-projection-depth-separation/code/check.py
python3 -O notes/two-layer-projection-depth-separation/code/check.py
```

No numerical optimizer, nonreplayable solver or floating-point inequality is part of the proof. Imported geometry is from 005 v2; the new analytic inequalities, classifications and exact witness comparisons are derived here. AI-assisted research; no priority, external human peer review or complete Lean formalization asserted.
