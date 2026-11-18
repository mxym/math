# Independent review: the 2018 logarithmic conjecture (separate from Conjecture 1)

**PASS.** Independent internal AI check, not external peer review. This review was performed on the source manuscript before its public Markdown formatting. It checks the argument independently by splitting the trace norm into the two determinant-sign cases.

The [original paper, Conjecture 2, p. 1177; Theorem 3, p. 1180](https://files.ele-math.com/articles/mia-21-81.pdf) places log A on the right of BA^(1−t) on the proposed smaller side and immediately left of B in A^t(log A)B on the larger side. It takes A positive definite, spectrum in [exp(−1),1] ∪ [exp(1),∞), B Hermitian, and 1/2≤t≤1. There is no requirement that the spectrum meet both branches. Its Hilbert–Schmidt case is proved in the article. At 1/2 the two matrices are adjoints and have equal singular values. The distinct 2017 Liu–Wang–Sun conjecture has a four-matrix product and no logarithm; the trureturing mixed-power counterexample is to 2018 Conjecture 1 only. No earlier settlement of this particular logarithmic claim was identified in the checked sources; priority is not certified.

With A=diag(1,exp(−1)) all functional-calculus factors are diagonal. Writing α=exp(−t), β=exp(t−1), x=(β−α)^(−1/2), one gets 0<α<β<1, x>1, and B positive definite. Entrywise, L has rows (x,1−β),(α,−(β−α)x); R has rows (x,β),(1−α,(β−α)x). The determinants are −1−α(1−β)<0, 1−β(1−α)>0. As an independent calculation, for X with entries a,b,c,d the squared trace norm is (a+d)²+(b−c)² if its determinant is nonnegative and (a−d)²+(b+c)² if it is nonpositive. The first square is identical for R in the positive branch and L in the negative branch, namely x²(1+β−α)². Subtracting the remaining squares gives

    (α+β−1)² − (α−β+1)² = 4α(β−1) < 0.

Thus every fixed 1/2<t<1 strictly reverses the proposed direction with a two-by-two real positive definite pair. At t=1 the displayed gap becomes zero, not a counterexample. For any fixed t and the resulting B, replacing the two log eigenvalues 0,−1 by −ε,−1+ε gives a valid strict-interior spectrum for sufficiently small ε>0 by continuity. This needs no uniform ε or B over the range of t.
