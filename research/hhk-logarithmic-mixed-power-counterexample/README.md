# A trace-norm counterexample to the logarithmic mixed-power conjecture

For every fixed $1/2<t<1$, two real positive definite $2\times2$ matrices reverse the inequality in [Conjecture 2 of Hayajneh, Hayajneh and Kittaneh (2018), p. 1177](https://files.ele-math.com/articles/mia-21-81.pdf). Write $L=A^tB+BA^{1-t}\log A$ and $R=A^t(\log A)B+BA^{1-t}$. The conjecture predicts $N(L)\le N(R)$ for **every** unitarily invariant norm under a spectral restriction. The trace norm $N(X)=\operatorname{tr}|X|$ fails even when $A$ has both eigenvalues in the permitted interval $[e^{-1},1]$.

For one example take $t=3/4$, $A=\operatorname{diag}(1,e^{-1})$ and $B=\bigl(\begin{smallmatrix}x&1\\1&x\end{smallmatrix}\bigr)$, where $x=(e^{-1/4}-e^{-3/4})^{-1/2}$. The exact squared-norm gap is
$$\|L\|_1^2-\|R\|_1^2=4e^{-3/4}(1-e^{-1/4})>0.$$

The [short proof](PROOF.md) gives the same construction for every interior $t$, with $B$ depending on $t$. At $t=1/2$ the matrices are adjoints. At $t=1$ this family ties; the note does not decide that endpoint. No counterexample for Schatten $p>1$ is asserted. The authors' Hilbert–Schmidt theorem ($p=2$) remains valid. Their separate [nonlogarithmic Conjecture 1](https://github.com/mxym/math/pull/98) is not the result proved here.

**Verification:** the argument is self-contained; see the [independent internal review](REVIEW.md), [primary sources and prior-work check](SOURCES.md) and [recorded checks](CHECKS.txt). To reproduce the algebra, run `python3 verify.py` and `python3 independent.py` in this directory with SymPy installed; run `sha256sum -c SHA256SUMS` to check the file snapshot.

**Status:** AI-assisted research and independent internal AI review, not external peer review or proof-assistant verification. No claim of historical priority.
