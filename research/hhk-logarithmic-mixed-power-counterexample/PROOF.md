# A counterexample in dimension two

## The conjecture

In [Hayajneh, Hayajneh and Kittaneh, Conjecture 2, p. 1177](https://files.ele-math.com/articles/mia-21-81.pdf), $A$ is a complex positive definite matrix with $\sigma(A)\subseteq[e^{-1},1]\cup[e,\infty)$, $B$ is Hermitian, and $1/2\le t\le1$. Set
$$L=A^tB+BA^{1-t}\log A,\qquad R=A^t(\log A)B+BA^{1-t}.$$
Powers and the natural logarithm are taken by spectral calculus. The conjecture asks whether $N(L)\le N(R)$ for every unitarily invariant norm (invariant under independent unitary multiplication on the left and right). The original paper proves this for the Hilbert–Schmidt norm in Theorem 3, p. 1180. The assertion here concerns the sum of singular values, not their squared sum.

## Counterexample

**Proposition.** For each $1/2<t<1$, there are real symmetric positive definite $2\times2$ matrices $A,B$ satisfying the spectral restriction for which $\|L\|_1>\|R\|_1$.

**Proof.** Take $A=\operatorname{diag}(1,e^{-1})$ and put
$$\alpha=e^{-t},\qquad \beta=e^{t-1},\qquad x=(\beta-\alpha)^{-1/2},\qquad B=\begin{pmatrix}x&1\\1&x\end{pmatrix}.$$
Since $0<\alpha<\beta<1$, we have $0<\beta-\alpha<1$ and $x>1$. Thus the eigenvalues $x\pm1$ of $B$ are positive. Both eigenvalues of $A$ lie in the permitted first interval; the conjecture does not require an eigenvalue in the second interval.

Now $A^t=\operatorname{diag}(1,\alpha)$, $A^{1-t}=\operatorname{diag}(1,\beta)$ and $\log A=\operatorname{diag}(0,-1)$. Multiplying in the specified order gives
$$L=\begin{pmatrix}x&1-\beta\\ \alpha&(\alpha-\beta)x\end{pmatrix},
\qquad R=\begin{pmatrix}x&\beta\\1-\alpha&(\beta-\alpha)x\end{pmatrix}.$$
The diagonal contributions to $\|R\|_{\rm HS}^2-\|L\|_{\rm HS}^2$ cancel. The off-diagonal terms give
$$\beta^2+(1-\alpha)^2-(1-\beta)^2-\alpha^2=2(\beta-\alpha)>0.$$
In particular, the predicted Hilbert–Schmidt inequality holds for this very pair. But $(\beta-\alpha)x^2=1$ gives oppositely signed determinants:
$$\det L=-1-\alpha(1-\beta)<0,\qquad \det R=1-\beta(1-\alpha)>0.$$
If a $2\times2$ matrix $X$ has singular values $s_1,s_2$, then $s_1s_2=|\det X|$. Consequently $\|X\|_1^2=(s_1+s_2)^2=\|X\|_{\rm HS}^2+2|\det X|$. Since $|\det R|-|\det L|=-\alpha-\beta+2\alpha\beta$, substitution yields
$$\|R\|_1^2-\|L\|_1^2
=2(\beta-\alpha)+2(-\alpha-\beta+2\alpha\beta)
=4\alpha(\beta-1)<0.$$
This is the strict reverse of the conjecture. In particular, $t=3/4$ gives $\alpha=e^{-3/4},\ \beta=e^{-1/4}$ and the explicit example in the [summary](README.md). $\square$

**Endpoints and scope.** At $t=1/2$, $R=L^*$ for all the allowed matrices, so equality holds for every unitarily invariant norm. At $t=1$ this construction is defined with $\beta=1$ and its trace-norm gap is zero; that does not settle the endpoint for other pairs. The claim is about the trace norm only, not a classification of norms or exponents. For fixed interior $t$ one may replace $A$ by $\operatorname{diag}(e^{-\varepsilon},e^{-1+\varepsilon})$ and keep $B$ fixed. All entries and the norm gap vary continuously, so strict reversal persists for sufficiently small $0<\varepsilon<1/2$, with both eigenvalues strictly inside the first interval. No common $B$ or common perturbation size across all $t$ is needed.
