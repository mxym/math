# A ternary counterexample to a proposed mutual-information continuity bound

**Written proof v1 — 9 October 2026.** This note gives a complete elementary written construction. Lean formalization is incomplete in this version. Novelty and priority are unconfirmed; no external independent review is certified.

## 1. Exact target and scope

Mario Berta, Ludovico Lami and Marco Tomamichel, *Continuity of entropies via integral representations*, [arXiv:2408.15226v2, Eq. (106)](https://arxiv.org/html/2408.15226v2#S4), propose the general mutual-information continuity inequality

$$
\left|I(A:B)_\rho-I(A:B)_\sigma\right|
\le h(\varepsilon)+\varepsilon\log\!\left(\min\{d_A^2,d_B^2\}-1\right)
$$

for nearby bipartite states, where the trace distance is at most a sufficiently small $\varepsilon$. The same proposal appears in [v1, Eq. (54)](https://arxiv.org/html/2408.15226v1#S3.SS3). The surrounding discussion first considers applications with one equal marginal, then proposes this more general inequality without that restriction.

The construction below refutes this **general version with different marginals** at arbitrarily small distances. Both marginals change. It does not resolve the version in which one marginal must remain equal.

All logarithms are natural. Write

$$
h(\varepsilon)=-\varepsilon\log\varepsilon-(1-\varepsilon)\log(1-\varepsilon),
\qquad 0\log0=0.
$$

For a probability vector $p$, let $H(p)=-\sum_i p_i\log p_i$. For a joint probability table $R$, let $R_A$ and $R_B$ be its row and column marginals and set $I(R)=H(R_A)+H(R_B)-H(R)$.

## 2. Construction on a ternary product alphabet

For every $0<\varepsilon\le1/16$, define joint probability tables on $\{0,1,2\}\times\{0,1,2\}$ by

$$
P_\varepsilon=
\begin{pmatrix}
(1-\varepsilon)/2&0&0\\
0&(1-\varepsilon)/2&0\\
0&0&\varepsilon
\end{pmatrix},
\qquad
Q_\varepsilon=
\begin{pmatrix}
(1-\varepsilon)/2&\varepsilon/2&0\\
\varepsilon/2&(1-\varepsilon)/2&0\\
0&0&0
\end{pmatrix}.
$$

Every entry is nonnegative, and each table sums to one. The entries at $(0,0)$ and $(1,1)$ agree. The only nonzero entries of $P_\varepsilon-Q_\varepsilon$ are $+\varepsilon$ at $(2,2)$ and $-\varepsilon/2$ at each of $(0,1)$ and $(1,0)$. Therefore

$$
\operatorname{TV}(P_\varepsilon,Q_\varepsilon)
=\frac12\sum_{i,j}|P_\varepsilon(i,j)-Q_\varepsilon(i,j)|
=\frac12(\varepsilon+\varepsilon/2+\varepsilon/2)
=\varepsilon.
$$

These tables also define diagonal density matrices

$$
\rho_\varepsilon=\sum_{i,j}P_\varepsilon(i,j)|ij\rangle\langle ij|,
\qquad
\sigma_\varepsilon=\sum_{i,j}Q_\varepsilon(i,j)|ij\rangle\langle ij|
$$

on $\mathbb C^3\otimes\mathbb C^3$. Their quantum trace distance equals the total variation distance above, and their von Neumann entropies equal the Shannon entropies of the corresponding diagonal probabilities. Thus the same classical commuting construction is also a quantum counterexample.

## 3. Exact entropies and mutual information

Both marginals of $P_\varepsilon$ are

$$
(P_\varepsilon)_A=(P_\varepsilon)_B=
\left((1-\varepsilon)/2,(1-\varepsilon)/2,\varepsilon\right).
$$

Its joint distribution is supported on the diagonal. Direct expansion gives

$$
H((P_\varepsilon)_A)=H((P_\varepsilon)_B)=H(P_\varepsilon)
=-(1-\varepsilon)\log\frac{1-\varepsilon}{2}-\varepsilon\log\varepsilon
=h(\varepsilon)+(1-\varepsilon)\log2,
$$

and hence

$$
I(P_\varepsilon)=h(\varepsilon)+(1-\varepsilon)\log2.
$$

Both marginals of $Q_\varepsilon$ are $(1/2,1/2,0)$, so each has entropy $\log2$. Its four nonzero joint entries describe a fair binary input followed by binary crossover probability $\varepsilon$. Equivalently, expanding those entries gives

$$
H(Q_\varepsilon)
=-(1-\varepsilon)\log\frac{1-\varepsilon}{2}
-\varepsilon\log\frac{\varepsilon}{2}
=\log2+h(\varepsilon).
$$

Consequently,

$$
I(Q_\varepsilon)=\log2-h(\varepsilon),
\qquad
I(P_\varepsilon)-I(Q_\varepsilon)=2h(\varepsilon)-\varepsilon\log2.
$$

## 4. Strict violation at arbitrarily small distances

Here $d_A=d_B=3$, so the proposed right-hand side is $h(\varepsilon)+\varepsilon\log8$. Subtracting it from the signed mutual-information difference gives

$$
\begin{aligned}
&I(P_\varepsilon)-I(Q_\varepsilon)
-\bigl(h(\varepsilon)+\varepsilon\log8\bigr)\\
&\qquad=h(\varepsilon)-\varepsilon\log16.
\end{aligned}
$$

For $0<\varepsilon\le1/16$, monotonicity of the logarithm gives

$$
-\varepsilon\log\varepsilon\ge\varepsilon\log16.
$$

Also $0<1-\varepsilon<1$, so

$$
-(1-\varepsilon)\log(1-\varepsilon)>0.
$$

Adding these inequalities proves $h(\varepsilon)-\varepsilon\log16>0$. In particular, the signed difference is positive and equals its absolute value. Thus, for **every** $0<\varepsilon\le1/16$,

$$
\boxed{
\left|I(P_\varepsilon)-I(Q_\varepsilon)\right|
>h(\varepsilon)+\varepsilon\log8
}
\qquad\text{while}\qquad
\operatorname{TV}(P_\varepsilon,Q_\varepsilon)=\varepsilon.
$$

There is therefore no positive uniform small-distance neighborhood on which the proposed general inequality holds. Explicitly, given any $\delta>0$, choose $\varepsilon=\min\{\delta/2,1/32\}$; then $0<\varepsilon<\delta$, and this construction still violates the bound.

The exact rational choice $\varepsilon=1/32$ has strictly positive gap

$$
\frac{\log2}{32}-\frac{31}{32}\log\frac{31}{32}>0.
$$

This positivity is symbolic and does not require numerical certification.

## 5. Necessary leading coefficient

The exact loss $2h(\varepsilon)-\varepsilon\log2$ also implies that no modulus of the form $c\,h(\varepsilon)+C\varepsilon$, with finite fixed $C$ and $c<2$, can bound arbitrary ternary mutual-information differences near zero. Indeed,

$$
\frac{h(\varepsilon)}{\varepsilon}\ge-\log\varepsilon\longrightarrow+\infty
\qquad(\varepsilon\downarrow0),
$$

so $(2-c)h(\varepsilon)-\varepsilon(\log2+C)>0$ for sufficiently small positive $\varepsilon$. This is a lower bound on the necessary leading coefficient; it does not establish an exact optimal finite-distance modulus.

## 6. Version status and remaining scope

This v1 publishes the complete written construction. Lean formalization is incomplete and is not included as a verified result. The equal-one-marginal version remains unresolved by this note. Novelty and priority are unconfirmed. No external independent review is certified.

## References

Mario Berta, Ludovico Lami and Marco Tomamichel, *Continuity of entropies via integral representations*, arXiv:2408.15226. Version 2: [Eq. (106), concluding discussion](https://arxiv.org/html/2408.15226v2#S4). Version 1: [Eq. (54), Section III.3](https://arxiv.org/html/2408.15226v1#S3.SS3).
