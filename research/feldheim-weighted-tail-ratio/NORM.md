# Application to the norm question in dimensions at least two

Feldheim and Feldheim already observed in [§1.1, following Conjecture 1](https://arxiv.org/pdf/1609.03004) that the weighted-mean assertion would imply their norm generalization. Here is the reduction, including sign and dimension details. It is a consequence, not an independent new principle.

**Corollary.** Let $n\ge2$, let $\|\cdot\|$ be any real norm on $\mathbb R^n$, fix $a\in(0,\infty)^n$, and let the coordinates of $X$ be independent nonnegative, finite random variables with unbounded individual supports. Then
$$
\limsup_{t\to\infty}\frac{\Pr(\|X\|>t\|a\|)}{\prod_i\Pr(X_i>ta_i)}=\infty.
$$
Although the source prints $n\in\mathbb N$, the ratio is identically one in dimension one. The corollary concerns all nontrivial dimensions only.

Choose a real linear norming functional $L(x)=\sum_i c_i x_i$ of dual norm one with $L(a)=\|a\|>0$. Let $I=\{i:c_i>0\}$, necessarily nonempty. Define $A(t)=\{X_j\le ta_j\text{ for all }j\notin I\}$, of probability tending to one (or identically one if there are no such coordinates), and $E(t)=\{\sum_{i\in I}c_iX_i>t\sum_{i\in I}c_i a_i\}$. These two events are independent. On their intersection, $L(X)>tL(a)$ since each $c_j(X_j-ta_j)$ is nonnegative when $j\notin I$, whence $\|X\|>t\|a\|$.

If $|I|\ge2$, apply the positive-weight result to the independent, unbounded variables $X_i/a_i$ and weights $c_i a_i/\sum_{j\in I}c_j a_j$ to get an infinite limit superior for $\Pr(E(t))/\prod_{i\in I}\Pr(X_i>ta_i)$. The full norm quotient is at least this ratio times $\Pr(A(t))/\prod_{j\notin I}\Pr(X_j>ta_j)$, whose latter factor tends to one for empty complement and to infinity otherwise. If $|I|=1$, the positive-coordinate ratio equals one, but the complement is nonempty since $n\ge2$, so the second factor tends to infinity. This proves the corollary without a sign restriction on the supporting functional.
