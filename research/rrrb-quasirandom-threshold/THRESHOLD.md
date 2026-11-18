# The sharp quasirandom threshold

Let $W$ be a symmetric graphon with values in $[0,1]$ and red-edge density $p=\int W$. Write $F(W)$ for the probability that four independent labels have the three consecutive red pairs $12,23,34$ and the blue pair $41$. For the constant graphon this is $f(p)=p^3(1-p)$. In finite simple graphs there are exactly two such ordered injections for each undirected RRRB-cycle, one for each direction of traversal with the unique blue edge placed last. Diagonals are free.

Let $T$ be the self-adjoint integral operator with kernel $W$, on real $L^2[0,1]$, and let $e=1$ be the unit constant function. Expanding the blue factor $1-W$ gives
$$
F(W)=\langle e,T^3 e\rangle-\operatorname{tr}(T^4).
$$
The first term counts a red path of length three, the second a red four-cycle. The formula also follows directly by integrating the four entries.

## A scalar bound

In the decomposition $\mathbb Re\oplus e^\perp$, write $T=\left(\begin{smallmatrix}p&u^*\\u&A\end{smallmatrix}\right)$ and set $q=\lVert u\rVert^2$. Squaring gives diagonal blocks $p^2+q$ and $uu^*+A^2$ and lower off-diagonal block $pu+Au$. Thus
$$
\begin{aligned}
\langle e,T^3e\rangle&=p^3+2pq+\langle u,Au\rangle,\\
\operatorname{tr}(T^4)&=p^4+4p^2q+4p\langle u,Au\rangle+4\lVert Au\rVert^2+2q^2+\operatorname{tr}(A^4).
\end{aligned}
$$
The second identity is $\lVert T^2\rVert_{HS}^2$; all terms exist since $T,A$ are Hilbert–Schmidt. If $q=0$ the excess $F-f=-\operatorname{tr}(A^4)$ is nonpositive, vanishing exactly when $A=0$.

If $q>0$, set $\lambda=\langle u,Au\rangle/q$, $x=4p-1$ and $a=(1-x^2)/4=2p-4p^2$. Since $\lVert Au\rVert^2\ge q\lambda^2$ and $\operatorname{tr}(A^4)\ge\lVert A\rVert_{op}^4\ge\lambda^4$,
$$
F-f\le q(a-x\lambda-4\lambda^2)-2q^2-\lambda^4. \tag{1}
$$
This relaxation has an exact realization whenever the following kernel is admissible. Take $s(v)=\pm1$ on two equal halves and set
$$
W(v,w)=p+\sqrt q\,[s(v)+s(w)]+\lambda s(v)s(w). \tag{2}
$$
It has mean $p$, $u=\sqrt q\,s$ and $A=\lambda ss^*$, so equality holds in (1). Its three block values are $p+\lambda\pm2\sqrt q$ and $p-\lambda$. We verify feasibility separately wherever we use this formula.

## Threshold and its endpoint

Put $c=4+2\sqrt2$. The arithmetic-geometric mean inequality gives $2q^2+\lambda^4\ge2\sqrt2\,q\lambda^2$. Completing the square in $\lambda$ now gives
$$
F-f\le q(a-x\lambda-c\lambda^2)\le \frac q4[1-(1-1/c)x^2]. \tag{3}
$$
Since $c/(c-1)=4-2\sqrt2$, the right side is nonpositive when $p\ge p_*=(1+\sqrt{4-2\sqrt2})/4$, strictly negative for $p>p_*$ if $q>0$. The constant graphon therefore maximizes for $p\ge p_*$ and is the unique maximizing graphon for $p>p_*$.

For $0<p<1/2$ take $\lambda=0$ and choose $q>0$ so small that $2q<a$ and $2\sqrt q\le\min(p,1-p)$. Then (2) is admissible and its excess is $q(a-2q)>0$.

For $1/2\le p\le p_*$ take $\lambda=-x/(2c)$ and $q=\lambda^2/\sqrt2$. Both inequalities in (3) are equalities. As $p_*<9/16$, $x<5/4$ and $c>6$, we have $|\lambda|<5/48$ and $\sqrt q<|\lambda|$. Every block of (2) belongs to $[p-3|\lambda|,p+3|\lambda|]\subset(0,1)$. Thus this construction strictly improves the random value for $p<p_*$ in this range. At $p=p_*$ the excess is zero and $q>0$: the degree function takes the distinct values $p\pm\sqrt q$. This gives both a constant and a nonconstant maximizer at the endpoint. For $p=0$ or $1$ the graphon is forced by its edge density.

## Stability and finite graph interpretation

For fixed $p>p_*$ put $\kappa=((1-1/c)x^2-1)/4>0$. If $F\ge f(p)-\epsilon$, (3) gives $q\le\epsilon/\kappa$, including $q=0$. Since $\lVert A\rVert_{op}\le\lVert T\rVert_{op}\le1$, the block identities above give $\operatorname{tr}(A^4)\le\epsilon+(|a|+|x|)q$. It follows that
$$
\lVert T-pee^*\rVert_{op}\le\sqrt q+[\epsilon+(|a|+|x|)q]^{1/4}.
$$
This controls the cut norm by testing indicators against the operator. If the actual edge densities tend to $p>p_*$, the associated $\kappa$ stays bounded away from zero, giving quasirandomness of all asymptotic maximizers.

The step graphon of an $n$-vertex graph changes its unordered red density by $O(1/n)$ and its labelled injection count divided by $n^4$ by $O(1/n)$, since repeated labels are the only possible counting discrepancy. If the step graphon has density $p_n\to p$, mixing it with the zero or the one kernel to reach exactly $p$ changes it in $L^1$ by $|p_n-p|$. Telescoping the four bounded factors changes $F$ by at most $4|p_n-p|$. Thus upper bounds stated at a fixed $p$ apply to convergent-density sequences as well. For the reverse direction, sample the displayed two-class graphs with class sizes rounded and with independent edges of the indicated probabilities. Their expected densities tend to those computed here; variances of normalized counts tend to zero because ordered tuples on disjoint vertex sets are independent. Thus deterministic sequences attaining the limits exist. If exact feasible edge counts are required, recolouring $o(n^2)$ edges costs $o(n^4)$ copies. The statements here concern asymptotic profiles, not exact finite-$n$ extremizers.
