# How much can sit outside an asymmetric seven-cycle in a six-dimensional kissing code?

A **strict edge** in a spherical $60^\circ$ code joins two unit vectors with inner product below $-1/2$. Let $f(t)=t^4-t^2/4$. For any nonempty block $H$, define its charge by
\[
q(H)=1/\min_{p\ge0,\,\sum p_i=1}\sum_{i,j\in H}p_ip_j f(x_i\cdot x_j).
\]
In dimension six the denominator is at least $1/48$, by fourth-degree harmonic positivity. Charges are not vertex counts.

**Complement theorem.** Suppose a strict connected component of a six-dimensional kissing code is a chordless seven-cycle. There is no metric symmetry assumption on its seven vectors. Then the sum of the charges of **all the other strict components** is strictly less than $42.977703$.

**Application at 75 points.** If there are not 36 disjoint strict edges in a 75-point code, the component lists $(1,7,9,27,31)$ and $(1,7,13,27,27)$ are impossible. Of the [previous eight lists](https://github.com/mxym/math/blob/a4d6e341ec4acce491ae63044fad65cd372dedd5/research/euclidean-tensor-geometry/KissingSixNoncycleSevenComponents.md), six remain:
~~~
1,7,7,27,33    1,7,7,29,31    1,7,9,29,29
1,7,11,27,29   1,9,9,27,29    1,9,11,27,27
~~~
This proves neither the existence nor the impossibility of a 75-point code. It does not yet guarantee a 36-edge matching in every such code, or improve the six-dimensional kissing-number upper bound.

## The two tests on the same Gram matrix

Suppose the outside charge sum is at least $S=42.977703$. Scale the outside component charges down proportionately so that their new sum is **exactly** $S$. A minimizing probability on a component with scaled charge $s$ still has energy at most $1/s$. Set $w=4.975124$ and $W=S+w=47.952827$. All decimals here denote exact rationals.

First, for **every** probability vector $p$ on the cycle,
\[
 E_p:=\sum p_ip_j f(G_{ij})\ \ge\ 1/(48-S).
\]
Indeed distinct components have nonpositive cross cost, so a weighted combination of their witnessing probabilities gives the scalar bound $\sum q(H)\le48$. Apply it to the selected block and the scaled outside charges.

Second, put $B=G/7$ and $E=49^{-1}\sum f(G_{ij})$. Every symmetric $K$ satisfying
$\sum_i(b_i^2-b_i^4)\ge b^TKb$ on $[-1,1]^7$ gives
\[
 E+J_K(B)\ \ge\ 1/w+(W^2/48-W)/w^2,
\]
where
\[
 J_K(B)=-\frac{W}{12w}\operatorname{tr}(KB)
 +\tfrac12\operatorname{tr}(KB^2)
 +\frac{\operatorname{tr}(KBKB)-(\operatorname{tr}(KB))^2/6}{16c},
 \qquad c=7/20 .
\]
Here one uses the **uniform** measure only for the selected block in the second test. To see the inequality, write $X$ for the six-by-seven column matrix, $U=XX^T/7$, $J=XKX^T/7$, and $m=w/W$. Give the outside components total probabilities $s/W$, and the selected one probability $m$. For an outside point $y$, every coordinate of $2X^Ty$ is in $[-1,1]$. The cube test bounds the two directions of the selected-to-outside interaction by $-(m/2)\operatorname{tr}(J(M-mU))$, where $M$ is the whole second moment. The whole energy is at least $1/48+c\|M-I/6\|_F^2$. Completing the square on the trace-free matrices gives the displayed inequality; the [earlier derivation](https://github.com/mxym/math/blob/3a815c47958df290d042f9e0e9976c5aa2093fbf/research/euclidean-tensor-geometry/KissingSixSevenComponentAsymmetry.md) gives the normalizations explicitly. No claim that $K$ is positive semidefinite is needed.

Both right sides strictly exceed $199095/10^6$: they are respectively $0.1991120795\ldots$ and $0.1990960516\ldots$. The continuous certificate proves that for every eligible $G$ **either** some $E_p$ **or** some $E+J_K$ is at most $199095/10^6$. Neither test is substituted for the other. This is the contradiction. In particular it would not suffice to prove the geometric cycle nontransitive, nor to check just the Fourier parameters of a cyclic Gram matrix.

## How the certificate covers all seven-point configurations

The [frozen tree](kissing-six-hybrid-cycle-cert.json) and [standalone exact verifier](verify_kissing_six_hybrid_cycle.py) use only standard Python. Exploratory LP, numerical eigensolvers and adversarial Gram searches were used to *find* the witnesses, not to accept any leaf.

* Six symmetric rational matrices $K$ are checked on all $3^7=2187$ ternary faces each. At a global minimum of the cube deficiency minus $b^TKb$, an interior coordinate satisfies $b_i^2\le(1-K_{ii})/6$. Therefore on all interior coordinates the deficiency is at least $\alpha\|b_{\rm int}\|^2$, where $\alpha=(5+\min_i K_{ii})/6>0$. For each boundary sign choice, positive exact Schur pivots and completion of the square verify the required inequality. Simultaneous cycle rotations and reversals give 71 different polynomial tests.
* The root box covers all 21 unordered Gram entries: $[-1,-1/2]$ for the seven cycle edges and $[-1/2,1/2]$ for the rest. It includes boundary degeneracies. The verifier reconstructs the graph automorphisms, checks which order inequalities they justify, and tightens the signed spherical triangle inequalities by integer square roots.
* It re-derives $J_K$ by exact polarization of the displayed trace polynomial. Coefficients are rounded down at precision $10^{-9}$ and 253 units are added to the constant, bounding the rounding error for all $|G_{ij}|\le1$. Each mixed quadratic term has its affine upper support verified on the four corners of the appropriate coordinate rectangle, while signed squares use their secant or their tangent. This converts a mixed test into an affine correction to the uniform quartic.
* Each leaf supplies nonnegative integer multipliers on probability tests, mixed tests, order comparisons and $v^TGv\ge0$. After collecting terms, only 21 univariate quartic upper bounds plus a constant remain. Independent degree-four Bernstein subdivision bounds these **combined** edge polynomials directly. Both children of every split are closed. The exact replay visits 2,311 cells with 1,156 terminal witnesses, maximum tree depth 18. It does not use the affine quartic envelopes or floating-point optimizer that generated the witnesses. The computation even permits Gram matrices of rank seven in these interval tests; the six-dimensional harmonic inequality used for actual codes is separate.

## The 75-point arithmetic

All seven-components of the exceptional code are bare cycles by the previous theorem. The charges in the first omitted list outside the selected seven sum to at least $1.333333+6.211180+16.540366+18.892824=42.977703$, including equality at the cutoff. For the second list, a new [order-13 positive-kernel witness](verify-kissing-six-order13-charge.js) gives
\[
13\,\mathbb E_{\rm unif} f(X\cdot Y)\le 7580247959364231/5000000000000000
\]
on any thirteen-point six-dimensional kissing code, by 849 closed or discarded continuous Gram boxes. Thus its charge is at least $8.574917$, and the outside sum is at least $1.333333+8.574917+2(16.540366)=42.988982>42.977703$. Other rounded-down charges come from the [75-point predecessor](https://github.com/mxym/math/blob/5c34aa6bc59244f3ed2a33ea1b224ae6d5b7b2a0/research/euclidean-tensor-geometry/KissingSixSeventyFiveExtension.md) and its fixed sources. [Anstreicher's antipodal classification](https://optimization-online.org/wp-content/uploads/2001/01/248.pdf) concerns a different, globally symmetric setting.

Replay from this directory:
~~~sh
python3 verify_kissing_six_hybrid_cycle.py
node verify-kissing-six-order13-charge.js
~~~
