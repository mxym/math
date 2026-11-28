# A seven-point component of a 75-point strict-pair obstruction cannot be even nearly cyclic

**Theorem.** Let $C$ be a six-dimensional kissing code with 75 points and no matching of 36 pairs of inner product below $-1/2$. If a connected component of its strict-pair graph has seven vertices, put those vertices in **any** cyclic order and form their Gram matrix $G$. Let $\overline G$ be its average over simultaneous cyclic shifts of rows and columns. Then
\[
                  \frac1{7}\|G-\overline G\|_{\rm F}>\frac1{225}.
\]
The left side is the root-mean-square difference of all 49 entries. In particular no such seven-point component is geometrically point-transitive, even if the rest of the code breaks all its symmetries. Indeed, a finite transitive permutation group on seven letters contains a 7-cycle; an isometry realizing that cycle makes the component Gram matrix circulant. A combinatorial 7-cycle with noncirculant inner products is **not** excluded.

**Its strict graph is one of six explicit graphs.** One is the theta graph with three internally disjoint paths of lengths 2, 3, 3 between two vertices. The other five have a 7-cycle labelled 0 through 6 and one of these chord sets: none; $03$; $03,25$; $04,15$; or $04,25,36$. Here $ij$ denotes a chord, not a required metric equality. The geometric asymmetry restriction applies to all six.

Eight of the [ten possible size lists](https://github.com/mxym/math/blob/5c34aa6bc59244f3ed2a33ea1b224ae6d5b7b2a0/research/euclidean-tensor-geometry/KissingSixSeventyFiveExtension.md) contain seven. This result restricts their *geometry* and removes no entire size list by itself. Neither 75 nor 76 points are ruled out. The new step is to charge the quartic interaction between a small component and all outside points rather than replace it with zero.

## 1. An anisotropic charge inequality

Use $f(t)=t^4-t^2/4$. Charges are in ordinary units, i.e. the earlier integer charges divided by $10^6$. Distinct components have absolute mutual inner products at most $1/2$. For each component other than the selected seven use a probability measure of energy $\iint f(x\cdot y)\le1/w_i$ supplied by the [charge bounds](https://github.com/mxym/math/blob/70aeadbd0f6859eda06452177fb39cebd763eec1/research/euclidean-tensor-geometry/KissingSixStrictPairCover.md) and their linked order-27 improvement. Give these measures mass $w_i/W$; give the seven-point component its **uniform** measure with mass $m=w/W$, where $w=4.975124$ and $W=\sum w_i$ includes $w$. The eight relevant lists give $W\ge W_0=47.868660$. Write $E=49^{-1}\sum_{ij} f(G_{ij})$, and let $X$ be the $6\times7$ matrix of the selected columns, $B=G/7$, $U=XX^T/7$. Write $M$ for the second-moment matrix of the whole probability measure.

Let $K$ be a symmetric matrix satisfying
\[
 \sum_{i=1}^7(b_i^2-b_i^4)\ \ge b^TKb\qquad(b\in[-1,1]^7).
 \tag{1}
\]
Either $K=0$ or the explicit circulant below will be used. Set $J=XKX^T/7$. For an outside point $y$ insert $b=2X^Ty$ into (1). This bounds the component-to-outside contribution in both directions by $-(m/2)\operatorname{tr}J(M-mU)$. Interactions among different outside components are nonpositive and may be discarded. The within-component upper bounds now give
\[
 E_{\rm all}\le 1/W-m^2(1/w-E)-(m/2)\operatorname{tr}J(M-mU).
\]
On the other hand degree-four harmonic positivity gives
\[
 E_{\rm all}\ge 1/48+c\|M-I/6\|_{\rm F}^2,\qquad c=7/20.
\]
Indeed $t^4-(3/5)t^2+3/80$ is a positive multiple of the normalized degree-four zonal on $S^5$; subtract it from $f$ and use $\iint(x\cdot y)^2=\operatorname{tr} M^2$. Completing the square in the trace-free matrix $M-I/6$ gives the necessary condition
\[
\begin{split}
 \Phi_K(W,B):={}&W^2/48-W+w^2(1/w-E)
 +wW\,\operatorname{tr}(KB)/12\\
 &-\tfrac{w^2}{2}\operatorname{tr}(KB^2)
 -\tfrac{w^2}{16c}\big[\operatorname{tr}(KBKB)-(\operatorname{tr}(KB))^2/6\big]
 \ \le 0. \tag{2}
\end{split}
\]
Here $E$ is computed from $7B$. For both choices of $K$, the derivative with respect to $W$ is at least $W_0/24-1-2.1w/12>0$, since $B\succeq0$ has trace one and $\lambda_{\min}(K)>-2.1$. It suffices to violate (2) at $W_0$.

**Proof of the graph list.** Four mutually nonadjacent vertices in this component would have uniform energy at most $3/16$ (the only positive terms needed are the diagonals). Replacing its charge by $16/3$ would increase the total to at least $47.868660-4.975124+16/3>48$, violating the basic scalar charge bound. Thus the component has independence number at most three. It is triangle-free because three strict negative products make the squared norm of the sum negative, and it is factor-critical by the predecessor theorem. The [graph checker](verify-kissing-six-seven-component-graphs.js) scans all $2^{21}$ edge subsets, tests all 35 triples and all 35 independent-four candidates, and recursively tests a perfect matching after each vertex deletion. It identifies duplicates only under explicit permutations and tests for a spanning cycle and prints its extra chords when present. There are 8,550 labelled survivors in the six listed isomorphism classes.

## 2. An exact quartic inequality on the entire seven-cube

Use the symmetric circulant $K$ with diagonal and successive offsets 1, 2 and 3 equal to
\[
             10^{-6}(-597788,-398531,93327,479339).
\]
The [checker](verify_kissing_six_seven_component_asymmetry.py) proves (1) by 2,187 rational Schur-complement tests. Here is why they are exhaustive. Take a global minimizer of the difference in (1). For each coordinate strictly between $-1$ and $1$, nonnegative second derivative forces $b_i^2\le(1-K_{ii})/6<3/10$. Put these coordinates in $S$, leave the boundary signs in $e\in\{-1,0,1\}^7$ with zeros on $S$, and denote the interior vector by $z$. Its quartic deficiency is at least $(7/10)\|z\|^2$; the boundary deficiency is zero. Put $A=(7/10)I-K_{SS}$ and $h=(Ke)_S$. The exact checker proves for every $e$ that $A$ is positive definite (vacuously for $S=\varnothing$) and
\[
                     e^TKe+h^T A^{-1}h\le0.
\]
Completing the square in $z$ proves the claim. There is no assumption that $K$ itself is positive semidefinite.

## 3. Fourier parameters of the averaged matrix and a perturbation margin

Set $\overline B=\overline G/7$. This circulant PSD matrix of trace one has Fourier masses $a_k\ge0$, $\sum_{k=0}^3a_k=1$, on the four real blocks of dimensions $r=(1,2,2,2)$. We allow the averaged matrix to have **rank seven**, even though $G$ does not. Its three lag products are $g_j=\sum_k a_k\cos(2\pi jk/7)$ and are at most $1/2$. If none is below $-1/2$, its quartic energy is at most $3/28$, yielding $\Phi_0(W_0,\overline B)>1/300$. Otherwise, reindex the cyclic order by a generator so a strict lag has index one; this gives the same cyclic average up to permutation and leaves its distance from $G$ unchanged. Choose $K$ in that ordering.

Let $\lambda_k$ denote the circulant eigenvalues of $K$. In (2) at $\overline B$, the three matrix traces become $\sum\lambda_k a_k$, $\sum\lambda_k a_k^2/r_k$, and $\sum\lambda_k^2a_k^2/r_k$ respectively. Also $E=(3/4+2\sum_{j=1}^3 f(g_j))/7$. Over the **entire** tetrahedron of admissible masses, the checker proves
\[
       \max\{\Phi_0(W_0,\overline B),\Phi_K(W_0,\overline B)\}>1/300 .
\]
It encloses $2\cos(2\pi/7)$ by consecutive rationals of denominator $10^{12}$ using $t^3+t^2-2t-1=0$, then uses exact interval arithmetic on the three independent masses. It visits 591 dyadic cells with maximum depth 48; no solver or floating-point calculation is needed in the proof.

Finally set $D=B-\overline B$. The cyclic average of $D$ is zero, so $\operatorname{tr}(KD)=0$ and the mixed linear terms in the two quadratic traces vanish. The changes in $\operatorname{tr}(KB^2)$ and $\operatorname{tr}(KBKB)$ are $\operatorname{tr}(KD^2)\le .03\|D\|_{\rm F}^2$ and $\operatorname{tr}(KDKD)\le(2.1)^2\|D\|_{\rm F}^2$, using the certified eigenvalue enclosure $-2.1<\lambda_k<.03$. In each lag the first derivative term for $f$ also cancels; on $[-1,1]$ we have $f''\le23/2$. Taylor's inequality gives $E(G)\le E(\overline G)+(23/4)\|D\|_{\rm F}^2$, with both energies normalized by 49. Thus for either chosen test,
\[
       \Phi(W_0,B)\ \ge\ \Phi(W_0,\overline B)-163\|D\|_{\rm F}^2 .
\]
The checker verifies the rational constant and $163/225^2<1/300$. If $\|D\|_{\rm F}\le1/225$, the winning test contradicts (2). This proves the claimed strict separation for every cyclic order.

**Replay:** `python3 verify_kissing_six_seven_component_asymmetry.py` (standard Python 3.9+) and `node verify-kissing-six-seven-component-graphs.js` (standard Node). This is a conditional obstruction, distinct from [Anstreicher's exact antipodal classifications](https://optimization-online.org/wp-content/uploads/2001/01/248.pdf); it gives neither a new unconditional kissing-number upper bound nor an example of the hypothetical 75-point code.
