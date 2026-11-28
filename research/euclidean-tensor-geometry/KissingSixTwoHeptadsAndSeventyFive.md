# Single- and double-heptad complement bounds leave two 75-point matching templates

Join two vertices of a spherical $60^\circ$ code by a **strict edge** if their inner product is below $-1/2$. As before put $f(t)=t^4-t^2/4$. The **charge** of a nonempty vertex set $A$ is $q(A)=1/h(A)$, where $h(A)$ is the minimum $f$-energy of a probability measure on $A$. In dimension six $h(A)\ge1/48$. A bare heptad is a connected component of the strict graph that is a chordless seven-cycle; its seven vectors need not possess any geometrical symmetry.

**Single-component theorem.** For any one bare heptad the charges of all other strict components sum to strictly less than $42.929023$, improving the [previous $42.977703$](https://github.com/mxym/math/blob/b6aced61e83a9f6c6b8956aa59f2f53241d96e38/research/euclidean-tensor-geometry/KissingSixHybridCycleComplement.md).

**Two-component theorem.** Select two bare heptads in any six-dimensional kissing code. The combined charges of all strict components **other than these two** sum to **strictly less than $37.918412$**. This concerns reciprocal energies, not the cardinality of the remaining set.

**Application.** A 75-point code in $\mathbb R^6$ without a 36-edge strict matching cannot have any of the three component-size lists $(1,7,7,27,33)$, $(1,7,7,29,31)$ or $(1,7,9,29,29)$. Following the [double-nine exclusion](https://github.com/mxym/math/blob/054956776e97821735ab35e67cf32b7fa74ac0c2/research/euclidean-tensor-geometry/KissingNinePoint160830.md), precisely two lists remain **as necessary alternatives**:
~~~
1,7,11,27,29       1,9,11,27,27
~~~
Thus one isolated vertex, an order-11 component and an order-27 component are all compulsory; the final two sizes are $7+29$ or $9+27$. Nothing in the argument constructs or excludes those two cases. In particular it neither rules out 75 points nor settles the six-dimensional kissing number.

## Why two different thresholds matter

Write $R=37.918412$, $w=4.975124$, and $W=R+2w=47.868660$; all decimals are exact. Suppose that the outside sum is at least $R$. Every heptad has charge at least $w$ by the [previous component charge bounds](https://github.com/mxym/math/blob/70aeadbd0f6859eda06452177fb39cebd763eec1/research/euclidean-tensor-geometry/KissingSixStrictPairCover.md). A probability measure on the entire code has energy at least $1/48$, and different strict components have only nonpositive cross costs. Giving each component mass proportional to its charge therefore proves
\[
 \frac1{h(A)}+\frac1{h(B)}\le48-R
\]
for the two selected heptads. At least one of them, say $A$, has $h(A)\ge2/(48-R)$. Consequently **every** probability vector $p$ on $A$ satisfies
\[
 E_p=\sum p_i p_j f(G_{ij})\ \ge\ 2/(48-R)>0.198377 ,
\]
where $G$ is its ordered heptad Gram matrix. This inference would fail if one selected an arbitrary heptad before the pigeonhole step.

For the *same* $A$, the complement (including $B$) has charge sum at least $R+w$. Scale witness charges in this complement down proportionately to total exactly $R+w$. Applying the [one-cycle mixed inequality](https://github.com/mxym/math/blob/b6aced61e83a9f6c6b8956aa59f2f53241d96e38/research/euclidean-tensor-geometry/KissingSixHybridCycleComplement.md) at $W$ gives
\[
 E_{\rm unif}+J_K(G/7)\ \ge\
 \frac1w+\frac{W^2/48-W}{w^2}>0.195707
\]
for every symmetric seven-by-seven matrix $K$ satisfying
$\sum(b_i^2-b_i^4)\ge b^TKb$ on $[-1,1]^7$. For reference,
\[
 J_K(D)=-\frac{W}{12w}\operatorname{tr}(KD)
 +\tfrac12\operatorname{tr}(KD^2)
 +\frac{\operatorname{tr}(KDKD)-\operatorname{tr}(KD)^2/6}{16(7/20)} .
\]
Scaling keeps each component's original witness valid, as its allowed energy $1/s$ only increases. No monotonicity of a floating-point estimate in $W$ is used.

The exact Gram calculation proves that for every eligible $G$, *at least one* of a finite collection of tests $E_p-0.002670$ and $E_{\rm unif}+J_K(G/7)$ is at most $0.195707$. Both kinds would be strictly larger than that under the two displayed lower bounds. This contradiction proves the theorem. Applying the same lower threshold to the unshifted $E_p$ would be a weaker test and is not what the certificate checks.

The [earlier structural result](https://github.com/mxym/math/blob/a4d6e341ec4acce491ae63044fad65cd372dedd5/research/euclidean-tensor-geometry/KissingSixNoncycleSevenComponents.md) ensures that all relevant seven-components are bare. In the second excluded list the other charge sum is at least $1.333333+17.692255+18.892824=37.918412$. In the first list, the previously verified charges give $1.333333+16.540366+20.064010=37.937709>R$.

## The single-heptad calculation

For $R_1=42.929023$ and $W_1=R_1+w=47.904147$, an outside sum at least $R_1$ would force, for the one selected heptad,
\[
 E_p\ge1/(48-R_1)>0.197134,\qquad
 E_{\rm unif}+J_K(G/7)>0.197134 ,
\]
where the mixed expression now uses $W_1$ in place of $W$. The same two inequalities follow exactly as above, except that the first uses the scalar total budget directly, without the two-heptad pigeonhole. The [single-heptad proof-producing replay](verify_kissing_six_single_heptad_42929023.py) shows one of these tests is at most $0.197134$; the original closed run used 26,883 cells, 13,442 integer-dual leaves and maximum depth 23. Its six cube matrices are the same proven witnesses as in the double-heptad test. In the third excluded list the charges outside the seven sum to at least $1.333333+6.211180+2(17.692255)=42.929023$ even using the older nine-point charge.

## Continuous certificates

For the double-heptad result, the [standalone verifier](verify_kissing_six_two_heptads.py) and three consecutive data chunks ([1](kissing-six-two-heptads-cert-1.txt), [2](kissing-six-two-heptads-cert-2.txt), [3](kissing-six-two-heptads-cert-3.txt)) need only standard Python. These chunks contain the complete double-heptad tree; its replay uses no optimizer. For the single-heptad result, the small proof-producing program regenerates the tree with NumPy, SciPy and threadpoolctl, accepting only closed integer-certified leaves. It optionally saves that tree for the same solver-free verifier.

* Six rational cube matrices are verified on all $3^7=2,187$ ternary faces each. Their dihedral orientations give 71 polynomial tests. The verifier independently polarizes their trace formulas and rounds with a guaranteed outward error.
* A closed 21-coordinate Gram box covers every labeled bare cycle in its cyclic order, including all limits. The verifier rebuilds the graph automorphisms, valid coordinate order inequalities, and signed-triangle interval tightening. For every quadratic correction its affine support is checked on the corners of each coordinate rectangle.
* The source tree was discovered with numerical optimization. A leaf stores only nonnegative integer multipliers, explicit mass vectors and Gram directions. The verifier uses the **combined** 21 edge quartics, bounds them by direct Bernstein subdivision, and subtracts the shift only times the sum of the **scalar probability** multipliers. The mixed tests receive no shift. Both children of every split are proved.
* There are 18,067 cells and 9,034 dual leaves, with maximum depth 24. The joined ASCII base64 witness has SHA-256 **614a3d42d0ca89d74d0937bec3f32e645da2fe26e9e681c8350c501b78fdc0c5**. Replay checks this before decoding.

Replay in this directory, in normal (not optimized) Python:
~~~
python3 verify_kissing_six_two_heptads.py
python3 verify_kissing_six_single_heptad_42929023.py single-tree.json
python3 verify_kissing_six_two_heptads.py --single-tree single-tree.json
~~~
The single-tree filename is optional if only the proof-producing check is wanted. The two runs use different masses and targets; a single-tree certificate cannot be used as if it proved the two-heptad bound.
