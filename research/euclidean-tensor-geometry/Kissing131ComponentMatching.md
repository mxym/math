# 62 disjoint strict obtuse pairs at 131 points

**Theorem.** Let \(X\) consist of 131 unit vectors in \(\mathbb R^7\) with \(x\cdot y\le1/2\) for distinct points. At least **62 disjoint pairs** have scalar product **strictly below \(-1/2\)**. At most seven points are unmatched. The previous bound was 61. There is no assumption concerning symmetry, root subconfigurations, or exact antipodes.

This raises a necessary matching count, not the best known upper bound on the seven-dimensional kissing number. It does not assert existence of a 131-point code or sharpness of 62.

## 1. Transferring a three-point certificate between cardinalities

Set \(f(t)=t^4-t^2/4\). Write \(U_q=q^{-1}\sum_{x,y}f(x\cdot y)\) for the uniform energy per point of a \(q\)-point code. A three-point certificate at cardinality \(q\) consists of a nonnegative linear combination \(h\) of the positive-degree normalized dimension-seven Gegenbauer polynomials, a symmetric positive [Bachoc–Vallentin kernel](https://arxiv.org/abs/math/0608426) \(H\), and a rational \(B\) (including any verification slack). Put \(J(t)=H(1,t,t)\). For every feasible triple \((a,b,c)\) of distinct-point inner products the certificate verifies
\[
 (q-2)H(a,b,c)+\tfrac13\sum_{t=a,b,c}
       [f(t)+h(t)+3J(t)]\le B.
\]
Summation over ordered distinct triples, restoring the one- and two-point coincidences and using positivity of the complete kernel sums, yields
\[
                U_q\le 3/4+h(1)+H(1,1,1)+(q-1)B.
\]
Feasibility of a triple is enforced by its \(3\times3\) Gram determinant; all three pair products lie in \([-1,1/2]\).

Here is an alternative to repeating a three-variable search at a new cardinality \(k\ge3\). Take certified source rows indexed by \(i\), with cardinalities \(q_i\), and nonnegative rational coefficients \(x_i\) summing to one. Set \(e_i=(q_i-2)/(k-2)\) and take the new positive kernel \(H'=\sum_i x_i e_i H_i\). Given a new \(h'\) with nonnegative harmonic coefficients, it is enough to check the **univariate** inequality
\[
 B'\ \ge\ h'(t)+\sum_i x_i
       [B_i-h_i(t)-3(1-e_i)J_i(t)]\qquad(-1\le t\le1/2).
\]
Indeed the trivariate term in the target certificate is now exactly the weighted sum of the trivariate source terms. Adding the displayed scalar bound at the three pair entries gives the target inequality. The cardinalities may lie on either side of the target; \(e_i>0\) in both cases. The resulting bound is
\[
       U_k\le 3/4+h'(1)+\sum_i x_i e_i H_i(1,1,1)+(k-1)B'.
\]
This is a sufficient transfer rule, not a claim to optimize all three-point certificates.

The [rational input data](kissing-131-uniform-data.json) include eleven directly certified rows for \(q=35,49,51,53,55,57,59,61,71,75,79\), and two transfers. The transfer from 83 alone gives \(U_{81}\le1.678932\). Mixing the sources 93 and 89 in proportions \(936095485:63904515\) gives \(U_{91}\le1.700327\). The [exact checker](verify-kissing-131-capacity-inputs.js) rechecks the three source rows too, certifies the scalar transfers using rational Bernstein coefficients and dyadic subdivision, and recomputes all 133 rounded reciprocal charges. No SDP optimality or sampling assumption enters the proof.

## 2. From the charges to a matching

Let \(G\) join pairs with product below \(-1/2\). A canonical Tutte–Berge barrier of size \(t\) leaves only odd factor-critical components (deleting any one vertex of such a component leaves a perfect matching). If the matching number were at most 61, their number \(o\) would be at least \(t+9\). There are no triangles, so a nonsingleton factor-critical component has at least five vertices. If \(s\) components are singletons, adding their antipodes to the surviving code gives \(s\le t+1\) by [Tomar's upper bound 132](https://www.mefyi.com/papers/kissing-numbers-five-seven/). See the [canonical barrier proof](https://github.com/mxym/math/blob/c36c642c5f6984e670f9ba2368f4bfafb5b966d7/research/euclidean-tensor-geometry/KissingOddComponentBarriers.md).

Different components have all mutual products in \([-1/2,1/2]\). We apply the [component-measure harmonic inequality](https://github.com/mxym/math/blob/f20e943b43557fb5e837426510844873b5d013dd/research/euclidean-tensor-geometry/KissingCoupledComponentHarmonics.md). It assigns an integer charge \(w_k\) to a size-\(k\) component admitting a probability measure of \(f\)-energy at most \(10^6/w_k\). A uniform row \(U_q\le u\) also gives \(U_k\le3/4+(k-1)(u-3/4)/(q-1)\) for every larger size, by averaging over \(q\)-subsets. The inherited charges are read from the byte-pinned 130-point proof; all new reciprocal charges round down.

The necessary scalar budget \(\sum w_k\le84{,}000{,}000\) still permits **133** partitions. Of these, 109 have \((t,o,s)=(0,9,1)\), 15 have \((0,9,0)\), and nine have \((1,10,2)\). The least charge is **83,820,161**. The [labeled harmonic data](kissing-131-component-data.json) assign 34 reusable rational Gram-factor templates, with explicit type mappings and nonnegative integer rescalings, to these 133 cases. The [replay](verify-kissing-131-component-measures.py) uses the byte-pinned predecessor verifier. It generates the partitions afresh and proves a strictly negative rational upper bound on a sum of positive-semidefinite spherical harmonic energies for every one. Thus none occurs.

## 3. An additional structural consequence at 132

If a 132-point code has no 63 disjoint strict pairs, then its **original** strong graph, without deleting vertices, consists of exactly **eight** connected odd factor-critical components, all of size at least five. In particular there are no exact antipodal pairs in such a configuration. An exact antipodal pair would form a component of order two, since no third code point can have product below \(-1/2\) with either member.

In fact deleting any vertex leaves 131 points and therefore a matching of size 62, already maximum under the assumption. Every vertex is exposable by a maximum matching. In a canonical barrier of size \(t\) and deficiency eight there are \(t+8\) odd components. Each exposed vertex of the barrier would leave at most \(t-1\) of these components matched to the barrier and at least nine unmatched component vertices, contradicting maximum size 62. Hence the barrier is empty. A singleton would allow a 133rd point, its negative. The scalar budget leaves **1,159** candidate size multisets for these eight components with the present inputs. This counts multisets, not realizable configurations, and does not prove a 63rd pair or exclude 132 points.

**Replay from this directory:**
~~~sh
node verify-kissing-131-capacity-inputs.js
python3 verify-kissing-131-component-measures.py
~~~
The new proofs use standard Node and Python libraries only. The two predecessor files needed for replay are retained in this directory, and their hashes are checked before use.
