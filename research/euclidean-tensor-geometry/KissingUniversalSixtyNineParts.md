# A 69-part decomposition for seven-dimensional kissing configurations

**Theorem.** Let \(X\) be any finite set of unit vectors in \(\mathbb R^7\) with \(x\cdot y\le 1/2\) for distinct \(x,y\). It admits a partition into **at most 69 parts**, each either a singleton or a pair with scalar product **strictly less than \(-1/2\)**. In particular, a 132-point code would contain **63 disjoint strict pairs**, leaving at most six points unmatched.

The pairs need not be antipodal. No symmetry, root subsystem, or prior pairing of \(X\) is assumed. This neither constructs nor excludes a 132-point code, and 69 is not asserted optimal. A universal bound below 63 would already be impossible by the 126-point \(E_7\) example. For context, [Tomar's cardinality certificate](https://www.mefyi.com/papers/kissing-numbers-five-seven/) gives \(|X|\le132\). [Cohn–Jiao–Kumar–Torquato, Theorem 7.5](https://msp.org/gt/2011/15-4/gt-v15-n4-p11-p.pdf) use partitions with the *weak* inequality \(\le-1/2\) as inputs to a higher-dimensional construction; their construction does not give this universal strict-pair bound.

## From a possible failure at 132 to eight components

Join pairs at scalar product \(<-1/2\) in a graph \(G\), and write \(\nu(G)\) for its maximum matching size. The minimum number of allowed parts is exactly \(|X|-\nu(G)\). Products between distinct components belong to \([-1/2,1/2]\). There are no triangles, by expanding the squared norm of a sum of three vectors.

The [131-point theorem and its structural corollary](https://github.com/mxym/math/blob/42305d0e08cc631e635aba2ff8f20bfa66738bd1/research/euclidean-tensor-geometry/Kissing131ComponentMatching.md) show that if a 132-point code has no 63-matching, its original graph has exactly eight nontrivial odd factor-critical components, without deleting any vertices. Their orders are odd and at least five. Recall the argument: every vertex can be exposed by a maximum 62-matching, using deletion and the 131-point theorem. No vertex in a positive canonical Tutte–Berge barrier can then be exposed. The barrier is empty; a singleton would allow its antipode as a 133rd point.

Let \(P_l\) be the normalized dimension-seven Gegenbauer polynomial and \(f(t)=t^4-t^2/4\). A certified component charge \(w_k\) guarantees a probability measure on the component of order \(k\) with \(f\)-energy at most \(10^6/w_k\). The minimum over all probability weights is called \(C_f\). The uniform measure suffices for the certified sizes \(k\ge11\). Since \(f\le0\) on the cross interval, and the constant harmonic coefficient of \(f\) is \(1/84\) with all positive-degree coefficients nonnegative, weighting components inversely to their cost gives the necessary budget
\[
                       \sum_i w_{k_i}\le84{,}000{,}000 .
\]
The [input table](kissing-132-mixed-inputs.json) starts from the byte-pinned 131-point table. The refinements are \(C_f\le.25095,.2010,.161\) at 5, 7, 9 respectively and five direct uniform rows at orders 31, 33, 37, 81, 91. Charges round **down**. The [nine-point result](https://github.com/mxym/math/blob/0af4adc189728c7d1abe67825746bc5a9c4be53c/research/euclidean-tensor-geometry/KissingNonagonSymmetryBreaking.md) is inherited. For five points an independent triple gives \(C_f\le1/4\); the remaining graph is \(C_5\). For seven the non-cycle classes already have \(C_f\le.20084\) or an independent four-set. The [local replay](verify-kissing-132-local-polynomials.py) tests the two critical cycles with the predecessor quartic verifier. The resulting integer enumeration leaves **275** eight-part multisets, with minimum charge **83,722,101**. We exclude each below.

## Reusing the positive part of a local certificate

A [Bachoc–Vallentin kernel](https://doi.org/10.1090/S0894-0347-07-00589-9) certificate at source size \(s\ge3\) supplies a symmetric polynomial \(H(a,b,c)\), a univariate \(h(t)\) with nonnegative harmonic coefficients, and a rational \(B\). Write \(J(t)=H(1,t,t)\), \(D=H(1,1,1)\). The certified inequality for distinct-point triples is
\[
 (s-2)H(a,b,c)+\tfrac13\sum_{t=a,b,c}[f(t)+h(t)+3J(t)]\ \le B .
\]
The data give its uniform per-point upper bound \(U_s=3/4+h(1)+D+(s-1)B\), with verification slack already included in \(B\). The [source checker](verify-kissing-132-source-charts.js) verifies the full continuous Gram domain, the positive factors, and the exact rational \(U_s\) for all sixteen source rows; \(B\) can equally be recovered from this identity.

For any target size \(q\ge3\), set \(e=(s-2)/(q-2)>0\) and
\[
 p(t)=f(t)+h(t)+3(1-e)J(t),\qquad
 M=[3/4+h(1)+(3-2e)D+(q-1)B]/q.
\]
The source inequality is exactly the target distinct-triple inequality for \(p\) and \(eH\), since \(p+3eJ=f+h+3J\). Summing over all ordered triples and restoring the coincidences yields, for the **uniform** target measure \(\mu\),
\[
                 E_{\mu^2}p+qe E_{\mu^3}H\le M .
\]
Here \(E_{\mu^2}p\) abbreviates the double integral of \(p(x\cdot y)\). This formula transfers both **upward and downward** in cardinality. It makes no claim of an optimal bound at the new size.

The degree-zero anchored block has Chebyshev-factor polynomials \(\phi_j\), read from the first positive Gram factor: before symmetrizing it is \(\sum_j\phi_j(a)\phi_j(b)\) about the common anchor. Averaging over the anchor gives \(\sum_j E_x[(E_y\phi_j(x\cdot y))^2]\). Every higher anchored block has nonnegative average by the addition formula in the orthogonal complement of the anchor (or by continuity at degenerate projections). Jensen therefore gives
\[
      E_{\mu^2}p+qe\sum_j(E_{\mu^2}\phi_j)^2\le M .
\]
Consequently, for every \(\ell>0\) and real vector \(z\),
\[
 E_{\mu^2}\big[\ell p+2qe\,z\cdot\phi\big]
             \ \le\ \ell M+qe\,\|z\|^2/\ell .
\]
These are simultaneous inequalities for the **same uniform target measure**. Their coefficients in the proof data are rational. This retained square, rather than just the transferred scalar charge, is useful in the difficult partitions. To reconstruct \(J\) exactly, let \(A_k(v,w)\) be the factor Gram polynomial in anchored block \(k\). Substituting \((1,t,t)\) in the three cyclic summands gives
\[
       3J(t)=2A_0(1,t)+\sum_{k\ge0}(1-t^2)^k A_k(t,t).
\]
In the first two anchored summands the positive-degree transverse kernel vanishes; in the third it equals \((1-t^2)^k\).

## A second choice of local measure at order seven

Put \(g=(9P_2+17P_4+10P_{10})/48\). For every seven-point code in arbitrary dimension, **\(C_g\le.180\)**, where the masses may be chosen specifically for \(g\). In particular we **do not** require one set of masses to achieve the two bounds for \(f\) and \(g\). The rational scalar replay checks \(g(1)=3/4\), \(g\le-.01\) on \([-1/2,1/2]\), and \(g\ge-.021\) on \([-1,1/2]\). An independent four-set therefore gives \(C_g\le (3/4-3/100)/4=.18\). Otherwise the triangle-free graph belongs to the nine classes of the pinned seven-vertex census. All nine continuous Gram searches pass: **907 boxes** in total.

Here is the new affine bound used for that degree-ten search. Take \(K=4096\), \(A=4K^4\), and a rational upper bound \(M_2\) on \(|g''|\) over \([-1,1/2]\); the sum of the absolute derivative-coefficient bounds suffices. At each integer knot form \(b_z=\lceil A[g(z/K)+M_2/(8K^2)]\rceil\). For a cell \([l/K,u/K]\) and any integer slope \(S\), the line
\[
      \frac{S K t+\max_{l\le z\le u}(b_z-Sz)}{A}
\]
majorizes \(g(t)\) on the entire real cell. Indeed linear interpolation between consecutive knots errs by at most \(M_2/(8K^2)\). Slope optimization merely selects among valid lines. Knot evaluation is rational and the integer array operations have explicit overflow guards. As with the quartic predecessor, numerical LP and eigenvector calculations only propose witnesses; integer dual verification, not a floating objective, closes a Gram box.

## Global combination and universal cover

For any chosen component measures, the matrices \(H^{(l)}_{ij}=E_{\mu_i\mu_j}P_l(x\cdot y)\) are PSD. Test them against the rational positive Gram factors of the [component harmonic method](https://github.com/mxym/math/blob/f20e943b43557fb5e837426510844873b5d013dd/research/euclidean-tensor-geometry/KissingCoupledComponentHarmonics.md). For different components bound the resulting polynomial on the weak interval. On a component subtract any certified local potentials and add their proved expectation bounds. Bound the resulting polynomial separately at 1 and on the off-diagonal interval. The diagonal mass is \(1/q\) for uniform weights. For \(q=5,7,9\) using an \(f\)-optimal measure of cost at most \(c\), it lies in \([1/q,(64c+1)/49]\) since \(f\ge-1/64\). In a certificate marked `g7` the seven-point mass is instead \(g\)-optimal, so its diagonal mass lies in \([1/7,(.180+.021)/(.75+.021)]\). No unrelated mass constraints are used in those rows.

The [rational replay](verify-kissing-132-mixed-moments.py) recomputes the census and checks **57** mapped predecessor-style certificates and **218** directly encoded certificates. In every case a sum of nonnegative harmonic energies has a strictly negative rational upper bound. All one-dimensional maxima are rigorous Bernstein upper bounds. Hence a 132-point code cannot fail to contain 63 disjoint strict pairs.

Finally let \(N\) be arbitrary. Delete a canonical Tutte–Berge barrier of size \(t\); let \(o\) odd factor-critical components remain, including \(s\) singletons. By the canonical barrier identity \(N-2\nu=o-t\), so the required number of parts is
\[
          L=N-\nu=(N-t+o)/2=\sum_i (k_i+1)/2 .
\]
Adjoin the negative of every surviving singleton. The added points are compatible with one another and the remaining code: the original singleton has weak product with every other point. Its negative forms an isolated strict pair with it. The resulting code has \(\widehat N=N-t+s\le132\), with the **same** minimum number of parts \(L\); each odd component itself needs exactly \((k_i+1)/2\) and each isolated pair needs one. If \(\widehat N=132\), the matching theorem gives \(L\le69\).

For \(\widehat N\le131\) use the scalar budget on these separated components. An isolated strict antipodal pair may use a point mass, so its item is (point count, part count, charge) \(=(2,1,w_1)\). A nontrivial odd component provides \((k,(k+1)/2,w_k)\), \(k\ge5\). The replay initializes \(D(0,0)=0\) and all other entries at infinity, and adds these items with unlimited multiplicity, retaining the least charge per pair of counts. Among \(\widehat N\le131\) and \(L\ge70\), the least integer charge is **84,017,101**, above 84,000,000. This proves the uniform 69-part bound, including codes which need not extend to 132 points.

**Replay from this directory**, using ordinary Python (no `-O`):
~~~sh
python3 verify-kissing-132-local-polynomials.py census
python3 verify-kissing-132-local-polynomials.py all
node verify-kissing-132-source-charts.js
python3 verify-kissing-132-mixed-moments.py
~~~
The Gram search requires NumPy, SciPy and threadpoolctl. The source and partition replays require only the standard Node and Python libraries, respectively. The longest two quartic trees can also be run separately with `five` and `seven`; `degree10` optionally accepts class indices. Immutable predecessors linked above supply the established nine-point quartic result, canonical barrier, and charge table.
