# In a 75-point matching obstruction, every seven-point component is a distorted chordless cycle

**Theorem.** Let $C$ be a 75-point kissing code in $\mathbb R^6$, and join two points when their inner product is **strictly below** $-1/2$. If there are not 36 pairwise disjoint such edges, every component of order seven is **exactly a chordless 7-cycle** as a graph. As a configuration of vectors it is **not** cyclic: in the cycle order, the RMS deviation of its $7\times7$ Gram matrix from its cyclic average exceeds $1/225$.

There are only **eight** candidate multisets of component sizes. Every row below also contains a singleton:
```
7,7,27,33    7,7,29,31    7,9,27,31    7,9,29,29
7,11,27,29   7,13,27,27   9,9,27,29    9,11,27,27
```
In six of the rows there is at least one such distorted chordless cycle; the last two rows have no seven-point component. In particular, if **any** seven-point strict component contains a chord of a spanning 7-cycle, or does not have a spanning 7-cycle, then the original 75 points have 36 disjoint strict pairs. An unframed seven-point Gram matrix is used throughout; no symmetry or root subsystem is prescribed. Neither the last eight size lists nor 75 points in general are ruled out.

## Why the other five graph types cannot occur

Write $f(t)=t^4-t^2/4$. The [component asymmetry theorem](https://github.com/mxym/math/blob/3a815c47958df290d042f9e0e9976c5aa2093fbf/research/euclidean-tensor-geometry/KissingSixSevenComponentAsymmetry.md) leaves six graph types and gives the metric conclusion quoted above. The five graphs **other** than the bare cycle are listed below. For each of them, in any ambient dimension and for **every** Gram matrix obeying the edge and nonedge ranges, there is a probability vector $p$ on its seven vertices with
\[
                  \sum_{i,j}p_i p_j f(G_{ij})\le 3913/20000 = 0.19565 .
\]
This is a bound on the minimum over weights, **not** on the uniform average. Some nearly antipodal arrangements require nonuniform weights. The five claims are continuous interval certificates, not an enumeration of sampled point sets.

| Graph | Labelled representative mask | Closed tree cells | Terminal exact inequalities |
|---|---:|---:|---:|
| $\theta(2,3,3)$ | 42232 | 137 | 69 |
| $C_7$ plus chord $03$ | 44340 | 1,075 | 538 |
| $C_7$ plus chords $03,25$ | 44404 | 361 | 181 |
| $C_7$ plus chords $04,15$ | 44856 | 139 | 70 |
| $C_7$ plus chords $04,25,36$ | 61112 | 57 | 29 |

Chord labels use the cyclic numbering from the [previous six-class census](https://github.com/mxym/math/blob/3a815c47958df290d042f9e0e9976c5aa2093fbf/research/euclidean-tensor-geometry/verify-kissing-six-seven-component-graphs.js). The separate masks use increasing pairs in lexicographic order on labels 0–6; the census checks their correspondence. The same bound covers the closed edge range $[-1,-1/2]$ and nonedge range $[-1/2,1/2]$, so points on boundary faces are safe.

For the charge proof, distinct graph components have $f(G_{ij})\le0$. A component with a probability measure of energy at most $1/w$ can be assigned charge $w$; the sum of all charges is at most 48 by degree-four harmonic positivity. In the [previous ten-list census](https://github.com/mxym/math/blob/5c34aa6bc59244f3ed2a33ea1b224ae6d5b7b2a0/research/euclidean-tensor-geometry/KissingSixSeventyFiveExtension.md), the least total for a list containing a seven is $47.868660$, with charge $4.975124$ assigned to that component. For any of the five graphs, substituting $20000/3913$ gives
\[
                   47.868660-4.975124+20000/3913>48.
\]
Thus every seven must be the remaining graph. The asymmetry theorem concerns the metric Gram matrix, so it does not contradict this conclusion about adjacency.

## Independently checkable continuous certificates

The [frozen trees](kissing-six-noncycle-heptad-certificates.json) hold the splits and nonnegative integer dual witnesses. Numerical optimization was used to **find** them. The [standalone verifier](verify_kissing_six_noncycle_heptads.py) needs **no numerical solver**. It rebuilds every graph automorphism, every signed spherical-triangle tightening and the full closed-box tree. In particular a simultaneous relabelling chooses a lexicographically maximal order of strong, then weak, Gram coordinates; each ordering constraint used in a leaf comes from a graph automorphism fixing earlier coordinates.

At a leaf, suppose for contradiction that every displayed probability mass has energy above the target. Form a nonnegative integer combination of their energy tests and of inequalities $v^TGv\ge0$ and the valid ordering inequalities. After the diagonal contributions are extracted, the expression separates across edges into univariate polynomials $a_{ij}f(t)+b_{ij}t$ with $a_{ij}\ge0$. The verifier upper-bounds each **combined quartic directly** in the degree-four Bernstein basis on its edge interval, using outward-rounded midpoint subdivision where necessary. The upper sum contradicts the assumed energy lower bound; a zero total probability multiplier instead gives an impossibility certificate for the whole cell. The original witness search used affine quartic envelopes and an LP; this replay does not use either. It visits 1,769 cells, including 887 terminal witnesses, over the five graphs.

## Why two size lists also disappear

There is a second, independent improvement at order 25. For the uniform probability on any 25-point six-dimensional kissing code, a rational three-point positive-kernel certificate gives
\[
 25\,\mathbb E f(X\cdot Y)\le U_{25}=
 \frac{4038635211584013}{2500000000000000}.
\]
The [order-25 verifier](verify-kissing-six-order25-charge.js) replays the same normalized [three-point construction](https://github.com/mxym/math/blob/70aeadbd0f6859eda06452177fb39cebd763eec1/research/euclidean-tensor-geometry/KissingSixStrictPairCover.md) with a new order-25 witness, rational slack $1/75000$, and exact continuous Gram-domain subdivision. Thus the charge, rounded down to a millionth, is $15.475524$. This raises the totals for $(1,7,11,25,31)$ and $(1,7,13,25,29)$ to $48.006512$ and $48.003884$. The other eight lists are simply retained, not asserted realizable.

**Replay:** `python3 verify_kissing_six_noncycle_heptads.py` and `node verify-kissing-six-order25-charge.js`. The Python replay uses only the standard library, and the order-25 replay uses standard Node. The cardinality input remains [Tomar's upper bound $\tau_6\le76$](https://www.mefyi.com/papers/kissing-numbers-five-seven/); no new cardinality bound is claimed here.
