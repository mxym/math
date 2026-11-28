# Near-contact counts and a strict angular bound for 132 points in seven dimensions

**Theorem.** If 132 unit vectors in $\mathbb R^7$ have all pairwise angles at least $60^\circ$, at least **1,372** unordered pairs have inner product greater than $0.490$, at least **541** exceed $0.497$, and at least **7** exceed $0.4989$. Those last pairs have angles in $[60^\circ,60.073^\circ)$. No symmetry, roots or other prescribed subconfiguration is required.

Consequently $A(7,\arccos(0.4989))\le131$: any 132-point subset at that stronger separation would contradict the last count. This is **not** $A(7,60^\circ)\le131$ and does not exclude or construct a 127–132 point kissing code. [Tomar's seven-dimensional cardinality theorem](https://www.mefyi.com/papers/kissing-numbers-five-seven/) gives the upper bound 132 at $60^\circ$; the $E_7$ lower bound is 126.

| Code size $N$ | Thresholds $t$, in order | Lower bounds on the number of unordered pairs with $x\cdot y>t$ |
|---:|---|---|
|127|.485|180|
|128|.4875|190|
|129|.490|238|
|130|.490|360|
|131|.495|274|
|132|.490, .495, .497, .498|**1,372**, **878**, **541**, **230**|
|132|.4984, .4986, .49875, .4988, .4989|**173**, **126**, **68**, **43**, **7**|

At 132 points, some point has at least **21** neighbors above $.490$; at least **35 disjoint** pairs exceed $.490$. At $.495$, $.497$, $.498$, and $.4988$ there are respectively at least **23, 14, 7, 2** disjoint pairs. The last assertion is deliberately not extended to $.4989$.

## How to verify the distribution

The dimension-six [triangle-slack reduction and all three expectation inequalities](https://github.com/mxym/math/blob/81c753971de179bf2fb1c2f76ba4dfd46216338d/research/euclidean-tensor-geometry/KissingSixCoupledTriangleContacts.md) carry over after changing the dimension, the original certificate, and every numerical dual row. Specifically put $L=\binom N2$, $H=\binom N3$, $M=13299/100$, and $v=(1,N,q_0,\ldots,q_{10})$, where $q_j$ sums the $j$th powers over unordered pairs. Tomar's seven-dimensional four-point certificate gives
\[
 v^TFv+N a_1+\sum_{\{x,y\}}R_2(x\cdot y)+\sum_{\{x,y,z\}}R_3(x\cdot y,x\cdot z,y\cdot z)\le M-N.
\]
The third sum is over **sets**, with no extra multiplicity. We discard the nonnegative four-distinct-point slack and other representation energies. The trivial block $F$ is positive semidefinite. For a rational test vector $z$ we retain the affine lower bound $2z^TFv-z^TFz$ instead of discarding the block.

For an edge use the normalized $d=7$ Gegenbauer recurrence with coefficients $(2j+5)/(j+5)$ and $-j/(j+5)$. For the stabilized three-point kernels anchored at a vertex use projections onto $\mathbb R^6$, so with $Q_0=1$, $Q_1=w-uv$ the recurrence is
\[
 (k+4)Q_{k+1}=(2k+4)(w-uv)Q_k-k(1-u^2)(1-v^2)Q_{k-1}.
\]
Averaging over the choice of anchor symmetrizes the kernel. Counting coincidences among three indices gives the terms with multiplicities $N-2$, one and $2\mathbf1_{k=0}$ in the linked derivation. These are valid at degenerate projections by continuity. The corresponding positive kernels and the four-point tangent yield the inequalities $\mathbb E A_i\le B_i$. The expectations are over distinct triangles (with a uniformly chosen edge or anchor where indicated).

For each row the [snapshot](kissing-seven-coupled-contact-data.json) gives nonnegative rational multipliers $\lambda_i$, the anchor polynomials and the tangents. For each possible triangle let $m$ be the number of its three products strictly above $t$. The [driver](verify_kissing_seven_coupled_contacts.py) and [Bernstein checker](verify-kissing-seven-contact-bernstein.js) certify
\[
 Lm/3+\sum_i\lambda_i(A_i-B_i)\ge K-1+1/100.
\]
Taking expectations and using integrality proves the stated bound $K$. The four threshold strata are checked separately over closed boxes and the Gram domain $1+2uvw-u^2-v^2-w^2\ge0$. An edge exactly at $t$ is assigned to the low side. The checker transforms exact integer polynomials to tensor Bernstein form, rounds outward, subdivides, and checks every dyadic Gram multiplier by exact coefficient comparisons. Sampling, floating-point optimization and unverified positivity of a rounded SOS matrix are not premises.

The optional [source audit](verify_kissing_seven_contact_source.py) checks **57 original file digests**, all **391** entries of the four retained pair/singleton/trivial matrices, and all **15** third-union dense Gram blocks with their rational transforms and polynomial bases. The four matrices have entrywise interval width at most $2\cdot10^{-24}$. For the triangle polynomial, flooring matrix entries at $10^{-34}$, expanding with exact rational transforms, symmetrizing, then flooring monomials at $10^{-26}$ leaves **351** distinct nonzero permutation representatives and uniform error $<2\cdot 10^{-23}$ on $[-1,1]^3$. For each prefactor $g$ and transformed basis vector $h$ the first error is bounded by $10^{-34}\|g\|_1(\sum_i\|h_i\|_1)^2$ using coefficient norms; the second charges one unit for each uncompressed monomial. All errors, including repetitions across the $H$ triples, enter the tangent budget. This reuses the original verified union identity rather than independently reproving the entire cardinality theorem.

## From counts to disjoint pairs

Around a vertex, two neighbors at heights $a,b>t$ project to unit vectors with product at most $(1/2-ab)/\sqrt{(1-a^2)(1-b^2)}\le (1/2-t^2)/(1-t^2)$. The last function is decreasing in either coordinate here since $a,b\in[t,1/2]$ and $t>1/4$. In dimension six a one-variable positive-Gegenbauer certificate bounds the size of this projected code: its constant coefficient is one, all other coefficients are nonnegative, and the polynomial is negative on the whole allowed interval. Its value at one bounds the degree. Exact univariate Bernstein replay gives maximum degrees **39, 38, 37** at $t=.490,.495,.498$. A simple graph of maximum degree $\Delta$ has an edge coloring with at most $\Delta+1$ colors (Vizing), yielding the matching bounds. The degree-21 assertion uses $2(1372)/132>20$.

**Reproduce:** run `python3 verify_kissing_seven_coupled_contacts.py` in this directory (Python 3.9+ and Node 18+, no third-party packages). A selection such as `132:0.4989` checks just that row in addition to the cap certificates. To rederive the compact inputs run `python3 verify_kissing_seven_contact_source.py proof_7_132.tgz`, or replace the path with `download` to stream the [original 907 MB v3 archive](https://github.com/tejasvi/kissing-numbers-lasserre/releases/download/v3/proof_7_132.tgz). The original certificate and derived data are credited to [Tejasvi Singh Tomar, CC BY 4.0](https://doi.org/10.5281/zenodo.24093810). The multipoint hierarchy is due to [de Laat, Leijenhorst and de Muinck Keizer](https://arxiv.org/html/2404.18794v2#S4); distance-distribution bounds from multipoint certificates were developed by [Musin](https://arxiv.org/html/2309.13854v4). The numerical counts here are additional consequences, not independent rediscoveries of those methods.
