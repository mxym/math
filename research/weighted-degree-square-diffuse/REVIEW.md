# Independent internal review: centered degree-square bound

**PASS** on the proof at SHA256 65916f1c9ff37de40216262ee1825696feea4693f6a66e6d2b312c1a009bc4b6. This is a scoped excerpt of an independent AI review, retaining its complete alternative proof for this result. Material about a superseded manuscript was omitted with the reviewer’s agreement; the independent checker is unchanged. This is not external peer review or a priority determination.

## Direct physical cut, without a cube relaxation assumption

Normalize total weight to one, with the edge sum taken once per unordered pair. Fix an initial partition of cut weight c. Let m be its degree-weighted signed mass in the manuscript; reflect if needed, write u=|m|, and call the positive-mass-majority side H. Its internal edge weight b obeys 2b+c=1+u. For any 0≤λ≤2, independently move each vertex in H to the other side with probability t=λu/(1+λu); never move a vertex of the other side. Ties u=0 give t=0 and are harmless. This is a distribution on actual cuts with no independence assumed of the final signs unconditionally. The exact conditional expected cut is (1−t)c+2t(1−t)b. Since the maximum C/W bounds it, multiplication by (1+λu)² yields, with A=2C/W−1,
```
A(1+λu)² ≥ (2λ−λ²)m²−f(ε),    f(ε)=1−2c.
```
This is true even when the initial cut is empty (u=1 in the absence of isolates), and confirms the squared denominator and cross term by counting two kinds of edges. Equivalently, the cut obtained conditionally by independent signs of the manuscript's means is exactly the described distribution (for negative m reflect first). Vertex weights are p_i=d_i/(2W), not d_i/W. The normalization gives ∑_{i<j}(w_ij/W)(ε_i+ε_j)=2m.

The crucial simplification of multiplying **before averaging** was found independently in this review and by the manuscript's author. Independent centered initial signs give E f=0 and E m²=P, so
```
A ≥ (2λ−λ²)P/[1+2λ E|m|+λ²P] ≥ (2λ−λ²)P/(1+λ√P)² .
```
The denominator is positive and the numerator nonnegative for all the indicated λ. For s=√P take λ=1/(1+s). Independently, the exact optimization identity is
```
(1+sλ)² −(1+2s)(2λ−λ²) = [1−(1+s)λ]² .
```
It proves both optimality for this last rational bound and the claimed value A≥P/(1+2√P), even without differentiating. Thus C/W≥1/2+P/[2(1+2√P)]≥(1+P)/2−P^(3/2) for all loopless finite nonnegative weights, W>0. This gives a positive improvement over the random-cut floor for every P, not the unrestricted exact conjecture. The odd uniform cliques' coefficient 1/2 is tight as BEKSZ already note. No sharpness of the error order or constant for actual Max-Cut follows.

## Comparisons and exact checks

For the disjoint equal-total-weight uniform cliques on k and k² vertices, each vertex in the respective component has endpoint masses 1/(2k) and 1/(2k²). Thus P=(1/k+1/k²)/4, and nP=(k+1)²/(4k)→∞. This only separates the parameters; on that graph a componentwise balanced cut already works. The order-only bound and the asymptotic nP→1 case are prior: see [Gutin–Yeo Cor. 2.4](https://arxiv.org/pdf/2104.05536) and [Gutin–Nielsen–Yeo–Zhou, Lem. 2.1 and Thm. 2.1, also heavy-star-on-clique Prop. 2.1](https://arxiv.org/pdf/2507.05827). [Gerke–Gutin–Yeo–Zhou, Nov. 2026](https://arxiv.org/html/2611.22760v1) gives a sharp surplus in terms of ordinary maximum degree; not this P. [BEKSZ Conjecture 5](https://doi.org/10.4230/LIPIcs.ITCS.2025.22) is the degree-square question, #132 an exact result for structured weights. #115/#123/#127/#133 concern their different Conjecture 3. Neither a finite positive-P exact solution nor an advance on channel noise is derived. External searches of the original question, weighted Max-Cut and weighted degrees, centering/flipping biased sides, cube rounding, graph discrepancy and judicious partition did not locate this arbitrary-profile inequality. The complete-tree, tag and release survey and own-repository boundary are documented separately in this research package. No claim to originality of independent rounding, second-moment identities or weighted averaging.

Run `python -B -O independent.py`; the checker uses exact rational arithmetic, direct enumeration of new flip outcomes, all 728 nonzero four-vertex graphs with weights in {0,1,2}, additional graphs, exact fourth moments and square-root-free checks of the optimized bound. It is evidence of implementation/normalization consistency; the short algebra above proves the all-order result.
