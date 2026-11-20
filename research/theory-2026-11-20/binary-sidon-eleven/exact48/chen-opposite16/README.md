# The unique opposite 16-set to the Chen binary 48-set

**Theorem.** Let A be the 48-point Sidon set in F₂¹¹ specified in `chen48.txt` (zero together with parity-check columns of the classical Chen binary [47,36,5] code, from the [Grassl code entry](https://www.codetables.de/BKLC/BKLC.php?q=2&n=47&k=36); [Chen's paper](https://doi.org/10.1109/18.133262)). There is exactly **one translation orbit** of 16-point sets B⊂F₂¹¹ such that (A,0)∪(B,1) is Sidon in F₂¹². No automorphism of A is needed to identify these B. A representative is

    0 90 166 284 368 402 556 660 870 970 1248 1316 1358 1530 1726 1752

The resulting 64-set is linearly equivalent to the graph of the known quadratic APN Gold extension on F₃₂×F₂:
$$
 (x,y)\longmapsto\bigl(x^3+y(x^{16}+x),\;y\operatorname{Tr}_{32/2}(x)\bigr).
$$
This function and its quadratic context are prior work: see [Beierle–Carlet, after Proposition 1](https://doi.org/10.1007/s10623-022-01111-6), [Beierle–Leander–Perrin](https://doi.org/10.1007/s10623-022-01024-4). We do not assert that *every* six-variable APN function with linearity 32 has a Chen hyperplane section. The consequence certified here is conditional: every six-variable APN function whose graph has a 48-point section affinely equivalent to A is CCZ-equivalent to this map, without assuming that the given function is quadratic. CCZ-equivalence here is affine equivalence of the graphs in the concatenated binary coordinates. If every extremal 48-set in dimension 11 were proved equivalent to A, then the known maximum-linearity value 32 would turn this into an unconditional uniqueness theorem; that additional classification is not an input or claim of this package.

## Proof and verification

For any finite X let ΔX consist of its unordered sums of two distinct elements. For the given Sidon A, a completion exists exactly when B is Sidon and ΔB∩ΔA is empty: a zero-sum quadruple must have zero, two, or four entries in the opposite layer. Translating B independently preserves both conditions and is an affine shear of the ambient sliced space.

The first exhaustive enumeration fixes an order on allowed nonzero differences. A B uses its least difference d on exactly one pair. Translate that pair to {0,d}; this gives exactly two choices, interchanged by adding d. The lexicographically smaller rooted subset is kept. A set of size more than two cannot be fixed by a nonzero translation because that translation would occur as the sum of two distinct pairs in at least two ways. Later pair differences must lie later in the fixed order. The second enumeration fixes a point at zero, without fixing a least d, grows a clique in the Cayley graph of allowed differences, and explicitly requires B to be lexicographically least among all its sixteen translates through zero. These enumerations have different branching and normalization rules. Both rule out further zero-sum quadruples by removing sums of each new point with any two earlier points. A greedy partition of the candidate graph into stable sets gives an upper bound on how many further clique points can be selected. Neither enumeration uses an unproved bound, a spectral filter, a cutoff, or an assumed automorphism group. The complete searches both produce the single translate class displayed above; the second counts sixteen labeled sets containing zero.

The field is F₂[t]/(t⁵+t²+1), encoded in the low five bits, with the sixth bit encoding y. The concatenated graph words are x₆+64F(x₆) for the integer input x₆ in 0,…,63. In the Chen completion, the high bit (2048) denotes the opposite layer. The images of the twelve binary basis vectors under the map from the function graph to the Chen completion are

    2174 694 1260 2616 884 1024 948 278 1200 1148 540 3743

The replay tests invertibility on all 4,096 vectors, equality of both point sets, all 2,016 unordered distinct-pair sums, the complete derivative table and all 4,032 component Walsh correlations. It verifies linearity 32 of this function, not just an abstract code equivalence. Any affine identification of a 48-section with A extends to an affine ambient isomorphism. Together with the unique opposite translate class this gives the claimed conditional CCZ statement.

## Replay

Run `python3 -O check.py` in this directory with Python ≥3.10 and g++ (C++17). Only the Python standard library and compiler are required. The two small C++ programs are compiled in a temporary directory. The supplied reference transcripts are informational; the checker regenerates its own outputs and verifies the sets.
