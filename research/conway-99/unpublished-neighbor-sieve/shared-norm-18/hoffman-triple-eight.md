# Three Hoffman cocliques of pairwise intersection eight

**Theorem.** In any strongly regular graph with parameters (99,14,1,2), if three 22-cocliques meet pairwise in eight sites, their triple intersection has size **3 or 4**. Neither linear-algebraic rank nor any automorphism hypothesis is needed. The two surviving intersection sizes both admit nonnegative integral controls for the specific local counting equations below; this does not say that the graph, or either triple, exists.

Put t=|C₁∩C₂∩C₃|. Partition the graph into its eight membership cells indexed by the binary masks 0,…,7 (low bit corresponds to C₁). Inclusion-exclusion gives the respective sizes
```
c=(57−t,6+t,6+t,8−t,6+t,8−t,8−t,t).
```
For a root in cell i let h_j be its number of neighbors in cell j. Enumerate all nonnegative integer profiles satisfying sum h_j=14, h_j≤c_j−[i=j], and sum_{j:j has bit k} h_j=0 or 4 according as i does or does not have that bit. The latter condition holds because each maximum 22-coclique is independent and every outsider has four neighbors in it. In particular no neighbor shares a nonempty membership with the root. Let x_(i,h) count vertices of each profile. It is enough to use the following equations:

* **Mass:** sum x_[i,h] over h is c_i.
* **Undirected edges:** for a≠b sum over all roots of [i=a]h_b−[i=b]h_a is zero.
* **Common neighbors:** for a≤b the sum over roots of h_a h_b+[i=a]h_b is 2c_a c_b+12c_a[a=b]. Indeed the first summand counts two-step walks from one cell to the other and A²=12I+2J−A; the second summand cancels the directed edge correction. This includes the diagonal case.

For t=0,…,8 the numbers of raw (i,h) types are 60,84,95,99,100,94,76,39,9. The [exact certificate](hoffman-triple-eight.py) separately supplies an integer linear combination of these equations for each t other than 3 or 4. To shorten the certificates, the combination is averaged over the six ways to rename the three cocliques. The right sides are unchanged because their pair intersection sizes are equal. This is a formal relabeling of the hypotheses, not a permutation symmetry of the graph. The checker verifies that each resulting coefficient of every single allowed profile is nonnegative; in the seven rejected cases the exact weighted right sides respectively equal
```
−21227832, −2899008, −819504, −1584, −8527104, −54802008, −6468.
```
The checker uses integer weights and tests the sixfold coefficient sums without division. For t=3 and 4 it verifies integer multiplicities in the original, **unaveraged** equations, not just their symmetric projections. No LP solver or nonstandard Python package is needed: run `python3 hoffman-triple-eight.py`.

This restriction applies, in particular, to the three-eligible-coclique option of [the sparse two-type counts](two-type-short-counts.md) if all three intersections are eight. It does not eliminate that option as a whole; pair intersections involving one have not been excluded by this argument.
