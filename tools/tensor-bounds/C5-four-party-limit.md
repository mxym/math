# Four parties still do not improve the C5 test

This workbench note is an exact limit of a proof strategy, not an exact value for the five-party tensor.

A four-part quotient of C5 merges exactly two vertices. Merging adjacent vertices gives a square, with exponent 4. Merging nonadjacent vertices gives a unit-weight triangle with a pendant of weight 2 at one corner. Its exponent is exactly 49/12, using the [triangle-with-pendant theorem](../../research/euclidean-tensor-geometry/TrianglePendantStarExact.md).

This is not limited to direct coarsening. Suppose each original party makes a local linear restriction on its whole collection of coordinates, even in a tensor power. If we subsequently group those parties, we could instead have grouped first and applied the tensor product of those local maps within each group. The resulting grouped tensor is therefore always a restriction of the original quotient (or a power of that quotient). Its exponent per copy cannot exceed that quotient's exponent. This claim is for local linear restrictions and includes the splices this tool produces.

Thus ordinary rank after final grouping into four or fewer parties cannot certify more than 49/12 by this route. This does not restrict methods that use all five parties, or methods that apply a different invariant rather than ordinary rank of such a quotient. It neither improves the lower bound nor determines the unweighted C5 exponent.
