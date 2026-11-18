# Further consequences for coordinate supports

Use the notation of [the main proof](PAPER.md). Each product basis here is the tensor product of one orthonormal basis for each physical site, shared by the words; we make no assertion about arbitrary expansions in nonorthogonal product vectors.

## 1. All-rank endpoint compressions: exact classification

For any nonempty word set $A$, put $S_{ij}=(-1)^{h(i,j)}$, $i,j\in A$. At the endpoint the diagonal sector of the row-compressed operator is exactly $2^{-n}S$; all other sectors are positive scalings of principal submatrices of $S$. Consequently nonnegativity for **all ranks** and arbitrary co-range is equivalent to any of the following:
1. $S\succeq0$.
2. $S_{ij}=e_i e_j$ for a sign $e_i\in\{-1,1\}$ on each word.
3. Every triple of distinct words has an **even** number of coordinates where all three letters are distinct.

Indeed a Gram matrix with unit diagonal and off-diagonal entries in $\{-1,1\}$ consists of collinear unit vectors, proving 1 implies 2. Conversely 2 is PSD and plainly gives positive sign product on triangles. Positive triangle products imply 2 by fixing an anchor. In a coordinate, the parity of the sum of three pairwise distances is odd only if all three letters differ, proving 3. If a triangle violates the condition, its signed principal matrix is diagonal-sign-conjugate to $2I_3-J_3$, giving a **rank-three** negative diagonal test. It need not be a rank-two distillation witness. If the triangle condition holds, the sector kernel at any $0\le t<1/2$ is a sign conjugate of $(z^{h(i,j)})$; this is positive definite, since it is a principal submatrix of a tensor product of $(1-z)I+zJ$ with $z=t/(1-t)<1$.

### Exact sizes for ternary row supports

For $A\subset\{0,1,2\}^n$ satisfying this condition one has $|A|\le2^n$, with equality only for a full product of two-letter sets. If **all three letters occur at each coordinate**, the sharp bound for $n\ge2$ is
$$
 |A|\le 2^{n-1}+1.
$$
This second bound measures only the dimensions of coordinate subspaces with positive semidefinite compression, not all rank-two-positive subspaces.

Encode the three symbols as $00,01,10\in\mathbb F_2^2$. The indicator of nonzero on the two-bit plane is $Q(u,v)=u+v+uv\pmod2$. Hence the parity of the three distances on the words $a,x,y$ equals $B(x-a,y-a)$, with $B$ the sum of the nonsingular local alternating forms $uv'+vu'$. Translated differences of $A$ therefore span a totally isotropic subspace $L$ of the $2n$-dimensional symplectic space; write $k=\dim L\le n$. Thus $|A|\le2^k$. Equality at $2^n$ forces its affine span to be the entire set. Each two-bit coordinate projection of that affine subspace then avoids $11$, so has dimension at most one. Cardinality $2^n$ forces exactly two letters per coordinate and all choices of the letters.

For the full-three-letter refinement assume every one-coordinate projection has at least three elements, hence rank two on $L$. The affine span $a+L$ projects to all four elements there, of which the forbidden value $11$ is omitted by $A$. Consider a growing list of coordinate projections; keep only ones that increase the dimension of the combined image. Eventually the dimension is $k$, since the original embedding is injective. At the first coordinate the projection of $A$ has at most three elements in affine dimension two. Inductively bound its size in dimension $j\ge2$ by $2^{j-1}+1$.
* If the next coordinate adds two independent bits, each old word has at most three permitted lifts. Then $3(2^{j-1}+1)\le2^{j+1}+1$ for $j\ge2$.
* If it adds one bit, each old word has at most two lifts. The fiber of the enlarged affine span over each old word projects to a two-point affine line with the same direction in the new two-bit plane. Since the new projection has full rank two, the attainable two-point lines occupy both cosets of this direction. The old words for which the line contains the forbidden letter form a nonempty proper affine hyperplane of the old affine span (one nonconstant affine condition). The old projection of $A$ spans that whole affine span, so at least one old word lies in this hyperplane; otherwise it would lie in its hyperplane complement over $\mathbb F_2$. At that word at least one of the two lifts is excluded. Thus the total is at most $2(2^{j-1}+1)-1=2^j+1$.
This proves $|A|\le2^{k-1}+1\le2^{n-1}+1$. Sharpness: use all binary even-weight strings, together with $2^n$ (the constant ternary string whose letters are all 2, not the cardinality). Every triple containing the exceptional word has an even number of rainbow positions because the two binary words differ at an even number of sites. For $n\ge2$ all projections contain three letters.

## 2. Four-row sparsity obstruction for qutrits

**Corollary.** At $t=1/2$, no rank-at-most-two qutrit test with at most four nonzero product-basis rows (or columns) detects negativity, for any number of copies. Equivalently, a counterexample must use at least five rows and at least five columns in every local product basis. Here the four-word corollary combines the main theorem with a cited, unrefereed two-sector theorem; it is not needed for the simplex-code hierarchy.

For at most three words, either they are trifferent or the unique triple never has a rainbow site and §1 applies (likewise if fewer). For four words, if they are trifferent use Theorem 1. Otherwise some triple $a,b,c$ uses at most two letters at every site. Write $w$ for the fourth word. Split the sites as follows:
* A thin site has at most two letters among all four words.
* At any other site, the triple uses exactly two letters and $w$ uses a different third letter.

Thin factors can be removed without increasing Schmidt rank. Indeed the row-compression of the local $W_3(1/2)$ to a coordinate plane is separable across row and column: on the plane times its matching column plane it is $I-|\Omega_2\rangle\langle\Omega_2|/2$, the partial transpose of the separable operator $I-F_2/2$; on its complement it is a product identity. A one-dimensional row factor is simpler or may be enlarged to a plane. Decompose each such local factor into positive combinations of product rank-one projectors. Evaluating their tensor product contracts $C$ by separate row and column linear functionals on those sites, preserving rank at most two and leaving row support in the span of the remaining strings.

If any sites remain, the first three rows are then in the product of their local two-letter spaces, and the fourth is in the product of the complementary lines, orthogonal at **every** remaining site. Apply the one-sided endpoint corollary of [Mishra–Senthilkumar, Two orthogonal product sectors](https://github.com/anshM123/werner-npt-research/tree/main/two-sector-class) to each contraction. No sites left is trivial. The column version follows by adjoint invariance. Local unitary covariance and the matched product basis on the other side allow the claim in every local basis. (Rank-two tests with no bound on their product-basis row count are not addressed.)

The small three-word case also overlaps known thin and repetition reductions after deleting sites with at most two letters; it is not our principal novelty claim.
