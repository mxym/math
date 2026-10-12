# A direct proof of the full equality classification

Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology. Email: mxymmxym1@gmail.com.
ORCID: 0009-0000-3864-3536. AI-assisted research; no external funding.

This supplement completes the formal proof of Theorem 1 of the four-row
permanent–determinant paper. It does not change the mathematical statement
or assert a new discovery or external peer review.

Write Q=|per A|, D=|det A|, R=the product of the four Euclidean row norms,
and M(c)=max(3/2,1+c). The sharp bound Q+cD<=M(c)R was already formalized.
Here is a proof of all equality cases that does not require the manuscript's
separate quantitative Theorem 4 to have been formalized first.

## 1. Propagation to every pair

Assume initially that every row is nonzero. For two rows a,b set
U=||a||^2, V=||b||^2, E=|sum_j a_j conjugate(b_j)|^2,
T=sum_j |a_j|^2 |b_j|^2 and F=S+(1/2)W. The exact expansion is
F=(3/2)UV+(1/2)E-2T. Cauchy gives E<=4T, hence F<=(3/2)UV.

At critical matrix equality Q+D/2=(3/2)R, the already proved weighted
Laplace estimate gives

    ((3/2)R)^2 <= F(a,b) F(d,e)
                  <= F(a,b) ((3/2)||d||^2||e||^2).

The left side is the product of the two sharp pairwise upper bounds.
The second upper bound is strictly positive. Cancellation therefore forces
F(a,b)=(3/2)||a||^2||b||^2 and E=4T. The proof is invariant under every
row permutation, so the same conclusion holds for every distinct row pair.

For z_j=a_j conjugate(b_j), the universal identity

    4 sum_j |z_j|^2 - |sum_j z_j|^2 = sum_{j<k} |z_j-z_k|^2

shows that E=4T is equivalent to all four z_j being equal. The formalization
proves this sum-of-squares identity and its converse, rather than assuming
a Cauchy equality interface.

## 2. The critical dichotomy

Suppose all distinct row pairs have a column-independent conjugate product.
If every pair of supports is disjoint, choose one nonzero entry in each row.
Their columns are distinct. An injection between the two four-element index
sets is a bijection, and surjectivity forces every other entry to vanish.
Thus the matrix is monomial in the literal permutation-support sense.

Otherwise two rows intersect. Their constant conjugate product is nonzero,
so both have full support. Every remaining nonzero row intersects one of
these and is therefore also fully supported.

For three such rows 0,1,2, put x_ij=|A_ij|^2. Pairwise product constancy gives
x_0k x_1k=x_00 x_10, x_0k x_2k=x_00 x_20 and x_1k x_2k=x_10 x_20.
Multiply the first two, substitute the third, and cancel the nonzero
x_10 x_20. This proves x_0k^2=x_00^2; nonnegativity gives x_0k=x_00.
The actual constant conjugate products with row 0 now give

    A_ik = (A_i0/A_00) A_0k.

Every factor is nonzero. This is an actual equimodular rank-one factorization.

## 3. Converse and all weights

For the rank-one factorization u_i v_j, exact Laplace expansion gives
per A=24 product_i u_i product_j v_j and det A=0. Equimodularity and the
actual row norms then give Q=(3/2)R. For a monomial matrix, column reindexing
produces a diagonal matrix and proves Q=D=R. Both classes therefore attain
the critical bound.

The same Laplace/alternating-energy argument proves D<=R for every A.
For c<1/2, equality in Q+cD=(3/2)R and the critical inequality force D=0;
the critical classification excludes the monomial class since R>0.
For c>1/2, combine the critical bound with (c-1/2)D<=(c-1/2)R. Equality
forces critical equality, and the rank-one class is excluded since R>0.
At c=1/2 both classes occur. Finally R=0 is proved equivalent to an actual
zero row; the sharp inequality and nonnegativity give trivial equality.

Consequently, without any nonzero-row assumption, equality holds if and only if
there is a zero row, or the matrix is flat rank one and c<=1/2, or the matrix
is monomial and c>=1/2. This is the endpoint `sharp_four_row_complete`.

## Trust and attribution

The six original sharp-bound modules are copied unchanged and identified by
SHA256 in `PROOF_SOURCES.json`; they are not counted as new mathematics.
The five new mathematical modules prove all the classification steps above.
The replay dependency collector is verification tooling, not an input to the
mathematical theorems. Its closure check rejects unexpected axioms and
unsafe/partial proof dependencies. No analytic classification theorem is
imported as an unproved premise. The former v1 source and evidence are retained.
