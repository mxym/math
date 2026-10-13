# Strong Chollet inequalities for arbitrarily weighted cycles and block graphs

**Yongxian Zhang (张永贤)**
School of Computer Science and Engineering, South China University of Technology.
Email: mxymmxym1@gmail.com. ORCID: 0009-0000-3864-3536.
13 October 2026. Research and writing assisted by OpenAI AI assistants.
No external funding or external human referee review. Original material:
copyright 2026 Yongxian Zhang, all rights reserved.

## 1. Statements and actual objects

Let G be a finite simple undirected graph with nonnegative real conductances
w_ij=w_ji on its edges, zero elsewhere, and no loops. Write d_i=sum_j w_ij
and let L be the actual weighted Laplacian: L_ii=d_i, L_ij=-w_ij for i!=j.
The positive-support graph has precisely the edges with w_ij>0. All degrees
below are weighted degrees in the original ambient graph. A block means a
maximal 2-connected subgraph or a bridge. Isolated vertices are treated separately.

**Theorem 1 (weighted cycles).** For every n>=3 and every choice of
nonnegative real conductances on the cycle C_n, its weighted Laplacian is
hereditarily strong: for every vertex subset S,

    per(L[S] circ L[S]) <= per(L[S]) product_(i in S) d_i.                  (W1)

For odd n>=3 there is also the explicit whole-cycle bound

    (product_i d_i) per L - per(L circ L) >= 2 (product_e w_e)^2.           (W2)

In particular the whole-cycle strong inequality is strict when all its
conductances are positive and its length is odd. No claim that the constant
2 in (W2) is optimal is made. The empty permanent and product are both one.

**Theorem 2 (weighted cycle--bipartite block graphs).** Suppose every block
of the positive-support graph is bipartite or a cycle. For every nonnegative
real diagonal addition diag(alpha_i), put A=L+diag(alpha_i). Then for every
vertex subset S,

    per(A[S] circ A[S]) <= per(A[S]) product_(i in S)(d_i+alpha_i).          (W3)

This includes every arbitrarily weighted cactus graph, arbitrary disconnected
graphs in the stated block class, isolated vertices, zero conductances,
empty subsets and singular Laplacians. It does not include arbitrary weighted
graphs with other nonbipartite blocks. That wider question remains open here.

The new argument concerns arbitrary positive conductances on odd cycles of
every length at least five. Bipartite support and the matrix closure operations
are already known; the weighted triangle has an existing exact proof in the
repository. We state and justify the needed ingredients without attributing
them as new results. No complete Lean formalization is claimed for this package.

## 2. The known elementary bipartite case and the triangle

A weighted Laplacian and each principal submatrix are positive semidefinite:
x^T L x=sum_(edges ij) w_ij(x_i-x_j)^2. If a real symmetric PSD matrix H has
nonpositive off-diagonal entries and bipartite support, every nonzero permanent
monomial t_sigma=product_i H_(i,sigma(i)) is nonnegative: each nontrivial cycle
has even length. The PSD two-by-two minors give

    |t_sigma| <= product_i sqrt(H_ii H_(sigma(i),sigma(i))) = product_i H_ii.

Hence per(H circ H)=sum_sigma t_sigma^2 <=(product_i H_ii) per H.
This covers even weighted cycles, all forests, and all proper principal
submatrices of any cycle Laplacian. It is the self-matrix specialization of
[Pant--Singh, Theorem 3.1](https://arxiv.org/html/2604.24192v2#S3).

For the triangle with conductances a,b,c>=0, direct polynomial expansion gives

    (product_i d_i) per L - per(L circ L)
      =2(ab+bc+ca)(a^2b^2+b^2c^2+c^2a^2).                              (W4)

This identity already underlies the repository's weighted triangle Lean proof;
we use it as a completed case. AM-GM makes its right side at least
18(abc)^2, and therefore at least the bound in (W2). If a conductance of
any cycle vanishes, its support is a forest and the right side of (W2) is
zero; the bipartite argument proves all required claims. From now on assume
an odd cycle n>=5 and strictly positive conductances.

## 3. Exact cycle formulas

Number vertices and edges cyclically modulo n, with edge i joining i to i+1.
Set d_i=w_(i-1)+w_i, H=product_i d_i and

    M=diag(d_i^(-1/2)) L diag(d_i^(-1/2)) = I-B,
    b_i=w_i/sqrt(d_i d_(i+1)), c_i=b_i^2,
    a=product_i b_i=product_i w_i/H, epsilon=2a.

All numbers here are positive. Let

    Z(c)=sum_(F a matching of C_n) product_(i in F) c_i,
    Z_-(c)=sum_(F a matching) (-1)^|F| product_(i in F) c_i.

The only nontrivial permutation cycles supported by C_n are edge transpositions
and the two directed cycles using all vertices. Thus the actual normalized
permanents and determinant satisfy

    P=per M=Z(c)-epsilon,
    Q=per(M circ M)=Z(c^2)+epsilon^2/2,
    det M=Z_-(c)-epsilon=0.                                             (W5)

The determinant vanishes because the weighted Laplacian has the constant
vector in its kernel. Subtracting the signed matching identity from the
permanent identity gives the important nonnegative formula

    P=Z(c)-Z_-(c)=2 sum_(F matching, |F| odd) product_(i in F) c_i.         (W6)

These are identities for every odd n and every stated real conductance;
they are not consequences of a finite cycle or weight table.

## 4. A classical triangle-free estimate forces P>=2

For a triangle-free graph and any p_i>=0 with sum p_i=1,

    sum_(edges ij) p_i p_j <= 1/4.                                    (W7)

This is the clique-number-two case of the classical
[Motzkin--Straus theorem](https://doi.org/10.4153/CJM-1965-053-6).
For completeness, maximize the continuous quadratic form on the simplex and
choose a maximizer with smallest support. If two nonadjacent support vertices
are present, redistribute their combined mass entirely to the one with
larger neighboring mass. The value cannot decrease, since there is no edge
between them and the dependence on the two masses is linear. This contradicts
minimal support. The support is therefore a clique, which has at most two
vertices; its only possible nonzero value is p(1-p)<=1/4. This proves (W7).

The cycle C_n, n>=5, is triangle-free. The unit vector proportional to
(sqrt(d_i)) satisfies Bv=v. Hence, using Cauchy--Schwarz and (W7) with p_i=v_i^2,

    1=(v^T Bv)^2
      =4 (sum_i b_i v_i v_(i+1))^2
      <=4 (sum_i b_i^2)(sum_i v_i^2 v_(i+1)^2)
      <=sum_i c_i.

The one-edge terms in (W6) now yield P>=2 sum_i c_i>=2. The Motzkin--Straus
estimate and this spectral consequence are classical tools, not novelty claims.

## 5. Independent neighbor choices compare the two matching polynomials

At each vertex i independently choose one of its two neighbors, choosing
i+1 with probability w_i/d_i and i-1 with probability w_(i-1)/d_i. Let F be
the set of mutual choices: edge i belongs to F exactly when i chooses i+1
and i+1 chooses i. F is a matching. For every matching S,

    Pr(S subset F)=product_(i in S) c_i.                               (W8)

The relevant endpoint choices are disjoint, so their probabilities multiply.
There are no mutual choices if and only if all the vertex choices point in
one cyclic direction. A nonconstant cyclic sequence of clockwise/counterclockwise
choices has an adjacent clockwise-then-counterclockwise pair, which is mutual.
Each of the two constant sequences has probability a, and therefore

    Pr(F empty)=2a=epsilon.                                            (W9)

Expanding 2^|F|=sum_(S subset F) 1 and taking expectations gives
E[2^|F|]=Z(c). For an independent copy G of F, (W8) gives
E[2^|F intersection G|]=Z(c^2). Pointwise,

    2^|F|-2^|F intersection G|
      >= 1_(G empty) (2^|F|-1).

The left side is always nonnegative and is exactly 2^|F|-1 when G is empty.
Independence and (W9) therefore give the universal comparison

    Z(c)-Z(c^2) >= epsilon (Z(c)-1).                                  (W10)

Substituting (W5) and then P>=2,

    P-Q >= epsilon (Z(c)-2-epsilon/2)
         =epsilon(P-2+epsilon/2) >= epsilon^2/2.                       (W11)

Undoing diagonal normalization multiplies the strong defect by H^2. Since
H^2 epsilon^2/2=2(product_i w_i)^2, this proves (W2) and the whole-cycle
part of (W1). Proper principal subsets were already covered in Section 2.
This completes Theorem 1, including zero weights, zero degrees and n=3.

## 6. Ambient principal degrees, diagonal additions and block assembly

We use the classical **Lieb block permanent inequality**: for a Hermitian
PSD matrix, the permanent is at least the product of the permanents of its
principal diagonal blocks. In particular per A>=product_i A_ii and
per A>=A_vv per A(v). The original reference is
[Lieb, 1966](https://doi.org/10.1512/iumj.1967.16.16008).
This is a disclosed published ordinary-mathematical input, not an unproved
Lean theorem asserted by this package.

The following hereditary closure is precisely
[Pant--Singh, Theorem 4.3 and Appendix A](https://arxiv.org/html/2604.24192v2#S4):
hereditarily strong PSD matrices remain so after a nonnegative diagonal
addition and after a one-point sum. The matrices at the common index have
their diagonal entries added; entries between the two other index sets are zero.
The matrix remains PSD as a sum of two embedded PSD matrices.

Here is the scalar calculation clarifying that weights cause no obstruction.
Let a_i be the distinguished diagonal, P_i=per A_i, R_i=per A_i(v),
Q_i=per(A_i circ A_i), T_i=per(A_i(v) circ A_i(v)), and
h_i=product diag A_i(v). Exact cycle expansion gives

    per(A_1 star A_2)=P_1 R_2+R_1 P_2,
    per((A_1 star A_2) circ (A_1 star A_2))
      =Q_1 T_2+T_1 Q_2+2 a_1 a_2 T_1 T_2.

Using Q_i<=a_i h_i P_i and T_i<=h_i R_i, the difference between the target
upper expression and this upper estimate is

    h_1 h_2 [a_2 R_2(P_1-a_1 R_1)+a_1 R_1(P_2-a_2 R_2)] >=0,

by Lieb. Principal submatrices omitting the common index split as direct sums;
those using vertices on only one side add a nonnegative diagonal at that index.
For such an addition alpha at a diagonal a, the exact expansions are

    per(A+alpha E_vv)=P+alpha R,
    per((A+alpha E_vv) circ (A+alpha E_vv))=Q+(2a alpha+alpha^2)T.

The bound Q<=a h P, T<=h R, P>=a R proves the enlarged strong inequality,
because its remaining scalar difference is h alpha(P-a R)>=0.
This also establishes diagonal closure for every principal submatrix.

Each weighted bipartite block is hereditarily strong by Section 2, each weighted
cycle by Theorem 1. Successive one-point sums along the finite block-cut tree
recover the actual weighted Laplacian: common diagonal weighted degrees add,
and edge conductances are unchanged. This proves hereditary strength component
by component; disconnected components multiply. Isolated vertices have the
one-by-one zero Laplacian and cause no exception. Applying diagonal closure
then proves (W3), with the original ambient diagonal entries d_i+alpha_i.
This completes Theorem 2. Lieb also yields the ordinary self-Chollet conclusion.

## 7. Prior scope, verification and remaining questions

Pant--Singh v2 defines unweighted simple graph Laplacians, proves its cycle and
block conclusions in that scope, and already proves the broader matrix-level
bipartite and closure ingredients used here. The repository separately proves
all unweighted graph Laplacians with complete Lean coverage. Neither theorem
is reused as an unsupported bridge to arbitrary conductances. The new cycle
proof uses weighted transition probabilities and the actual singular normalized
Laplacian throughout; it permits conductances with unbounded ratios.

The proof is complete ordinary mathematics, with the published Lieb theorem
as a disclosed external input and the other needed scalar arguments written
out. No new Lean build, kernel replay or external peer-review claim is made.
The companion exact checker independently computes actual integer/rational
weighted Laplacians and principal permanents, validates the stated cycle
identities and mutual-choice moments, and compares the quantitative lower
bound. These finite diagnostics do not establish the all-n theorem; Sections
2--6 do. Literature searches do not certify first historical discovery.

The all-weighted-graph strong Chollet theorem and the larger class of all
real symmetric PSD Z-matrices are **not** proved here. A numerical matching
upper-bound candidate and finite searches remain exploration only. In
particular negative coefficients in a five-vertex weighted defect expansion
are not an actual matrix counterexample, and no coefficientwise-positive
extension is claimed.
