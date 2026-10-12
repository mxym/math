# Retention controlled by the number of extra vertices

8 October 2026. Traditional proof; no formalization or compilation claim.

## Theorem

Put n=d+1. Let r>=1 be an integer, let P be a full-dimensional d-simplex, and let K be a full-dimensional polytope contained in P with at most n+r vertices. Suppose each P-coordinate ell_i attains at least 1-rho on K, with rho>=0. For every prescribed maximum-volume inscribed simplex S, with its original centroid,

\[
 E(K,S)\le64nr\rho.
\tag{1}
\]

The stronger local bound is

\[
 E(K,S)\le8n\rho\qquad
 \left(0\le\rho\le\frac1{64r}\right).
\tag{2}
\]

The local threshold depends on the **number of extra vertices**, rather than on the ambient dimension. For r=1 the separate exact classification in `FEW_VERTEX_LINEAR_RETENTION.md` gives the much better all-scale coefficient 3n.

Combined with the retained actual Entry005 enclosing-simplex and cap chain, (1) gives

\[
 E(K,S)\le64(d+1)rH_d^{1/(d-1)}e(K)^{1/(d-1)}
 \le12288dr\,e(K)^{1/(d-1)},
\]

for K with at most d+1+r vertices. The old universal quadratic estimate can of course be used instead when it is smaller. Thus every fixed vertex excess r has a linear-dimensional stability coefficient, retaining every maximum simplex.

## 1. Near vertices and a comparison simplex

Only the local branch needs proof: for rho>1/(64r), the universal estimate E<=n gives (1). Assume henceforth rho<=1/(64r).

Choose actual K-vertices q_i maximizing the P-coordinate ell_i. Since rho<1/2 these n vertices are distinct. Let Q be their P-coordinate matrix. It is nonnegative column stochastic and

\[
 Q_{ii}\ge1-\rho,\qquad
 \|Q-I\|_1\le2\rho,\qquad
 \|Q^{-1}\|_1\le(1-2\rho)^{-1}\le1+4\rho.
\tag{3}
\]

The final inequality uses rho<=1/4. Therefore T=conv(q_i) is a full-dimensional simplex contained in K.

## 2. Every maximum vertex simplex is already near a permutation

Let S_v be any maximum simplex whose vertices are K-vertices. Its volume is at least V(T). It can omit at most r of the q_i, since there are at most r other K-vertices. Write k for the number omitted, so 0<=k<=min(r,n).

The case k=0 gives S_v=T and needs no block argument. Otherwise let R be the k omitted indices. Relabel the vertices of S_v so that the retained q_i occupy column i for i outside R; place the other vertices arbitrarily in columns R. Let W be the P-coordinate matrix of this S_v, and C=Q^{-1}W. Columns C_i are e_i for i outside R. Determinant expansion along those columns gives

\[
 |\det C_{R,R}|=|\det C|
 =\frac{V(S_v)}{V(T)}\ge1.
\tag{4}
\]

Set U=W_{R,R}. This matrix is nonnegative and column **substochastic**. Each column of C has l1 norm at most (1-2rho)^(-1), because each W-column is a probability vector. Also W-C=(Q-I)C, so corresponding restricted columns of U and C_{R,R} differ in l1 by at most

\[
 2\rho(1-2\rho)^{-1}\le4\rho.
\]

Telescoping the determinant one column at a time, and using
|det(v_1,...,v_k)|<=product_j ||v_j||_1, yields

\[
 \bigl|\det U-\det C_{R,R}\bigr|
 \le4k\rho(1+4\rho)^{k-1}.
\]

For x>=0 with kx<1, the binomial expansion gives
(1+x)^(k-1)<=sum_{j>=0}(kx)^j=(1-kx)^(-1).
Here 4krho<=1/16, so (1+4rho)^(k-1)<=16/15<2. Consequently

\[
 |\det U|\ge1-8k\rho\ge1-\eta,
 \qquad\eta:=8r\rho\le1/8.
\tag{5}
\]

### Substochastic determinant matching lemma

If a nonnegative k by k column-substochastic matrix U has |det U|>=1-eta with 0<=eta<1/3, then after a column permutation it has all diagonal entries at least 1-eta.

Proof: represent each column as the expectation of a random standard basis vector, with any missing column mass assigned to the zero vector. The determinant is the expectation of the resulting signed selection determinant. Fixing one column while sampling all the others shows

\[
 |\det U|\le\max_i U_{ij}
\]

for every j: every nonzero sampled cofactor selects exactly one entry of that fixed column, with a sign. Thus each column has an entry at least 1-eta. If two chosen dominant entries share a row, independently selecting both gives a collision with probability at least (1-eta)^2. Every selection determinant has magnitude at most one, hence

\[
 |\det U|\le1-(1-\eta)^2\le2\eta<1-\eta,
\]

a contradiction. The dominant rows are distinct and give the required permutation. This proof includes eta=0 and k=1.

Apply the lemma to (5). The k new vertices can be matched to the omitted indices R with W_ii>=1-eta. Retained q_i already satisfy W_ii>=1-rho>=1-eta. Hence **every maximum vertex simplex** has exactly one vertex in each of the pairwise disjoint caps

\[
 \mathcal C_i=\{x\in K:\ell_i(x)\ge1-\eta\}.
\tag{6}
\]

The caps are disjoint because eta<=1/8<1/2.

## 3. Pass from vertex maxima to the prescribed arbitrary maximum S

Represent each vertex of S as a convex combination of K-vertices and sample these combinations independently. Since S is maximum, equality in the determinant expectation and triangle inequality forces every positive-probability sampled tuple to be a maximum vertex simplex, with one K-vertex in each cap (6).

For each i, some sampled column must lie in C_i with probability one. Otherwise the product of the positive probabilities of avoiding C_i would give positive probability of a sampled tuple missing that cap. Since the caps are disjoint, different i require different deterministic-cap columns. There are n caps and n columns, so after relabeling, the i-th column is supported entirely in C_i. Convexity of C_i implies that the actual i-th vertex of S is in C_i.

Thus the P-coordinate matrix W of this **same prescribed S** satisfies

\[
 W_{ii}\ge1-\eta,\qquad\eta\le1/8.
\tag{7}
\]

No assertion that all maxima have polytope vertices was used. The argument includes continuous families of nonvertex maxima.

## 4. Dimension-free inverse bootstrap on this same S

Let B=W^{-1}, D=B-I, beta=max_ij |D_ij|, and r_j=1-W_jj. From DW=I-W and column stochasticity,

\[
 D_{ij}=(\delta_{ij}-W_{ij})+
 \sum_{k\ne j}(D_{ij}-D_{ik})W_{kj}.
\]

Therefore beta<=eta+2eta beta, giving

\[
 \beta\le\frac\eta{1-2\eta}\le\frac1{6}.
\tag{8}
\]

The ii-entry of BW=I gives

\[
 B_{ii}-1\ge\frac{(1-\beta)r_i}{1-r_i}\ge r_i/2.
\]

Each actual q_i lies in K. Maximum-volume replacement relative to the prescribed S therefore gives (BQ)_ii<=1. Since Q_ii>=1-rho, B_ii>0, and off-diagonal B_ij>=-beta,

\[
 B_{ii}-1\le\rho(B_{ii}+\beta)\le2\rho.
\]

It follows that r_i<=4rho. Reusing the inverse identity with this improved loss gives

\[
 \beta\le\frac{4\rho}{1-8\rho}\le8\rho,
\]

where rho<=1/64 supplies all strict denominators. Every S-coordinate of every P-vertex is therefore at least -8rho, and convex averaging extends this to P. The exact centroid-dilation coordinate threshold is -u/n, so E(K,S)<=8nrho. This proves (2) and then (1).

## 5. Scope of the conclusion

The proof genuinely uses the number of K-vertices. It is not applicable to an arbitrary convex body merely because d+1 cap points were selected. In particular, it does not remove the unrestricted d versus d^2 gap.

It does show that any family witnessing a superlinear dimension coefficient through this near-vertex retention mechanism must have an unbounded number of vertices beyond d+1. A hypothetical rho comparable to 1/n and E comparable to n is incompatible with bounded r. More quantitatively, (1) would require r comparable to n in that regime.

The actual Entry005 corollary uses precisely the old H_d, original defect, and original-centroid affine transport, just as in the separate r=1 note. No new source package was compiled, and no external state was changed.
