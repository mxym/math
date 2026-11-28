# Residual-fiber obstructions for a rank-five thirteen-column linear C7 code

Let \(H\) be a rank-five matrix with thirteen columns over \(\mathbb F_7\), and put \(D=\{0,1,-1\}\subset\mathbb F_7\). Call \(H\) **dissociated** if \(\ker H\cap D^{13}=\{0\}\). Equivalently, its binary subset sums are all distinct, and its kernel is a linear independent set in \(C_7^{\boxtimes13}\).

**Theorem.** In a dissociated \(H\), a rank-three subspace contains at most **five** columns, and a rank-four subspace at most **eight** columns. If a rank-four subspace contains eight, then in the quotient line its five complementary columns have one of the absolute-residue multisets
\[
     (1,1,1,2,3),\qquad (1,1,2,2,3),
\]
up to nonzero rescaling of the whole line and individual signs. Here absolute residue means \(\min(a,7-a)\) for the integer representative \(0\le a<7\). These are necessary forms, not realizability assertions.

This replaces the caps six and nine in the previous [rank-five separator note](https://github.com/mxym/math/blob/146c850425759b23999e4bb2135c2c0f9455be83/research/euclidean-tensor-geometry/theoretical-cryptography/C7RankFiveSeparatorObstruction.md). Combined with the earlier rank-one and rank-two bounds the proper-flat caps are \(1,4,5,8\). The present proof of the improved caps does not rely on the earlier internal 4-connectivity computation. It does not exclude all rank-five thirteen-column systems and does not settle either linear or general Shannon capacity. [Guruswami–Riazanov](https://arxiv.org/abs/2009.05685) treat linear capacity via finite-field polynomial bounds; [Polak–Schrijver](https://arxiv.org/abs/1808.07438) give a lower bound from a general independent-set construction, not a flat obstruction.

## 1. A fiber bound for the separator

Partition the columns into \(X,Y\), with matrix maps \(H_X,H_Y\). Set \(U=\operatorname{span}X\), \(V=\operatorname{span}Y\), \(r=\dim U\), \(W=U\cap V\) and \(\delta=\dim W\). Write \(G_Y\) for the Cayley graph on \(W\) whose connection set is the nonzero values \(H_Y d\in W\) with \(d\in D^Y\). With \(t=\vartheta(C_7)=7\cos(\pi/7)/(1+\cos(\pi/7))\), one has
\[
             7^{|X|-r}\,\vartheta(\overline{G_Y})\ \le\ t^{|X|}.             \tag{1}
\]
Indeed, the map \(a\mapsto(a,H_Xa)\) on \(H_X^{-1}(W)\) is an independent-set embedding into \(C_7^{\boxtimes |X|}\boxtimes G_Y\). If distinct images were confusable, the \(X\)-difference would be a nonzero member of \(D^X\) with syndrome a signed \(Y\)-sum (or zero). This contradicts dissociation. The domain has size \(7^{|X|-r+\delta}\); multiplicativity of theta and the vertex-transitive identity \(\vartheta(G_Y)\vartheta(\overline{G_Y})=7^\delta\) yield (1). Both facts are from [Lovász](https://doi.org/10.1109/TIT.1979.1055985).

In particular, if \(k\) binary sums of \(Y\) agree after projection modulo \(U\), then \(k\) distinct points form a clique in \(G_Y\): subtract their common-fiber basepoint, and all differences are \(Y\)-signed sums in \(W\). Thus \(k\,7^{|X|-r}\le t^{|X|}\). This is valid for any column partition and needs no enumeration. If \(r=4\) and \(|X|=9\), the four remaining columns have a fiber of at least \(\lceil16/7\rceil=3\), but \(3\cdot7^5>t^9\). If a rank-four subspace contained more than nine, one could still take a nine-column subset containing a rank-four basis. This proves the cap eight.

## 2. Working in the kernel of the projected column map

Represent the projection of \(H_Y\) modulo \(U\) by \(Q:\mathbb F_7^{Y}\to\mathbb F_7^{5-r}\). It is onto, since the full configuration spans five dimensions. Put \(L=\ker Q\), \(K=\ker H_Y\subseteq L\), and \(S=L\cap(D^Y\setminus\{0\})\). Then \(H_Y:L\to W\) is onto, \(W\simeq L/K\), and \(G_Y\) is the Cayley graph with connection set the image of \(S\) in \(L/K\). Dissociation gives \(K\cap S=\varnothing\).

We use the complement side of the Fourier theta formulation of [DeCorte–de Laat–Vallentin](https://arxiv.org/abs/1307.5703). A real even function \(f\) on \(L/K\) supported on \(\{0\}\) and the image of \(S\), with \(f(0)=1\) and nonnegative Fourier transform, certifies
\[
                        \vartheta(\overline{G_Y})\ \ge\ \sum_x f(x).
\]
In detail, the matrix with entries \(f(x-y)/|L/K|\) is positive semidefinite by Fourier diagonalization, has trace one and vanishes on the edges of the complement. Its all-entries sum is the right-hand side.

We can even certify on \(L/K_0\) for \(K_0\subseteq K\). Sum \(f\) over the fibers of the natural quotient to define \(f'\) on \(L/K\). The normalization survives because \(K\cap S=\varnothing\), the support projects into the allowed support, the Fourier transform is restricted to the characters of \(L/K\), and the total sum is unchanged. Collisions among nonzero images are allowed. This lets us test only the smallest possible kernel dimension.

## 3. Rank three

Suppose \(X\) has six columns and rank three. Inequality (1) allows no projected binary-sum fiber with four points because \(4\cdot7^3>t^6\). Projected \(Y\) has seven columns of rank two. Normalize two independent columns to \(e_1,e_2\); the other five are a multiset of the \(25\) sign-representatives of \(\mathbb F_7^2\), including zero. A sign change translates the list of binary sums and preserves all fiber sizes. The exact [checker](verify_c7_rank_five_residual_fibers.py) checks \(\binom{29}{5}=118755\) cases using the recurrence \(c_{\rm new}(a)=c(a)+c(a-v)\). There are exactly 72 with maximum fiber at most three; changing basis, signs and column order puts them all in the single form
\[
              Q=((1,0),(0,1),(0,2),(1,1),(2,4),(3,0),(3,3)).
\]
For the equivalence check, the canonical form is the lexicographically least sorted list of sign-representatives over all ordered independent pairs of signed columns mapped to \(e_1,e_2\). This rule is invariant under the allowed equivalences and can be used without enumerating arbitrary ordered bases of the ambient space.

Use the last five coordinates of \(L\cong\mathbb F_7^5\) as free coordinates. A free tuple \(z\in D^5\) belongs to \(S\) precisely if \(z\ne0\) and the two forced coordinates of \(Q\)'s kernel also lie in \(D\). This gives 44 elements, or 22 sign-pairs. Since \(H_Y\) has rank at most five on seven columns, \(\dim K\ge2\). Take any two-dimensional subspace \(K_0\subseteq K\), still disjoint from \(S\). For each of the 140050 two-dimensional subspaces of \(L\), the checker enumerates its unique two-row reduced row echelon form, forming \(L/K_0\cong\mathbb F_7^3\) by subtracting pivot multiples and retaining the three nonpivot coordinates. Exactly 131469 subspaces avoid \(S\). The residual Cayley graph on this three-dimensional quotient either has a four-clique (the checker searches for one containing zero, by translation), or admits a nonnegative rational Fourier witness with objective at least \(39/10\). There are 1498 cases of the latter kind; each is checked. Descent of the witness now contradicts (1) because \((39/10)7^3>t^6\). If a rank-three subspace contains at least six columns, take six containing a rank-three basis, so this proves the full cap.

## 4. Eight in rank four

If \(X\) has eight columns and rank four, the five columns in \(Y\) project to a line with binary-sum fibers of size at most six, as \(7\cdot7^4>t^8\). Normalize one nonzero projected column to \(1\), then enumerate the four remaining residues up to sign and order. Rescaling the line and reordering gives precisely the six multisets
\[
 (0,1,1,2,3),\ (1,1,1,2,3),\ (1,1,2,2,3),\
 (0,1,1,1,3),\ (1,1,1,1,3),\ (1,1,1,3,3).
\]
For four of the six, the checker certifies \(\vartheta(\overline{G_Y})\ge 3057/500\), already on \(L\cong\mathbb F_7^4\) with \(K_0=\{0\}\). The support is obtained by checking the forced first coordinate against \(D\), just as above. Descent to \(L/K\) then contradicts (1) because \((3057/500)7^4>t^8\). The two remaining multisets are exactly the displayed necessary forms. In particular, no claim is made that a larger Fourier certificate for either remaining form is impossible.

## 5. Exact verification

Run the [standalone Python 3 checker](verify_c7_rank_five_residual_fibers.py) next to its [certificate](c7_rank_five_residual_fiber_certificate.json):

    python3 verify_c7_rank_five_residual_fibers.py

It uses only the standard library, and does not run an LP solver or evaluate cosines. For each signed support representative it reads a nonnegative weight (adding weights if quotient images coincide). If the numerators are \(w_j\) with denominator \(d\), it checks the objective \(1+2\sum_j w_j/d\) and the signed Fourier constraints
\[
        1+\sum_j (w_j/d)\,2\cos(2\pi\,u\cdot s_j/7)\ \ge\ 0
\]
using integer lower bounds at denominator \(10^9\). The three distinct nontrivial doubled cosines, in descending order, are the real roots of \(x^3+x^2-2x-1\): substitute \(x=\zeta+\zeta^{-1}\) and use \(1+\sum_{j=1}^3(\zeta^j+\zeta^{-j})=0\). The code checks sign changes in three disjoint ordered rational intervals of width \(10^{-9}\), so the lower endpoints are certified. It checks \(t<331767/100000\) using \(\cos^2(\pi/7)=(2+2\cos(2\pi/7))/4\), and all strict comparisons in (1) by rational arithmetic.

The eight compressed rank-three arrays encode sequential lists of 22 unsigned little-endian 16-bit numerators per witness, with denominator 1000. The first seven arrays correspond to the first free echelon entry for pivot pair \((0,1)\); the eighth covers other pivot pairs. They are consumed only when a subspace avoids \(S\) and its residual graph lacks a four-clique, in lexicographic echelon enumeration order. The four uncompressed rank-four arrays have denominator \(10^6\) and are keyed by the reordered projection tuple with first coordinate one. All supports are independently reconstructed by the checker. Numerical optimization was used only to find these rational vectors, not in their verification.
