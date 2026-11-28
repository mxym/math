# Weighted rank-one cases of the four-factor Duchi inequality

Research note, 28 November 2026. On a finite-dimensional real or complex Hilbert space define
\[
 R=4^{-4}\sum_{i,j,k,l=1}^4\|A_iA_jA_kA_l\|,\qquad
 S=(4!)^{-1}\sum_{i,j,k,l\ \mathrm{distinct}}\|A_iA_jA_kA_l\|,
 \qquad D=\tfrac14\sum_{i=1}^4\|A_i^4\|,
\]
using the operator norm. We prove two cases allowing different scalar weights on the different labels.

1. Let \(A_i=w_iP_i\) with \(w_i\ge0\) and \(P_i\) rank-one orthogonal projections. If every pair overlap \(\|P_iP_j\|\) for \(i\ne j\) is at most
\[
                     \beta_*=(14+4\sqrt{46})/45,
\]
then \(R-S\ge(D-S)/64\ge0\), and \(1/64\) is sharp in this class. The proof works even for arbitrary abstract symmetric overlap data in \([0,\beta_*]\), without requiring that they are Gram magnitudes.

2. Let \(A_1,A_2,A_3\) be arbitrary rank-at-most-one PSD matrices, and \(A_4\) a PSD matrix commuting with each of them. Then \(R\ge S\), with equality only when all matrices vanish, or when \(A_1=A_2=A_3=tP\) for some \(t>0\) and rank-one projection \(P\) and \(A_4\) has norm \(t\) and eigenvalue \(t\) on \(\operatorname{Ran}P\). There is no overlap upper bound in this case.

These are restricted cases of the expected-product-norm comparison in [Duchi's COLT commentary, equations (2)–(3)](https://proceedings.mlr.press/v23/duchi12/duchi12.pdf), not the different Recht–Ré comparison of norms *after* averaging the matrices. The [preceding four-projection note](DuchiFourProjectionInequality.md) allows arbitrary ranks but requires a common scalar per commuting block. The hypotheses here are different; we make no claim for arbitrary four PSD matrices.

## 1. Four differently weighted lines with bounded overlaps

Write \(r_{ij}=\|P_iP_j\|\) for \(i\ne j\) and \(r_{ii}=1\). For each word its norm is exactly the product of all its weights times the overlaps at successive transitions. If \(W=\prod_i w_i=0\), then \(S=0\) and the four constant words alone give \(256R\ge4D\). Assume \(W>0\), and throughout this section divide every word sum by \(W\).

There are three perfect matchings \(M_1,M_2,M_3\) on the four labels. Define \(x_i=ab,\ u_i=\sqrt{x_i},\ s_i=a+b\), where \(a,b\) are the two edge overlaps for \(M_i\). Let \(B_i=\sum_{j\ne i}s_j\). An unoriented Hamilton path with matching \(M_i\) as its two outer edges chooses one of the four remaining edges as the middle edge. Thus
\[
                               S/W=\frac1{12}\sum_i x_iB_i .
 \tag{1}
\]
Write \(P_2,P_3\) for the normalized sum of all words using respectively two and three distinct labels, which have lengths four and include repetitions. We prove \(P_2+P_3\ge228S/W\).

**Two labels.** A pair with overlap \(r\) contributes \(2(r+r^2)(w_i^3w_j+w_j^3w_i)\) and \(2(r+r^2+r^3)w_i^2w_j^2\) before normalization. Indeed a letter appearing once has two endpoint and two interior placements, and the two-plus-two words give two of each of the one-, two-, and three-transition types. This sum is at least \(w_i^2w_j^2 f(r)\) where \(f(r)=6r+6r^2+2r^3\). Pair it with the complementary label pair by AM–GM. Matching \(M_i\) then contributes at least \(2\sqrt{f(a)f(b)}\), in normalized units. Cauchy–Schwarz applied to the three positive coefficients of \(6+6r+2r^2\) gives
\[
 P_2\ge \sum_i(12u_i+12u_i^2+4u_i^3)
 \ge(12/\beta+12+4\beta)\sum_i x_i,                        \tag{2}
\]
when all overlaps are at most \(\beta\le1\). The latter follows from \(u_i\le\beta\), since \(12/u+12+4u\) is decreasing on \((0,1]\).

**Three labels.** Fix the repeated label \(i\), the missing label \(l\), and the other labels \(j,k\). Put \(a=r_{ij}, b=r_{ik}, c=r_{jk}\). The 12 words with this multiset have total coefficient
\[
                   U_i=2(ab+ac+bc+a^2b+ab^2+abc)
\]
multiplying \(Ww_i/w_l\): six words collapse the adjacent repeated pair, four are backtracks, and two are triangles. Swap \(i\) and \(l\), and put \(a'=r_{lj},b'=r_{lk}\). AM–GM gives normalized contribution at least \(2\sqrt{U_iU_l}\) for this unordered pair of repeated/missing labels. In the two lists of six monomials, match \(ac\) to \(b'c\), \(bc\) to \(a'c\), \(ab\) to \(a'b'\), \(a^2b\) to \(a'b'^2\), \(ab^2\) to \(a'^2b'\), and \(abc\) to \(a'b'c\). By Cauchy–Schwarz, with \(u=\sqrt{ab'}\), \(v=\sqrt{ba'}\),
\[
             2\sqrt{U_iU_l}\ge4[c(u+v)+(1+c)uv+u^2v+uv^2].
\]
Here \(u,v\) correspond to the two matchings not containing both \(il,jk\). For fixed matching \(M_t=\{il,jk\}\), the two unordered choices of repeated/missing label pair produce the same \(u,v\) and their \(c\)'s add to \(s_t\). Therefore, using \(u_i\ge x_i/\beta\) and \(s_i\ge2u_i\),
\[
 P_3 \ge \frac4\beta\sum_i x_i B_i
       +\left(\frac8{\beta^2}+\frac{16}{\beta}\right)\sum_{i<j}x_ix_j
       +\frac{24}{\beta^3}x_1x_2x_3 .                    \tag{3}
\]

Choose \(\beta=\beta_*\), so \(d=19-4/\beta>0\). Since each matching's two overlaps \(a,b\) are at most \(\beta\), \((\beta-a)(\beta-b)\ge0\) implies \(s_i\le\beta+x_i/\beta\). Thus \(\sum_i x_i B_i\le 2\beta\sum_i x_i+(2/\beta)\sum_{i<j}x_ix_j\). From (1)–(3), it remains to check the nonnegativity on \(0\le x_i\le\beta^2\) of
\[
 (\tfrac{12}{\beta}+20-34\beta)\sum_i x_i
 +(\tfrac{16}{\beta^2}-\tfrac{22}{\beta})\sum_{i<j}x_ix_j
 +\tfrac{24}{\beta^3}x_1x_2x_3 .
 \tag{4}
\]
It is affine in each variable. At a vertex with \(0,1,2,3\) nonzero coordinates, the value divided by \(\beta^2\) is respectively
\[
 0,\quad
 12/\beta+20-34\beta,\quad
 24/\beta+56-90\beta,\quad
 36/\beta+108-144\beta .
\]
The characteristic equation \(90\beta^2-56\beta-24=0\) makes the third entry zero. The second is \(11\beta-8>0\), and the fourth is positive since \(\beta<1\). This proves (4). Adding the 24 distinct words and the four constant words now gives \(256R\ge 252S+4D\). Since \(S\le W\le D\) by elementary AM–GM, the first claim follows. Four mutually orthogonal nonzero lines have \(R=D/64,S=0\), proving sharpness.

## 2. One scalar and three arbitrary weighted lines

First take \(A_4=tI\) with \(t\ge0\), and \(A_i=w_iP_i\) for \(1\le i\le3\). Write \(S_3\) for the without-replacement average norm of length three among the first three operators, \(D_3=\tfrac13\sum_i w_i^3\), and \(f_\ell\) for their with-replacement average at length \(\ell\), \(f_0=1\). Then \(S=tS_3\) and counting positions of \(tI\) gives
\[
               256R=81 f_4+108t f_3+54t^2 f_2+12t^3 f_1+t^4.
 \tag{5}
\]
If \(tS_3=0\) then the desired nonnegative difference is immediate, and equality can only hold when all operators vanish because of the constant words. Otherwise all three weights are positive.

The length-three comparison has a quantitative form in this model:
\[
                      f_3\ge (8S_3+D_3)/9.              \tag{6}
\]
Indeed the distinct words contribute \(6S_3\) to \(27f_3\), and the constant words contribute \(3D_3\). For the two-label words, divide their sum by \(W_3=w_1w_2w_3\). With \(r_k\) the overlap of the two labels other than \(k\), that contribution is
\[
       \sum_{i\ne k}(w_i/w_k)(2r_k+r_k^2).
\]
Pair \((i,k)\) with \((k,i)\) by AM–GM and use \(2r+r^2\ge3r^2\) on \([0,1]\). This gives at least \(6\sum_{i<k}r_i r_k=18S_3/W_3\). Inserting the three contributions gives (6).

There is also a positive moment law for all \(f_\ell,\ell\ge1\). The symmetric matrix \(K=(r_{ij})_{1\le i,j\le3}\) of absolute Gram entries is PSD: its \(1\)- and \(2\)-row principal minors are nonnegative, and its determinant is at least that of the actual Gram matrix since the real part of a product is at most its magnitude. Put \(M=\operatorname{diag}(\sqrt{w_i})K\operatorname{diag}(\sqrt{w_i})/3\), and let \(\nu\) be its spectral probability law seen from the unit vector proportional to \((\sqrt{w_i})_i\). Then
\[
                  f_\ell=f_1\int z^{\ell-1}\,d\nu(z)
                  \quad(\ell\ge1),\qquad \operatorname{supp}\nu\subset[0,\infty).
 \tag{7}
\]
The matrix product expansion is exactly the path expression for rank-one norms. This step uses absolute Gram positivity only for three lines, not for general absolute Gram matrices.

Use homogeneity to normalize \(S_3=1\), and put \(u=f_1\ge1\), since \(S_3\le W_3\le u^3\). By Jensen and (6), \(f_3\ge A=(8+u^3)/9\). In (7) this says \(\int z^2\,d\nu\ge A/u\). For
\[
             g(x)=81 x^{3/2}+108t x+54t^2\sqrt{x}
\]
a nondecreasing convex minorant is \(g\) on \(x\ge (2/3)t^2\), joined to zero below that point by a line of slope \((108+54\sqrt6)t\). This follows by minimizing \(g(x)/x\), which gives the positive tangent at \((2/3)t^2\), and checking \(g''>0\) thereafter. Apply Jensen for the minorant at \(\int z^2\,d\nu\), and use monotonicity to substitute \(A/u\).

Set \(v=t\sqrt{u/A}\). If \(v^2\le3/2\), equations (5)–(7), divided by \(t>0\), give
\[
 256R/t \ge A G(v)+(A/u)^{3/2}v^3,\qquad
 G(v)=81/v+108+54v+12v^2.
\]
Here \(G(v)+v^3=(3+v)^4/v\ge256\), \(G(v)>240\), \(A-1\ge(u-1)/3\), and \((A/u)^{3/2}-1\ge u^{-3/2}-1\ge-\tfrac32(u-1)\). Since \(v^3<2\), we conclude \(256R/t\ge256+77(u-1)\). If \(v^2\ge3/2\), the minorant is linear instead, giving \(256R/t\ge A(108+54\sqrt6+12v^2)>258A\), which also suffices. Undoing normalization proves the quantitative estimate
\[
 R-S\ \ge\ \frac{77}{256}\,t\, S_3^{2/3}\big(f_1-S_3^{1/3}\big).
 \tag{8}
\]

If \(R=S>0\), (8) requires the normalized \(u=1\). Thus all weights are one by equality in \(1=S_3\le W_3\le u^3=1\), and all overlaps are one by equality in \(S_3\le W_3\). Now \(R=(3+t)^4/256\) and \(S=t\); equality requires \(t=1\). Undoing normalization gives \(A_1=A_2=A_3=tP\).

Finally let \(A_4\) merely commute with the three rank-one operators. Each nonzero line lies in an eigenspace of \(A_4\). If a distinct word has positive norm, then all three line vectors lie in the same eigenspace: adjacent nonzero overlaps in the length-three product force equal eigenvalues by orthogonality of distinct eigenspaces, and \(A_4\) can be moved to the end. The common eigenvalue \(t\) is positive. Applying the scalar case on this eigenspace leaves \(S\) unchanged and can only decrease \(R\). Words involving any rank-one factor vanish on the orthogonal complement, so the only possible extra gain in \(R\) is from the all-\(A_4\) word, which is strict exactly when \(\|A_4\|>t\). Conversely, under the stated common-line and norm conditions, every word has norm \(t^4\), so equality indeed holds. This finishes the second case.

The [exact word checker](verify_factor_duchi_rank_one_scales.py) checks the finite multiplicities and rational overlap test cases without using numerical matrices. The inequalities on the continuous domains are established by the proof above, not the tests.
