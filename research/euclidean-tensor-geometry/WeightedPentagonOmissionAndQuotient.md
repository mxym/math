# Omission-cut certificates and exact weighted pentagon ranks

**Yongxian Zhang.** AI-assisted proof development and independent internal checks; no external peer review claimed.

For a weighted odd cycle, an *omission cut* alternates around the cycle except for one omitted edge. We optimize their weighted mixtures and characterize when the resulting point optimizes both of [Zhou's path-strengthened conic bounds](https://arxiv.org/html/2610.34273v3#S6.SS3). For a pentagon this gives a test in the five individual weights and actual exact rank regimes. None of the results settles the unweighted pentagon.

## 1. The omission cone for any odd cycle

Index edge \(i\) by its endpoints \(i,i+1\), indices cyclic. Write \(W=\sum_i w_i>0\), \(f_i=W-w_i\), \(F_0=\max_i f_i\). Let \(s_i\) be the omission cut's sign vector oriented to have sum one, and \(S\) have columns \(s_i\). Taking adjacent vertex sums sends \(s_i\) to \(2e_i\), so \(S\) is invertible; also \(S\mathbf1=\mathbf1\) by rotation. For \(P=\sum_i\lambda_i(J-s_i s_i^\mathsf T)/2\), \(\lambda_i\ge0\), \(M=\sum_i\lambda_i\), the triangle inequalities hold and
\[
J-2P=S[\operatorname{diag}(\lambda)-(M-1)\mathbf1\mathbf1^\mathsf T]S^\mathsf T .
\]
For \(M\le1\) this is PSD. For \(M>1\) it is PSD exactly if all \(\lambda_i>0\) and \((M-1)\sum_i1/\lambda_i\le1\), by Cauchy–Schwarz and its equality vector.

If \(\sum_i\sqrt{1-f_i/F_0}\ge1\), the best SDP objective inside this cone is \(F_0\), attained by a maximal omission cut. Otherwise it is the unique \(F>F_0\) with \(\sum_i\sqrt{1-f_i/F}=1\); existence and uniqueness follow from continuity and strict increase until the limit given by the number of edges. To see the upper bound in either regime, set \(b_i=\sqrt{1-f_i/F}\) with \(F\) as specified. If \(M>1\) then
\[
\sum_i\lambda_i b_i^2\ \ge\ \frac{(\sum_i b_i)^2}{\sum_i1/\lambda_i}\ \ge\ M-1.
\]
Thus \(\sum_i\lambda_i f_i\le F\); if \(M\le1\) this is immediate. For \(F>F_0\), writing \(Z=\sum_i1/b_i\), the weights \(\lambda_i=1/[b_i(Z-1)]\) attain \(F\) and have a corank-one matrix \(J-2P\). In fact \(a_i=(b_{i-1}+b_i)/2>0\) satisfies \(S^\mathsf T a=b\), \(\sum_i a_i=1\), and \((J-2P)a=0\). The first identity uses the adjacent-sum formula. All off-diagonal entries \(p_{ij}\) are strictly positive: along a proper interval between \(i,j\), parity under the cut is reversed by whether or not the omission lies in that interval, and both choices occur.

## 2. When does this solve the full conic programs?

In the active case \(F>F_0\), put \(K=1/(4F)\), \(Q=\sum_{i<j}a_i a_j p_{ij}\), and \(D=Q-K\sum_i w_i p_{i,i+1}\). It vanishes on every omission cut: evaluating \(Q\) on that cut gives \((1-b_i^2)/4=K f_i\). The omission value is the full SDP optimum if and only if \(D\) is a nonnegative combination of triangle inequalities tight on every omission cut. If it is, the same value also solves CP, since copositivity tested on \(a\) gives \(Q\le1/4\).

For necessity, the SDP has a strictly feasible point: take sufficiently small positive constant off-diagonal entries, then \(J-2P\) is positive definite and every triangle has positive slack. Thus an optimal candidate has a complementary optimal dual certificate. Because its positive-semidefinite matrix has one-dimensional kernel spanned by \(a\), the PSD multiplier is a scalar multiple of \(aa^{\mathsf T}\); the nonnegativity constraints are inactive because all off-diagonal entries are positive. Only the common tight triangles can occur since every omission cut has positive coefficient in \(P\). Consequently the objective functional is proportional to \(Q\) modulo the common tight triangles. Evaluating on an omission cut with \(f_i>0\) fixes the proportionality from \(Q=K f_i\), proving the test. If it fails, the SDP and hence CP strictly exceed the omission value. This necessity is for the active branch, not the boundary where an optimal omission may be a single cut.

## 3. Explicit five-weight test and two-edge evaluations

For a pentagon the only triangle inequalities tight on every omission cut are
\[
T_i=p_{i+1,i+3}+p_{i+3,i}-p_{i,i+1}\ge0.
\]
Indeed a triangle partitions the cycle into arcs of lengths \((1,2,2)\) or \((1,1,3)\). In the first case, the vertex between the two even arcs cannot be isolated by an omission cut (both those arcs would need to contain the omission), and either other vertex can be isolated. In the second case each vertex can be isolated by omitting in the opposite arc. This gives exactly the list. The five \(T_i\) are independent because their edge coefficients are \(-1\) on separate edges; so are the five omission cuts because their edge-coordinate matrix is \(J-I\). Thus \(D=\sum_i u_i T_i\), with \(u_i=K w_i-a_i a_{i+1}\). If \(B=\sum_{j<k} b_jb_k\), one has \(4K w_i=b_i^2+B/2\) from \(\sum b_i=1\) and \(b_i^2=1-f_i/F\). Consequently \(u_i\ge0\) exactly when the three pair products of the consecutive triple \((b_{i-1},b_i,b_{i+1})\) sum to at most \(B/2\).

For two edges of weight \(t\) and three unit edges let the unnormalized \(b_i\) be \(x\) at the two distinguished edges and one elsewhere. Substitution yields
\[
 t=3(x+1)/(x+5),\qquad F=(7t+3)^2/(24t).
\]
For separated distinguished edges, consecutive triples have one or two \(x\)'s. Their pair sums are \(2x+1\) and \(x^2+2x\); with \(B=x^2+6x+3\), the first inequality always holds for \(x\ge0\), and the second is equivalent to \(x\le3\). For adjacent distinguished edges the additional all-one triple requires \(x\ge2\sqrt3-3\). Therefore the displayed formula is the exact CP and SDP value:
- for the separated case, \(3/5<t\le3/2\);
- for the adjacent case, \(6-3\sqrt3\le t\le3/2\).

In the separated case it extends by continuity to \(t=3/5\), where \(F=18/5=3+t\). At \(t=0\), the upper value is at most 3 since the two-coordinate copositive tests give \(p_{ij}\le1\), and a cut crosses the three unit edges. Convexity of the conic values in the edge weights (support functions of fixed feasible sets) now gives an upper bound \(3+t\) on the whole interval. This is the maximum cut, since the omitted edge can have weight \(t\) and no cut crosses all five, so the **actual rank exponent is \(3+t\) for \(0\le t\le3/5\) over every field**. This part does not need any rectangular rank equality.

## 4. A different certificate: actual rank in the symmetric three-edge-path regime

Let the successive weights around the pentagon be \((r,1,r,s,s)\). Define \(z=\sqrt{2r+1}\). For
\[
 1\le z\le3,\qquad 0\le s\le \tfrac12 z(z-1)(3-z),
\]
both conic values equal \(2r+1+s+s^2/[4(2r+1)]\). Using the [pinned exact rectangular theorem](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/SpectralBooks/ExactExponent.lean#L45), this is also the actual rank exponent over every field. Rank equality in the active positive-\(s\) case uses that external lower bound; the conic equality does not.

For the upper bound, average \(P\) with its reversal \(0\leftrightarrow3,1\leftrightarrow2\), fixing 4. It suffices to use the resulting symmetric \(P\). Set
\[
 \alpha=p_{01}=p_{23},\quad \beta=p_{12},\quad c=p_{34}=p_{40},\quad
 d=p_{02}=p_{13},\quad e=p_{03},\quad f=p_{14}=p_{24}.
\]
Take the test vector \((u,1,1,u,g)\) with \(u=z-1,\ g=s/z\). The quadratic sum satisfies
\[
 Q=2u\alpha+\beta+2ug c+2u d+u^2 e+2g f
   \ \ge\ (2u+u^2)\alpha+\beta+2g(u+1)c+(2u-u^2-2g)d.
\]
Here \(e\ge\alpha-d\) and \(f\ge c-d\) by two triangle inequalities. Now \(2u+u^2=2r,\ g(u+1)=s\), and \(2u-u^2-2g=(z-1)(3-z)-2s/z\ge0\). Hence \(Q\ge2r\alpha+\beta+2sc\), the objective. Copositivity gives
\[
 Q\le (2u+2+g)^2/4=z^2+s+s^2/(4z^2).
\]

For the common matching lower bound, merge the independent sets \(\{0,2\}\), \(\{1,3\}\), leaving \(\{4\}\). The quotient is the triangle \((z^2,s,s)\). For the SDP lower bound, take the exact triangle SDP from Zhou Proposition 6.2 and repeat its three party vectors within the sets (repetition preserves PSD, nonnegativity and triangles). For the true rank lower bound, grouping parties cannot increase rank and the pinned rectangular theorem gives the same value: \(s\le z^2\) in the stated interval, and for \(s>0\) the correction is \(s^2/(4z^2)\). At \(s=0\), the crossing path already gives the result by a cut.

This yields two further pieces of **actual** rank:
- two adjacent edges of weight \(t\), three unit edges: take \(r=1,s=t\), so the rank exponent is \(3+t+t^2/12\) for \(0\le t\le 6-3\sqrt3\);
- two separated edges of weight \(t\), three unit edges: take \(r=t,s=1\), so the rank exponent is \(2t+2+1/[4(2t+1)]\) for \(3/2\le t\le1+\sqrt2\). The condition factors as \(z(z-1)(3-z)-2=-(z-2)(z^2-2z-1)\), and \(2\le z\le1+\sqrt2\) is precisely that interval.

Thus the exact two programs interpolate between different optimal faces; the cap in one face is not evidence that the true rank equals the conic value in the intervening range. In particular unweighted \(C_5\) remains unresolved.
