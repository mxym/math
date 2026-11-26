# The ten-vertex Möbius ladder on nonnegative hosts of ordinary rank at most two

**Yongxian Zhang.** AI-assisted proof development and internal verification.

Let \(H=C_{10}+\{i(i+5):0\le i<5\}\), the ten-vertex Möbius ladder, equivalently \(K_{5,5}\) with a Hamilton cycle removed. Let \(W\) be a bounded nonnegative kernel on a product of probability spaces, with ordinary real operator rank at most two. For the side-preserving bipartite homomorphism density,
\[
t(H,W)\ge\bigl(\mathbb E W\bigr)^{15},
\]
with strict inequality unless \(W\) is constant almost everywhere. No symmetry or constant marginal condition is imposed. The theorem covers all kernels with at most two types on one side, and every finite rectangular weighted host matrix of ordinary real rank at most two, with arbitrary probability weights on both sides.

## Biregular kernels

First suppose both marginal integrals equal \(p=\mathbb E W>0\). In the respective orthogonal decompositions into constants and mean-zero functions, \(W\) acts as \(p\) on constants and maps mean-zero into mean-zero. Hence its mean-zero part has rank at most one and
\[
 W(x,y)=p(1+f(x)g(y)),\qquad \mathbb E f=\mathbb E g=0 .
\]
If the rank-one part is nonzero, both factors are nonzero and essentially bounded by boundedness of their product and Fubini. Set \(A=\mathbb E f^2,\ B=\mathbb E g^2,\ M=\mathbb E f^3,\ N=\mathbb E g^3,\ z=AB,\ w=MN\). Write the essential ranges of \(f,g\) as contained in \([-a,b]\), \([-c,d]\) using their essential endpoints. All four endpoints are positive in the nonconstant case, and nonnegativity requires \(ad,bc\le1\), by independence of the two variables and the definition of essential extrema. Also \(A\le ab,\ B\le cd\), by integrating the corresponding interval quadratics. Thus \(0<z\le1\).

Expand the edge product of the 15 factors \(1+fg\). The surviving edge subsets are precisely those eligible to be nonzero after removing any subset with a degree-one vertex. An edge subset contributes \(A^iM^j B^kN^\ell\) if its two sides have \(i,k\) vertices of degree two and \(j,\ell\) of degree three. The exact small enumeration is in the [replay](verify_mobius_ladder_rank_two.js). Its balanced part, where \(i=k,j=\ell\), minus the empty subset, is
\[
\begin{aligned}
 &5z^2+15z^3+30z^4+13z^5\\
 &+(5z^2+60z^3+95z^4)w+
 (15z^2+145z^3)w^2+75z^2w^3+15z w^4+w^5 .
\end{aligned}
\]
The other terms come from the following tuple pairs, with each tuple appearing at the indicated multiplicity:
\[
(0432,3204):5,\quad(1240,4012):5,\quad
(1341,4113):30,\quad(2250,5022):35 .
\]
Here a four-digit string stands for \((i,j,k,\ell)\); on each side degrees sum to the number of selected edges. If \(w\ge0\) all terms are nonnegative since \(j,\ell\) have equal parity, and the \(5z^2\) term is positive.

If \(w<0\), reverse signs of both factors so that \(M>0\), \(N<0\). Put \(u=-w\). From \(\mathbb E[(b-f)(f+A/b)^2]\ge0\) and its counterpart for \(-g\) with endpoint \(c\), obtain
\[
 M\le bA(1-A/b^2),\qquad -N\le cB(1-B/c^2).
\]
Both factors in parentheses are nonnegative. Their product is at most \((1-\sqrt z/(bc))^2\) by AM–GM. Since \(\sqrt z\le bc\le1\),
\[
 0<u\le z\,bc(1-\sqrt z/(bc))^2
 \le z(1-\sqrt z)^2\le 1/16 .
\]
In particular \(u\le z\). Among the unbalanced terms only the two with coefficient 30 are negative. Bundle them with the corresponding coefficient-35 terms \(2250\) and \(5022\): their coefficients after extracting \(A B^4 M^2\) and \(A^4 B N^2\), respectively, are \(30w+35z\ge0\). The other unbalanced terms are nonnegative. Dropping all positive even powers of \(w\) from the balanced part and using \(u^5\le z^2u^3\) gives the lower bound
\[
 (5-5u-76u^3)z^2+(15-60u)z^3+(30-95u)z^4+13z^5>0
\]
as each coefficient is positive for \(0\le u\le1/16\). This proves strictness in the nonconstant biregular case.

## Rank-preserving regularization

For a finite weighted nonnegative host \(W\), with weights \(\mu_x,\nu_y\), maximize
\[
 M_0=\sum_{x,y}\mu_x\nu_y\,W_{xy}a_x^2 b_y^2
 \quad\text{subject to}\quad a,b\ge0,\quad
 \sum_x\mu_x a_x^3=\sum_y\nu_y b_y^3=1.
\]
Discard zero original weights. The feasible sets are compact, and \(M_0\ge p\) by choosing \(a=b=1\). If \(p=0\) the nonnegative host is zero. Otherwise, maximizing over \(a^2\) with \(b\) fixed is the \(L^{3/2}\) versus \(L^3\) duality equality case, giving
\(\sum_y\nu_y W_{xy}b_y^2=M_0 a_x\) on \(a_x>0\); the analogous column equality holds on \(b_y>0\). Define new probability weights \(\mu_x'=\mu_x a_x^3,\ \nu_y'=\nu_y b_y^3\) on these positive supports, and \(V_{xy}=W_{xy}/(a_xb_y)\) there. Its marginal integrals are both \(M_0\), and its rank is at most that of \(W\) since only restriction and invertible diagonal rescaling were used. As every vertex of \(H\) has degree three, the measure factors cancel exactly in the density:
\[
 t(H,V;\mu',\nu')=
 \sum_{\text{assignments into positive supports}}\!
 \left(\prod_{\text{vertices}}\text{original weight}\right)
 \left(\prod_{\text{edges}}W_{xy}\right)\le t(H,W;\mu,\nu).
\]
The biregular case now gives \(t(H,W)\ge M_0^{15}\ge p^{15}\). Moreover, if either original marginal is nonconstant, taking the other scaling uniformly one and using strict \(L^3\) versus \(L^1\) gives \(M_0>p\). Otherwise the original host is already biregular and the strict polynomial argument applies.

For a bounded rank-two kernel on general probability spaces, approximate in \(L^1\) by conditional expectations on increasing finite rectangular partitions, which do not increase rank (projection on each side). Such approximants exist by simple rectangle approximation, or by approximating the finitely many functions in a separated representation of \(W\). The densities converge by telescoping the bounded edge product. If either marginal is nonconstant, first choose a finite partition of that side on which its conditional expectation is nonconstant; the same admissible scaling giving \(M_0>p\) is then available on all refinements. Its strict gap persists in the limit. If both marginals are constant use the direct rank-one expansion.

The scaling step works with \(3\) replaced by any common pattern degree above one, and preserves the host's rank. General reductions to biregular hosts precede this application, e.g. [Coregliano–Razborov](https://www.ias.edu/sites/default/files/CoRa21.pdf); the point here is an exact rank-preserving reduction specialized to the rank-bound problem, not a priority claim about regularization.

## Unlimited rank under two reflection symmetries

There is also a separate sufficient condition for all subcubic bipartite patterns. Suppose a bounded nonnegative kernel has the form \(W=p+U\), and on each probability space there is a measure-preserving involution negating \(U\) in that variable while the other variable is fixed, almost everywhere. Both marginals of \(U\) vanish. Expand the homomorphism density in the edges carrying \(U\). A term having a vertex of odd degree in the selected subgraph is zero by the involution in that variable. Since the pattern is subcubic, the remaining nonempty terms consist of disjoint even cycles. A \(2j\)-cycle contributes \(\operatorname{tr}((T_U^*T_U)^j)\ge0\), where \(T_U\) is the kernel operator; this is strictly positive for any nonzero \(U\). All other edge factors are \(p\ge0\). Thus the Sidorenko inequality follows, strictly for a nonconstant kernel when the pattern has a cycle; no operator-rank bound is needed under this reflection hypothesis.

One such involution suffices for any subcubic bipartite pattern with at most five vertices on the side having the involution, including the ladder. Assume the left variable has the involution and both marginals of \(U\) vanish. In the expansion left degrees can only be zero or two, and right degree one also gives zero by centering. Integrate out each selected degree-two left vertex by replacing it with an edge between its two right neighbors, carrying the PSD kernel \(K=T_U^*T_U\). The resulting loopless multigraph has at most five edges (there were only five left vertices) and positive degrees two or three. Thus it has at most two degree-three vertices. Apart from cycles, its only possible components after suppressing degree-two paths are a theta or a dumbbell (the two degree-three vertices either have three paths joining them, or one joining path and one cycle at each endpoint). Parallel edges are allowed. A theta contributes the integral of the pointwise product of three kernels \(K^{\ell_1},K^{\ell_2},K^{\ell_3}\) for the three path lengths. This is nonnegative, since an entrywise product of PSD kernels is PSD, which follows by tensoring Gram features. A dumbbell must have two length-two cycles and a length-one joining path to fit five edges. Its contribution is \(\langle F,KF\rangle\ge0\), with \(F(x)=\int K(x,y)^2\,dy\) on the right space (measure understood). Cycles also contribute nonnegative traces of powers of \(K\); the ladder's four-cycles give strictness for \(U\ne0\). This strengthens the preceding sufficient condition for this class of small patterns.

## Scope

The unrestricted Möbius-ladder inequality is not proved. See the [Möbius-ladder manuscript](https://users.cs.duke.edu/~br148/sidorenko-mobius.pdf) for its status as a small test graph, [Conlon–Lee](https://www.its.caltech.edu/~dconlon/Holder.pdf) for positive blow-up results, and [OpenAI family 161](https://github.com/openai/math/blob/main/lean/docs/161.md) for a distinct 35-vertex pattern that refutes the universal Sidorenko conjecture. Neither an unrestricted result for this ladder nor a claim of exhaustive priority is made here.
