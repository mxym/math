# Short semibent tails and a spectrum-sensitive lower bound for quadratic APN maps

## Main result

Let \(F:\mathbb F_2^n\to\mathbb F_2^n\) be quadratic almost perfect nonlinear (APN), with \(n\ge4\) even. Let \(m\) be the number of nonzero semi-bent output masks, i.e. the number of scalar components of Walsh amplitude \(2^{n/2+1}\). Then \(m\ge n+1\). If no nonzero component has a polar radical of dimension greater than two, then \(m=(2^n-1)/3\).

Otherwise let \(d\ge4\) be the least radical dimension greater than two, and put
\[
 s=\frac{2^d-1}{3},\qquad \rho=\min\left(s-1,\binom d2\right).
\]
The following are necessary:
\[
\begin{array}{c|l}
\text{possible }m&\text{necessary condition}\\ \hline
s & n\le \rho;\ \text{the semi-bent radicals form a complete }2\text{-spread of one }d\text{-space},\\
2s & 2d\le n\le 2\rho;\ \text{they form two complete }2\text{-spreads in disjoint }d\text{-spaces},\\
m\ge 3s & \text{no additional condition claimed here}.
\end{array}
\]
Here and below disjoint subspaces meet only at zero. In particular the lower bound jumps to \(2s\) when \(n>\rho\), and to \(3s=2^d-1\) when additionally \(n>2\rho\) or \(n<2d\). These are necessary bounds, not realizability statements for the surviving spectra.

For instance, when \(d=6\) the old vector-partition tail minimum \(21\) is replaced by \(42\) for even \(16\le n\le30\), and by \(63\) for even \(32\le n\le60\) (above those ranges the same bounds still apply but \(n+1\) may match or exceed them). When \(d=8\), the corresponding improvements replace \(85\) by \(170\) for \(30\le n\le56\), and by \(255\) for \(58\le n\le252\). The exact parameter regimes in which the bound strictly improves \(\max(n+1,s)\) are:

- \(n>\rho,\ 2d\le n\le2\rho,\ n\le2s-2\), where the new term is \(2s\);
- \(n>\rho,\ (n>2\rho\text{ or }n<2d),\ n\le3s-2\), where the new term is \(3s\).

The comparisons use the displayed inequalities only for even \(n,d\) with \(4\le d\le n-2\). This is a spectrum-sensitive improvement for [Carlet–Thornburgh, Open Problem 5.16](https://arxiv.org/html/2608.23888v2), not an exact formula for the minimum as a function of \(n\) alone.

## 1. Alternating forms, the radical partition and the right-inverse tensor

Let \(V\) denote the input binary space and \(W\) the output binary space. Fix the bit dot product on each, so that masks may be written as vectors. The polar map
\[
 \beta(x,y)=F(x)+F(y)+F(x+y)+F(0)
\]
is alternating and bilinear. The APN hypothesis says that for \(x\ne0\), the derivative \(F(x+y)+F(y)\), as a function of \(y\), is exactly two-to-one on its image. Equivalently, \(\ker\beta(x,-)=\{0,x\}\). Thus its image is a hyperplane in \(W\). For each \(b\ne0\) let
\[
R_b=\{x:\langle b,\beta(x,y)\rangle=0\text{ for every }y\in V\}.
\]
Each nonzero input direction \(x\) lies in exactly one such \(R_b\), whose label \(b\) is the nonzero ortho-derivative value \(\pi_F(x)\). This gives a partition of the nonzero input vectors. The positive dimensions of the \(R_b\) are even, since scalar alternating ranks are even.

For a quadratic scalar component \(b\cdot F\), its amplitude is \(2^{(n+\dim R_b)/2}\). In fact, on squaring a Walsh coefficient the inner character sum over \(x\) is zero off \(R_b\) and is \(2^n\) times a sign on \(R_b\). The remaining phase is linear on \(R_b\) up to a constant with phase \(+1\) at zero. This gives squared values \(0\) or \(2^n |R_b|\); Parseval ensures at least one nonzero value. Consequently the set of semi-bent labels is \(B=\{b\ne0:\dim R_b=2\}\), with \(|B|=m\).

For a nonzero output \(v\), let \(\mathcal L_v\) be the set of input planes \(E\) of dimension two with \(\sum_{x\in E}F(x)=v\), and let \(m(v)=|\mathcal L_v|\). For each nonzero \(x\) with \(v\in\operatorname{im}\beta(x,-)\), the solutions to \(\beta(x,y)=v\) are \(y,y+x\), and determine one plane through \(x\) in \(\mathcal L_v\). Thus the planes in \(\mathcal L_v\) are pairwise disjoint, and their nonzero points are just the nonzero directions with \(v\cdot\pi_F(x)=0\).

In fact \(m(v)\) is odd. The indicator of \(\dim R_b=0\), evaluated at all \(b\in W\), has Boolean degree at most \(n/2\): the determinant of an alternating matrix at a binary mask is its Pfaffian. In the determinant expansion, a permutation with a cycle of length at least three cancels against the one reversing its first such cycle, and diagonal terms vanish. The remaining transpositions give the square of the matching sum, which equals that matching sum when evaluated over \(\mathbb F_2\). Its entries are linear in \(b\), so the matching sum has degree at most \(n/2\). Since \(n/2<n-1\), its restriction to the \((n-1)\)-space \(v^\perp\) has even weight. Among the \(2^{n-1}-1\) nonzero masks there, an odd number therefore have positive radical dimension. The union of those radicals' nonzero points is also odd, since each has odd size and the blocks are disjoint. This union has size \(3m(v)\), proving the claim.

For \(b\in B\) write \(s_b(u)=1_{u\notin R_b^\perp}\). For \(u\ne0\), let \(m_u(v)\) count the planes in \(\mathcal L_v\) contained in \(u^\perp\), and let \(m_0(v)=m(v)\). Any plane not contained in \(u^\perp\) has exactly two points outside it. Counting the same outside points by the partition into radicals gives
\[
 m(v)-m_u(v)\equiv\sum_{\substack{b\in B\\ v\cdot b=0}}s_b(u)\pmod2 .
\]
Indeed a split \(r\)-dimensional radical contributes \(2^{r-1}\) outside points, giving \(2^{r-2}\) after division by two, even if \(r\ge4\). The same count for the full radical partition, not restricted by \(v\), shows that \(\sum_{b\in B}s_b(u)\) is zero modulo two: the full outside count divided by two is \(2^{n-2}\), even. Thus the defining exclude parity identity \(\langle v,\varepsilon_F(u)\rangle=1+m_u(v)\bmod2\) gives
\[
 \varepsilon_F(u)=\sum_{b\in B}b\,s_b(u),\qquad
 \sum_{b\in B}s_b(u)=0\quad\text{in }\mathbb F_2 .
\]
This recovers the needed part of Carlet–Thornburgh Proposition 5.12 without any nonvanishing claim about \(\varepsilon_F\) at fixed inputs.

For a plane \(E\le V\) choose any basis \(x,y\) and let \(p_E=x\wedge y\in\bigwedge^2 V\). This is independent of the basis because every invertible binary two-by-two matrix has determinant one. The quadratic part of \(1_{u\notin E^\perp}\) corresponds to \(p_E\): the indicator is \(\langle u,x\rangle+\langle u,y\rangle+\langle u,x\rangle\langle u,y\rangle\), and its polarization is the alternating bilinear form encoded by \(p_E\). This identification is a linear isomorphism between bivectors and alternating forms on \(V^*\), equivalently between bivectors and Boolean quadratic functions modulo affine functions. Explicitly the coefficient of \(u_i u_j\) for \(i<j\) is \(x_i y_j+x_j y_i\). No distinction between \(\bigwedge^2\) and the space of symmetric matrices with arbitrary diagonal is being suppressed.

Write \(p_b=p_{R_b}\) for \(b\in B\). The quadratic tensor of \(u\mapsto\langle v,\varepsilon_F(u)\rangle\) can be computed in either of two ways:
\[
 Q(v)=\sum_{E\in\mathcal L_v}p_E=\sum_{b\in B}(v\cdot b)p_b\qquad(v\ne0).
\]
The first uses the defining parity and odd \(m(v)\): the component is the parity of the planes in \(\mathcal L_v\) *not* contained in \(u^\perp\). The second uses the preceding radical formula. Set \(Q(0)=0\), so this is a linear map in \(v\). The alternating \(\beta\) induces the linear map \(\Psi:\bigwedge^2 V\to W\) given by \(\Psi(x\wedge y)=\beta(x,y)\). Each \(E\in\mathcal L_v\) has \(\Psi(p_E)=v\), giving
\[
 \Psi Q(v)=v .
\]
This proves that \(Q\) is injective, including the exact quadraticity of every nonzero scalar component of \(\varepsilon_F\). Hence
\[
 \dim\operatorname{span}\{p_b:b\in B\}\ge n .
\]
The relation \(\sum_{b\in B}p_b=0\) follows from \(\sum s_b=0\) by taking quadratic parts. In particular \(B\) is nonempty and \(m\ge n+1\). If all positive radical dimensions are two then the partition immediately yields \(3m=2^n-1\). If another dimension \(d\) occurs, disjointness from any semi-bent radical gives \(d+2\le n\).

## 2. A short projective-code lemma

Let \(S\) be a nonempty set of distinct nonzero points in a binary space, of length \(N\), and let \(r=\dim\operatorname{span}S\). Its projective code consists of the evaluations \((u(x))_{x\in S}\) for all linear forms \(u\) on \(\operatorname{span}S\). Say it is \(\Delta\)-divisible if all those weights are multiples of \(\Delta\). We use the following short-length facts, with a self-contained proof. The length alternatives are an application of Heinlein–Honold–Kiermaier–Kurz–Wassermann's [Theorem 5.13](https://arxiv.org/html/1912.10147), and the small-code structures are described in their [earlier §5](https://arxiv.org/html/1703.08291v1#S5). Indeed with their \(q=2,\ r=d-1\), all admissible lengths up to \((d-1)2^d\) have the form \(a(2^d-1)+b2^d\), \(a,b\ge0\). Below \(3(2^d-1)\) one has \(a+b\le2\); requiring length divisible by three then forces \(b=0\). The argument below makes this short case self-contained.

**Lemma.** Let \(d\ge4\) be even, \(\Delta=2^{d-1}\), and \(N\) be a multiple of three. If this code is \(\Delta\)-divisible then
\[
 N=2\Delta-1,\quad N=4\Delta-2,\quad\text{or}\quad N\ge6\Delta-3.
\]
In the first case \(S\) is a whole \(d\)-space minus zero. In the second case \(S\) is exactly the union of the nonzero vectors in two disjoint \(d\)-spaces.

*Minimum and residual facts.* If \(C\) is a nonempty projective \(\delta\)-divisible binary code of length below \(2\delta\), then every nonzero word has weight \(\delta\). Averaging the weight over the \(2^r\) words gives \(N=\delta(2^r-1)/2^{r-1}\). Distinct nonzero columns give \(N\le2^r-1\), hence \(\delta\le2^{r-1}\) and \(N\ge2\delta-1\). If \(N=2\delta-1\) then \(2^{r-1}=\delta\) and the column set contains every nonzero vector in its span.

If \(a\) is a word of weight \(k\delta\), discard its support. The remaining code has divisibility \(\delta/2\) when this is an integer, since for each original word \(c\) its remaining weight is \((\mathrm{wt}(c)+\mathrm{wt}(c+a)-\mathrm{wt}(a))/2\). Projectivity is unchanged (the remaining columns stay distinct and nonzero in their span). A projective \(\delta\)-divisible code of length \(2\delta+1\) is impossible for \(\delta\ge4\): if weight \(2\delta\) is present, the residual code would consist of one point of divisibility \(\delta/2\ge2\); if not, the averaging equation for constant nonzero weight gives \(N<2\delta\).

*Two moment gaps.* Distinct nonzero binary columns are pairwise independent over a uniform linear form. Thus \(\mathbb E[w]=N/2\) and \(\mathbb E[w^2]=N(N+1)/4\). For every nonnegative integer \(j\), \((w-j\Delta)(w-(j+1)\Delta)\ge0\) for multiples \(w\) of \(\Delta\). In particular
\[
 f_j(N)=N(N+1)-2(2j+1)\Delta N+4j(j+1)\Delta^2\ge0 .
\]
For \(j=1\) its values at \(2\Delta+2\) and \(4\Delta-3\) are both \(6-2\Delta<0\); by convexity all integers between them are excluded. For \(j=2\) its values at \(4\Delta+3\) and \(6\Delta-4\) are both \(12-2\Delta<0\), excluding that interval. Since \(d\) is even, \(2\Delta\equiv1\pmod3\), so the only multiple of three strictly between the two claimed consecutive allowed regions not covered by these gaps is \(4\Delta+1\). At this length weights \(4\Delta\) and \(3\Delta\) would give residual lengths \(1\) and \(\Delta+1\) with divisibility \(\Delta/2\), both excluded above. With only weights \(0,\Delta,2\Delta\) the sum of the \(j=1\) moment polynomial over the words comes solely from the zero word, so \(2^{r-2} f_1(N)=2\Delta^2\). But \(f_1(4\Delta+1)=6\Delta+2\), requiring \(3\Delta+1\), an odd integer greater than one, to divide a power of two. This is impossible. Together with the minimum-length fact, the claimed alternatives follow.

*Second equality case.* At \(N=4\Delta-2\), a weight \(3\Delta\) would have a nonempty residual code of length \(\Delta-2\) divisible by \(\Delta/2\), below the minimum \(\Delta-1\). Thus again the moment sum is \(2\Delta^2\) and \(f_1(4\Delta-2)=2\), giving \(2^r=4\Delta^2\), or \(r=2d\).

Let \(q=2^d\). The Cayley graph on \(\operatorname{span}S\) uses adjacency \(x+y\in S\). Its degree is \(2(q-1)\), and the characters indexed by nonzero linear forms have eigenvalues \(N-2\mathrm{wt}(u)\in\{q-2,-2\}\). Writing \(A\) for adjacency and \(J\) for the all-one matrix, it follows on the character basis that
\[
 (A-(q-2)I)(A+2I)=2J.
\]
Indeed both sides vanish on the nontrivial characters, and both give \(2q^2\) times the constant vector on the remaining eigenspace. In particular distinct vertices have \(q-2\) common neighbors if adjacent, and two otherwise.

In \(S\), if distinct \(x,z\) are not adjacent, their two common neighbors are already \(0\) and \(x+z\), neither in \(S\), so no third one can lie in \(S\). Hence the relation \(x\sim z\) iff \(x=z\) or \(x+z\in S\) is transitive as well as reflexive and symmetric. Each class is a clique of size \(q-1\), because for \(x\in S\) the neighbors of \(x\) in \(S\) are exactly the common neighbors of \(x\) and \(0\). There are exactly two such classes. Adding zero to a class gives a subspace: for distinct \(x,y\) in it, \(x+y\in S\) is adjacent to \(x\) and lies in the same class. The two subspaces are disjoint and have dimension \(d\). This is a direct elementary-abelian Cayley proof, rather than an assertion that arbitrary graphs with the same parameters are unique. This completes the lemma.

## 3. Apply the lemma and couple with the wedge span

Let \(S=\bigcup_{b\in B}(R_b\setminus\{0\})\), of length \(N=3m\). Assume the next radical dimension \(d\) exists. For every nonzero input linear form, the entire ambient space has \(2^{n-1}\) points outside its kernel; each split radical of dimension at least \(d\) contributes \(2^{r-1}\), a multiple of \(\Delta=2^{d-1}\). Radicals wholly in the kernel give zero. Subtracting the high-dimensional blocks shows that \(S\) is \(\Delta\)-divisible. The distinct nonzero points give projectivity. The lemma therefore gives \(m=s,\ 2s,\) or \(m\ge3s\).

In the one-space case, all the two-dimensional radicals lie in the \(d\)-space. In the two-space case they each lie in one or the other: a plane meeting both disjoint subspaces in nonzero vectors would also contain their sum, outside the union. So the radicals in each space form a complete 2-spread with \(s\) planes.

For reference, the cited general length theorem also gives a longer necessary window: if \(3m\le(d-1)2^d\), then \(m=ks+j\) for some \(1\le k\le d-1\), \(0\le j\le\lfloor k/3\rfloor\). Indeed \(3m=a(2^d-1)+b2^d\) forces \(b=3j\), and with \(k=a+3j\) and \(2^d=3s+1\) it yields \(m=a s+j2^d=ks+j\). Also \(k\le d-1\) since \(d(2^d-1)>(d-1)2^d\). This is a direct corollary of the earlier code theorem, not an APN realizability condition.

For any one of these \(d\)-spaces \(U\), the sum of its \(s\) plane bivectors is zero. If a hyperplane does not contain \(U\), it leaves \(2^{d-1}\) points of \(U\) outside; each split plane contributes two, so \(2^{d-2}\) planes split, an even number. If the hyperplane contains \(U\), none splits. Taking quadratic parts of the resulting zero parity of split-plane indicators proves the bivector relation. Therefore the bivectors in a single \(U\) have span of dimension at most both \(s-1\) and \(\binom d2\), hence at most \(\rho\). For two spaces the sum of the two bounds is \(2\rho\). Applying the lower bound \(n\) from §1 completes the main theorem.

## 4. Structure if the unconditional bound is attained

As a separate consequence, suppose \(m=n+1\), with or without a larger radical dimension. Label the semi-bent masks \(b_i\) and let \(d_i=\Psi(p_{b_i})\). Write \(B_0\) and \(D\) for the \(n\)-by-\(m\) matrices with columns \(b_i\) and \(d_i\), respectively. Since \(\Psi Q\) is the identity, \(D B_0^{\mathsf T}=I_n\). Hence \(P=B_0^{\mathsf T}D\) is an idempotent of rank \(n\). Its diagonal is zero: \(b_i\cdot d_i=0\) by the radical property. Consequently \(I_m+P\) is a rank-one idempotent with every diagonal entry one. Over \(\mathbb F_2\) every column of such a matrix is the same nonzero column, and its entries must all be one. Thus \(P=I_m+J_m\) over \(\mathbb F_2\). In particular
\[
 b_j\cdot d_i=[j\ne i],
 \qquad d_i\cdot\varepsilon_F(u)=\sum_{j\ne i}s_{b_j}(u)=s_{b_i}(u).
\]
Each of these components therefore has polar rank two, and takes value one at exactly \(3\cdot2^{n-2}\) inputs. This is a necessary structure, not a general exclusion of equality. The dimension-four Gold cube attains \(m=n+1=5\).

## 5. Replay and scope

The proof is analytic in all dimensions; the scripts do not claim to enumerate all APN maps. One script checks the moment endpoints for a range of powers of two, exact thresholds, direct weight counts for one- and two-space spread models, the wedge identities, and the right-inverse tensor on two explicit APN maps. The spread models are examples of **point sets**, not assertions that all these tails occur for APN functions. The other script independently checks Cayley neighbor counts and recomputes radical sizes from Walsh amplitudes and constant scalar derivatives; it verifies the adjoint formula directly from all exclude plane parities in both APN cases. The six-variable APN example is the known QAPN-6-6 row 11, recoverable without downloading the table. See [SOURCES.md](SOURCES.md).
