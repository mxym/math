# Parity-dependent asymptotics for random stable roommates

Every participant independently ranks all other participants uniformly at random, with no ties. A matching is stable if no pair jointly prefers a match to their current assignments; an unmatched participant prefers any other participant to being unmatched. Thus for odd size the unmatched participant can block, and the model is not “delete one participant and ignore all their edges.” Let \(p_n\) denote the probability of a stable matching in this model.

**Theorem.** As \(N\) tends to infinity through even integers,
\[
\begin{aligned}
p_N
&= \frac{e\,2^{1/4}\Gamma(3/4)}{\sqrt{\pi}}\;N^{-1/4}
 - \frac{e\,\Gamma(1/4)}{2^{5/4}\sqrt{\pi}}\;N^{-3/4}
 + O(N^{-1}),\\[2mm]
p_{N+1}
&= C_{\mathrm{odd}}N^{3/4}e^{-\sqrt N}
     +O\!\left(N^{1/2}e^{-\sqrt N}\right),\\
C_{\mathrm{odd}}
&=\frac{e^{1/4}}{2\sqrt{\pi}}
      \int_0^\infty t^{-3/2}\left(1-e^{-2t^2-t}\right)\,dt
 \ =\ 1.5516231454\ldots .
\end{aligned}
\tag{1}
\]
Moreover, if \(q_n\) is the probability that a stable partition contains a singleton, allowing other odd cycles, then along **either** parity
\[
q_n=e^{-3/4}\, n\,e^{-\sqrt{n-1}}\bigl(1+O(n^{-1/2})\bigr).
\tag{2a}
\]
The even leading coefficient in (1) is due to [Young–Studebaker, arXiv:2610.07741v1](https://arxiv.org/html/2610.07741v1). The second coefficient, the odd solvability asymptotic, and the fixed-point prefactor (2a) are the refinements derived here. The odd asymptotic is for one singleton with the rest matched stably, not for existence of any stable partition. [Pittel, Lemma 4.2 and Corollary 4.3](https://arxiv.org/html/1705.08340v1) already obtains stretched-exponential upper estimates for fixed points in the broader stable-partition model. [Glitzner–Manlove](https://arxiv.org/html/2505.06717v1#S3.SS2) document the odd/even disparity numerically. A targeted search did not locate these refinements; this is not a priority claim.

## 1. One signed formula, two weights

The exact signed cycle identities of [Mertens, Proposition 3.2 and §5, Eqs. (8), (19)](https://arxiv.org/abs/1502.06635) are the combinatorial input. Use \(N\) active vertices, even, and a flag \(b=0\) or \(1\) for no singleton or one prescribed singleton. The ordinary permutations of the active vertices have cycles of even length. The transpositions give a matching \(B\) and the cycles of length at least four give a simple two-regular graph \(H\) on a set \(A\) of \(m=2k\) vertices. Let \(D=B\cup H\) and let \(\ell\) count the long cycles. The stability integral for a given such permutation is
\[
p_{H,b}=\int_{[0,1]^N}\prod_{i\in A}x_i\,
    \prod_{\{i,j\}\notin D,\ i<j}(1-x_ix_j)\,
    \prod_{i=1}^N(1-x_i)^b\,dx .
\tag{2}
\]
For example, use independent uniform preference scores and condition on the score of each successor, with smaller scores preferred. Each long-cycle predecessor contributes \(x_i\). Each non-neighbor blocking pair has forbidden area \(x_ix_j\). The prescribed singleton is unmatched and accepts any pair, so each active vertex \(i\) must prefer its successor to that singleton, accounting for \(1-x_i\). The signed sum of (2) has multiplier \((N+1)^b\) and signs \((-1)^\ell\). This counts ordinary directed permutations: the two orientations of an undirected long cycle are not identified in the enumeration.

Write \(L=N+m\), \(S=\sum_i x_i\), \(q=\sum_i x_i^2\). Let
\[
J_{N,m}=\int_{\mathbb R_+^N}e^{-S^2/2}\prod_{i\in A}x_i\,dx=\frac1{(L-1)!!}.
\]
Under the measure with this normalized density, \(S\) has the chi law with \(L\) degrees of freedom and \(u=x/S\) is independent Dirichlet with parameters \(\alpha_i=2\) on \(A\), \(\alpha_i=1\) elsewhere. This follows by radial-simplex factorization. Define
\[
M_L=\mathbb E_{\chi_L}e^{-S},\qquad
J^{(0)}_{N,m}=J_{N,m},\quad J^{(1)}_{N,m}=J_{N,m}M_L .
\]
The reference measure for \(b=1\) is tilted by \(e^{-S}\); it leaves the independent Dirichlet law unchanged.

For any excluded graph \(D\) of maximum degree two, the non-neighbor product in (2) is bounded by \(e^{81/16-S^2/2}\) on the cube. Indeed \(\log(1-y)\le-y-y^2/2\). For a sequence \(y_i\), \(\sum_{\{i,j\}\in D} y_i y_j\le\sum_i y_i^2\). Apply this with \(y_i=x_i\) and \(y_i=x_i^2\) to bound the logarithm by \(-S^2/2+(9/4)q-q^2/4\); use \(x_i^4\le x_i^2\). Also \(\prod(1-x_i)\le e^{-S}\). Thus **both** integrands are bounded by a fixed constant times their respective reference density before normalization.

Use a good set \(G=\{S\le2\sqrt N,\ \max_i u_i\le\log^2 N/N\}\) and \(a=2\log^2 N/\sqrt N\). The complement has probability \(O(e^{-c\log^2 N})\) under either reference measure, uniformly in \(m\le N\). For the untilted radial component the chi-square exponential moment at \(1/4\) gives \(e^{-N}2^{L/2}\le e^{-(1-\log2)N}\); tilting by the decreasing function \(e^{-S}\) cannot increase an upper tail. The Dirichlet coordinate laws are \(\mathrm{Beta}(1,L-1)\) or \(\mathrm{Beta}(2,L-2)\); their upper tails at \(z\) are \((1-z)^{L-1}\) and \((1-z)^{L-2}(1+(L-2)z)\), respectively. A union bound gives the conclusion. On \(G\), \(x_i\le a<1\), and the loss upon cutting off the cube integral (2) is \(O(J^{(b)}_{N,m}e^{-c\log^2 N})\).

## 2. Uniform integration through two orders in the long edges

For up to \(m_*=\sqrt N\log N\) long vertices, set
\[
T_b=e^{S^2/2+bS}\prod_{\{i,j\}\notin B,\ i<j}(1-x_ix_j)\prod_i(1-x_i)^b,
\qquad z_e=x_ix_j\quad(e=\{i,j\}\in H).
\]
On the cube \(T_b\) is bounded by the domination just proved. On \(G\), \(Z=\sum_{e\in H}z_e\le m a^2=o(1)\). The multiplicative correction that omits the long edges is
\[
\prod_{e\in H}(1-z_e)^{-1}
  = 1+\sum_e z_e+\sum_e z_e^2+\sum_{e<f}z_e z_f+O(Z^3).
\tag{3}
\]
The bound follows by comparing the complete homogeneous polynomials of degree at least three in the \(z_e\) with the corresponding powers of \(Z\).

Under the even reference measure, each fixed monomial of total degree \(2r\) has expectation
\[
\mathbb E\prod_i x_i^{r_i}
   = \frac{\prod_i (\alpha_i)_{r_i}}{(L+1)(L+3)\cdots(L+2r-1)},
   \qquad \sum_i r_i=2r,
\tag{4}
\]
where \((\alpha)_r=\alpha(\alpha+1)\cdots(\alpha+r-1)\). It follows that \(\mathbb E Z^3=O(m^3/N^3)\). Under the tilted reference the same bound follows from the independent moment formulas for \(u\) and \(\mathbb E S^6=O(L^3)\), proved below. The expectation of the degree-two part in the \(z_e\) is \(O(m^2/N^2)\) under either reference.

Both \(G\) and \(T_b\) are invariant under all permutations of the \(m\) long vertices. The integrated polynomial in (3) depends only on \(N,m\), not on \(H\): there are \(m\) edges, \(m\) repeated-edge squares, and exactly \(m\) unordered pairs of distinct edges sharing a vertex, because \(H\) is simple and two-regular. All other pairs are disjoint. Let this common normalized integral on \(G\) be \(b^{(b)}_{N,m}\). Including the cutoff error and bounded \(T_b\),
\[
p_{H,b}=J^{(b)}_{N,m}
 \left[b^{(b)}_{N,m}+O(m^3/N^3+e^{-c\log^2 N})\right].
\tag{5}
\]
This common second-degree correction is important for the even second term: bounding the degree-two contribution in absolute value separately for each permutation leaves an error of the very order being measured.

### The even common profile

Set \(h_B=\sum_{e\in B}x_ix_j\), and \(f=q/2+h_B-q^2/4\). On \(G\) Taylor expansion gives
\[
|\log T_0-f|
   \le C\left(\sum_i x_i^4+\sum_{e\in B}z_e^2+
                       \sum_{i<j}(x_ix_j)^3\right),
\tag{6}
\]
using \(z_e=x_ix_j\) here also for \(e\in B\). By (4) its expectation is \(O(1/N)\): there are \(O(N)\) degree-four terms and \(O(N^2)\) degree-six terms. Because \(h_B\le q/2\), \(f\le1\), and the bound on \(T_0\) yields
\(\mathbb E[\mathbf1_G|T_0-e^f|]=O(N^{-1})\).

By (4), with \(r_B=(N-m)/2\),
\[
\mathbb E q=(2N+4m)/(L+1),\quad
\mathbb E h_B=r_B/(L+1),\quad
\operatorname{Var}(q),\operatorname{Var}(h_B)=O(N^{-1}).
\tag{7}
\]
For detail, the numerators for \(\mathbb E q^2\) and \(\mathbb E h_B^2\), with denominator \((L+1)(L+3)\), are \((2N+4m)^2+20N+64m\) and \(r_B^2+3r_B\), respectively. Subtract the squared means.

Write \(f=1/2+U-V\) with
\[
U=h_B-\tfrac12-\tfrac12(q-2),\qquad V=(q-2)^2/4.
\]
Since \(1/2+U=1+h_B-q/2\le1\),
\[
\begin{aligned}
\mathbb E U&=(-2m+1/2)/(L+1)=-2m/N+O(N^{-1}+m^2/N^2),\\
\mathbb E U^2+\mathbb E V&=O(N^{-1}+m^2/N^2),\\
\mathbb E e^f&=e^{1/2}(1-2m/N)+O(N^{-1}+m^2/N^2).
\end{aligned}
\tag{8}
\]
Indeed \(e^{1/2+U}-e^f\le eV\), and Taylor's remainder for \(e^{1/2+U}\) is at most \(eU^2/2\); no fourth central moment is needed.

For the linear term in (3), any edge \(e\) on \(A\) has \(\mathbb E z_e=4/(L+1)\) and \(\|z_e\|_2=O(N^{-1})\). Also
\[
\|\mathbf1_G T_0-e^{1/2}\|_2=O(N^{-1/2}+m/N).
\]
To see this, boundedness converts the \(L^1\) estimate following (6) to squared \(L^2\); for \(e^f\) use \(|e^f-e^{1/2}|\le C(|U|+\min(V,1))\) and \(\min(V,1)^2\le V\). The cutoff itself costs \(O(e^{-c\log^2 N})\). Thus the linear term contributes \(4m e^{1/2}/(L+1)+O(N^{-1}+m^2/N^2)\) by Cauchy–Schwarz. The quadratic terms contribute \(O(m^2/N^2)\). Combining,
\[
b^{(0)}_{N,m}=e^{1/2}(1+2m/N)+O(N^{-1}+m^2/N^2).
\tag{9}
\]

### Radial tilt and the odd common profile

For the chi law with \(L\) degrees of freedom put \(\nu=\sqrt{L-1}\) and \(y=S-\nu\). Up to normalization the radial density in \(y>-\nu\) is \(e^{F_\nu(y)}\) with
\[
F_\nu(y)=-y^2/2+\nu^2\{\log(1+y/\nu)-y/\nu\}\le -y^2/2 .
\]
On \(|y|\le\nu/2\), \(F_\nu(y)=-y^2+O(|y|^3/\nu)\). By the mean value theorem for exponentials, the difference of the two densities \(e^{F_\nu(y)}-e^{-y^2}\) on that region is bounded in absolute value by \(C|y|^3e^{-y^2/2}/\nu\). The remaining tails are exponentially small, even multiplied by \(e^{-y}\). Therefore
\[
M_L=e^{-\sqrt L+1/4}\bigl(1+O(L^{-1/2})\bigr)
\tag{10}
\]
by taking the ratio of the integrals with and without \(e^{-y}\) and completing the square. Moreover \(y\) has bounded absolute moments of each fixed order under the tilted law, since the normalizing integral against \(e^{-y}\) stays bounded below. In particular \(\mathbb E|S^2-L|=O(\sqrt L)\) and \(\mathbb E S^r=O(L^{r/2})\) for each fixed \(r\). This also proves the moment bounds used in (5) for \(b=1\).

The Dirichlet variable \(u\) is independent of \(S\), and \(q=S^2\sum_i u_i^2\), \(h_B=S^2\sum_{\{i,j\}\in B}u_i u_j\). Under the untilted law the means and variances are (7). Replacing \(S^2\) by \(L\) in each expression costs \(O(N^{-1/2})\) in \(L^1\), since \(\mathbb E|S^2-L|=O(\sqrt L)\) for either radial distribution and the means of the two simplex forms are \(O(N^{-1})\). The resulting variables depending only on \(u\) have the same law in both cases. Hence under the tilted law
\[
\mathbb E|q-2|+\mathbb E|h_B-1/2|=O(N^{-1/2}+m/N).
\tag{11}
\]
On \(G\), \(\log T_1\) has leading term \(f_1=h_B-q^2/4\); the extra error from \(\sum_i(\log(1-x_i)+x_i)\) after its quadratic part is \(O(\sum_i x_i^3)\), of tilted mean \(O(N^{-1/2})\). The error (6) still has tilted mean \(O(N^{-1})\). The exponents \(f_1\) and \(\log T_1\) are bounded above. Also \(f_1\le h_B-q^2/4\le1\) and \(\mathbb E|e^{f_1}-e^{-1/2}|=O(N^{-1/2}+m/N)\): on \(|q-2|\le1\) use Lipschitz dependence on \(q,h_B\), and outside use boundedness and Markov. Consequently the constant part in (3) integrates to \(e^{-1/2}+O(N^{-1/2}+m/N)\), the linear part is \(O(m/N)\), and the quadratic part is \(O(m^2/N^2)\). Thus
\[
b^{(1)}_{N,m}=e^{-1/2}+O(N^{-1/2}+m/N).
\tag{12}
\]

## 3. Signed summation

For \(m=2k\), the signed and unsigned counts of long-cycle permutations on their prescribed labels are \((2k)!\,d_k\) and \((2k)!\,v_k\), where
\[
d(z)=\sum d_kz^k=e^{z/2}\sqrt{1-z},\qquad
v(z)=\sum v_kz^k=e^{-z/2}(1-z)^{-1/2}.
\]
These follow by exponentiating the signed cycle series \(\mp\sum_{j\ge2}z^j/(2j)\). Choices for the long vertices and their complement matching yield the normalization
\[
A_{N,k}=\frac{N!}{(N-2k)!}\frac{(N-2k-1)!!}{(N+2k-1)!!}
       =\prod_{j<k}\frac{N-2j}{N+2j+1}
\tag{13}
\]
when multiplied by \(J_{N,2k}\); put \(A_{N,k}=0\) for \(k>N/2\). The \(k=0\) product is 1. The coefficient identity \(k d_k=-\frac12[z^{k-2}]e^{z/2}(1-z)^{-1/2}\) for \(k\ge2\) gives \(d_0=1,d_1=0\), and \(d_k<0\) for \(k\ge2\). Coefficientwise domination by \((1-z)^{-1/2}\) gives \(v_k=O((k+1)^{-1/2})\). From (13),
\[
A_{N,k}\le e^{-k^2/(4N)},\qquad
1-A_{N,k}\le\min(1,2k^2/N).
\tag{14}
\]
These follow by summing \((4j+1)/(N+2j+1)\) and using \(1-\prod(1-z_j)\le\sum z_j\). In particular all terms with \(2k>m_*\) are exponentially small in \(\log^2 N\) after summing by the unsigned \(v_k\). For the odd case their radial factors satisfy \(M_{N+2k}=O(e^{-\sqrt N})\) by (10), so this tail estimate remains valid even after division by \(e^{-\sqrt N}\).

In (5) the cubic errors sum with \(v_k\), giving \(O(N^{-5/4})\) after radial normalization: \(\sum k^3v_k A_{N,k}=O(N^{7/4})\) by (14). The common coefficients sum with \(d_k\), an absolutely summable series of total absolute mass 2. The terms \(m^2/N^2\) in (9) then cost \(O(N^{-5/4})\) since \(\sum k^2|d_k| A_{N,k}=O(N^{3/4})\). These power sums are elementary comparisons with Gaussian integrals. The even formula becomes
\[
p_N=e^{1/2}\sum_{k\ge0}d_k A_{N,k}(1+4k/N)+O(N^{-1}).
\tag{15}
\]
For odd size, (10) and (12) yield
\[
\frac{p_{N+1}}{(N+1)e^{-\sqrt N-1/4}}
  =\sum_{k\ge0}d_k A_{N,k}e^{-k/\sqrt N}+O(N^{-1/2}).
\tag{16}
\]
For the latter, the radial correction
\(e^{-\sqrt{N+2k}+\sqrt N}=e^{-k/\sqrt N}(1+O(k^2/N^{3/2}))\)
holds uniformly below the cutoff and sums to \(O(N^{-3/4})\) with \(|d_k|A_{N,k}\). The factor \(m/N\) in (12) costs \(O(N^{-3/4})\) there too. These statements rely on preserving the signs of the **common** terms, rather than bounding them against \(v_k\).

## 4. Evaluation of the two scalar sums

Let \(s_k=-d_k\) for \(k\ge2\) and \(c=e^{1/2}/(2\sqrt\pi)\). We have \(\sum_{k\ge2}s_k=1\) by absolute summability and \(d(1)=0\), and
\[
s_k=c\,k^{-3/2}\left(1+\frac9{8k}+O(k^{-2})\right).
\tag{17}
\]
For detail, in the derivative identity for \(d_k\), write \([z^j](1-z)^{-1/2}=\binom{2j}{j}/4^j=(\pi j)^{-1/2}(1-1/(8j)+O(j^{-2}))\) by Stirling. For \(j=k-2-r\) with \(r\le k/2\) this gives \(1+(7/8+r/2)/k+O((1+r)^2/k^2)\) relative to \((\pi k)^{-1/2}\). Averaging over weights \(2^{-r}/r!\) adds \(1/4\) to \(7/8\). The larger \(r\)'s are an exponentially small factorial tail. The same argument gives the bound \(|d_k|=O((k+1)^{-3/2})\) used above.

Below the cutoff \(2k\le m_*\), expansion of the logarithm in (13) yields
\[
\log A_{N,k}=-2k^2/N+k/N+O(k^2/N^2+k^4/N^3).
\tag{18}
\]
The two squared terms in each logarithmic difference have difference \((4j+1)/(2N^2)\), not order \(j^2/N^2\). This cancellation is needed for the second coefficient. When combined with \(1+4k/N\), the first correction to \(e^{-2k^2/N}\) is therefore \(5k/N\). The summed error in this substitution is \(O(N^{-5/4})\) with weights \(s_k\) by (14), (17); the tails beyond the cutoff of the replaced terms are superpolynomially small.

Write \(J=\int_0^\infty t^{-1/2}e^{-2t^2}\,dt=2^{-5/4}\Gamma(1/4)\). Using \(\sum s_k=1\), (17) and (18), the scalar sum in (15) is
\[
c N^{-1/4}\int_0^\infty t^{-3/2}(1-e^{-2t^2})\,dt
+c N^{-3/4}\left\{\frac98\int_0^\infty t^{-5/2}(1-e^{-2t^2})\,dt-5J\right\}
+O(N^{-1}).
\tag{19}
\]
To verify the error as a bound rather than a formal expansion, use mesh \(u=N^{-1/2}\). For the first integral the summand function is \(O(t^{1/2})\) near zero and has second derivative \(O(t^{-3/2})\) there and integrable away from zero. The trapezoid error is \(O(u^{3/2})\): bound the first interval directly, and bound the rest by \(C u^2\int_u^\infty |f''(t)|dt\). For the other two integrals the functions are \(O(t^{-1/2})\) near zero and their derivatives \(O(t^{-3/2})\); the same first-interval argument and the usual first-derivative Riemann estimate give \(O(u^{1/2})\). Their rescaled errors are all \(O(N^{-1})\). The remainder term of (17) costs
\(\sum_{k\ge2} O(k^{-7/2})\min(1,Ck^2/N)=O(1/N)\), and using just the leading coefficient in the \(5k/N\) term costs \(O(1/N)\). Finally integration by parts gives
\[
\int t^{-3/2}(1-e^{-2t^2})dt=2^{5/4}\Gamma(3/4),
\qquad
\int t^{-5/2}(1-e^{-2t^2})dt=(8/3)J
\]
with the indicated integrals over \((0,\infty)\). The second bracket in (19) is \(-2J\); multiplying (19) by \(e^{1/2}\) proves the even formula.

For (16) the summed error replacing \(A_{N,k}\) by \(e^{-2k^2/N}\) is \(O(N^{-3/4})\) after including \(e^{-k/\sqrt N}\), by (18) and (17) and the same tail bounds. Rewriting using \(1-\sum s_k=0\), the scalar sum is
\[
c N^{-1/4}\int_0^\infty t^{-3/2}(1-e^{-2t^2-t})\,dt+O(N^{-1/2}).
\]
The near-zero \(O(t^{-1/2})\) bound for this function and \(O(t^{-3/2})\) for its derivative again give \(O(u^{1/2})\) mesh error. The \(O(k^{-5/2})\) coefficient correction in (17) is \(O(N^{-1/2})\) since \(1-e^{-2k^2/N-k/\sqrt N}\le C\min(1,k/\sqrt N)\). Inserting this into (16) proves the odd formula. The alternate nonsingular integral for \(C_{\mathrm{odd}}\) is \(2 e^{1/4}\pi^{-1/2}\int_0^\infty (4z^2+1)e^{-2z^4-z^2}dz\), by integration by parts and \(t=z^2\).

## 5. Exact prefactor for the singleton event

We first justify a **restricted pointwise signed identity**, rather than restricting an expected identity after cancellation. [Tan's Theorem 6.6](https://www.dcs.gla.ac.uk/~pat/jchoco/roommatesMorph/papers/1-s2.0-019667749190028W-main.pdf) says that all stable partitions have the same odd cycles, including singletons, with the same cyclic permutations (reversed if using the opposite successor convention). At most one singleton is possible with complete preferences, since two unmatched participants would block.

Fix a preference instance and its common odd cycles \(C\). Let \(R\) be the complement of their vertices. A participant \(c\) in \(C\) threatens \(i\in R\) if \(c\) prefers \(i\) to its prescribed successor in \(C\). On \(R\), declare an edge \(ij\) acceptable if each endpoint prefers the other to all of its threats. An even stable permutation on \(R\) that extends to a stable partition with \(C\) uses only acceptable edges: its successor must beat all threats and its predecessor is at least as preferred as its successor. Conversely, using acceptable edges and stability on this restricted graph suffice for extension. A pair excluded by a threat cannot block on \(R\), because its threatened endpoint strictly prefers its assigned successor to that pair; pairs touching \(C\) cannot block by construction and by feasibility of \(C\) in the given instance.

Complete the preferences on \(R\) by placing all unacceptable partners after every acceptable one at both endpoints. There is an acceptable stable perfect matching, obtained by splitting the even cycles of one stable partition into alternate pairs. Such a split only improves preferences relative to each old successor and cannot create a block. Every stable perfect matching of the completed lists is likewise acceptable. Indeed compare with a known acceptable one. In a nontrivial alternating cycle of their union, every edge of either matching has an endpoint preferring the other matching, by its stability. Counting the two preference classes on the cycle then forces every edge to join opposite classes. An unacceptable edge of the new matching would have *both* endpoints preferring the known acceptable matching, impossible. Similarly every stable all-even permutation has only acceptable edges, because each of its edges belongs to one of the stable perfect matchings produced by splitting its cycles. The case \(R=\varnothing\) has just the empty matching and empty permutation.

Thus the full-list pointwise even signed identity, [Young–Studebaker, Appendix A](https://arxiv.org/html/2610.07741v1#A1), applies on \(R\) and gives signed sum 1 on this odd-cycle layer. In the original instance there is only one such layer. It follows that the signed sum over stable permutations with exactly one singleton, **allowing other odd cycles** with positive cycle sign, is the indicator defining \(q_n\).

Now let \(N=n-1\) be the number of active vertices (not necessarily even). The integral (2) with \(b=1\) still applies, with \(m\) now the number of vertices in all long cycles of lengths at least three. Its long graph is still simple and two-regular, so estimates (5), (10), and (12) hold, with \(N-m\) even. Signed and unsigned counts on \(m\) prescribed vertices, divided by \(m!\), have generating functions
\[
a(z)=\exp\left(\sum_{\ell\ge3,\ \ell\ {\rm odd}}\frac{z^\ell}{\ell}
                  -\sum_{\ell\ge4,\ \ell\ {\rm even}}\frac{z^\ell}{\ell}\right)
    =(1+z)e^{-z+z^2/2},\qquad
w(z)=\frac{e^{-z-z^2/2}}{1-z}.
\]
The coefficients are denoted by \(a_m,w_m\). We have \(0\le w_m\le1\) by coefficientwise domination by \((1-z)^{-1}\). The coefficients of \(a(z)\) have finite sums \(\sum_m(m+1)^j|a_m|\) for every fixed \(j\), by analyticity on disks of arbitrarily large radius. Also
\[
\sum_{m\equiv N\ (2)}a_m=\frac{a(1)+(-1)^N a(-1)}2=e^{-1/2}.
\tag{20}
\]
For allowed \(m\), the normalization replacing (13) is
\[
\widetilde A_{N,m}
 =\frac{N!}{(N-m)!}\frac{(N-m-1)!!}{(N+m-1)!!}
 =\prod_{j=1}^m\frac{N-m+2j}{N+j}.
\]
It is at most \(e^{-m(m-1)/(4N)}\), and \(1-\widetilde A_{N,m}\le m(m-1)/(2N)\), by summing \((m-j)/(N+j)\). With unsigned weights \(w_m\) the integrated cubic errors in (5) now cost \(O(N^{-1})\), by summing \(m^3 e^{-m(m-1)/(4N)}/N^3\); terms beyond \(\sqrt N\log N\) are superpolynomially small. With signed weights \(a_m\) we can replace \(\widetilde A_{N,m}\) by 1, \(b^{(1)}_{N,m}\) by \(e^{-1/2}\), and \(M_{N+m}/e^{-\sqrt N+1/4}\) by 1, at total error \(O(N^{-1/2})\). For the radial factor use (10) and \(0\le1-e^{-\sqrt{N+m}+\sqrt N}\le m/(2\sqrt N)\). Multiplying by \(n\) choices of singleton and using (20) proves (2a). In particular on odd sizes, conditional on there being a singleton, the probability that it is the *only* odd cycle is asymptotic to \(e^{3/4} C_{\mathrm{odd}}(n-1)^{-1/4}\).

## A check on counting matchings instead of existence

If \(Z_n\) counts stable matchings (with one possible singleton when \(n\) is odd), its expectation comes from just the transposition type, \(m=0\), without signs. Equations (9), (10), and (12) give
\[
\mathbb E Z_N=e^{1/2}+O(N^{-1}),\qquad
\mathbb E Z_{N+1}=(N+1)e^{-\sqrt N-1/4}(1+O(N^{-1/2})).
\]
The even leading expectation is classical. Dividing by (1) shows that on solvable instances the mean number of solutions is of order \(N^{1/4}\) in *both* parities, despite their different chances of solvability.

The accompanying [exact checker](verify_stable_roommates_parity.py) checks the signs/counts, three quadratic edge classes, required moment identities and finite Mertens examples. No fitting of finite probabilities is used for (1). This is AI-assisted research and has not been externally peer reviewed or Lean verified.
