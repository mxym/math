# Variance matching does not order the moments of a lattice Gaussian

For a full lattice \(L\subset\mathbb R^n\) let \(X_t\) have probabilities proportional to \(e^{-t|x|^2}\), \(x\in L\), with \(t>0\). For a nonzero real direction \(u\), write \(Y_t=u\cdot X_t\), \(v_t=\mathbb E Y_t^2\), and compare its \(2k\)-th moment to that of the centered real Gaussian with the **same actual variance**:
\[
\Delta_{2k}(L,u,t)=\mathbb E Y_t^{2k}-(2k-1)!!\,v_t^k,\qquad k\ge2.
\]

**Results.**
1. In every dimension and fixed direction, the sign of \(\Delta_{2k}\) is \((-1)^k\) for sufficiently small precision \(t\), and is positive for sufficiently large precision. The small-precision term is explicit below, including when the first dual shell is orthogonal to the direction.
2. On \(\mathbb Z\) with \(u=1\), the fourth and eighth excesses are strictly positive for every \(t>0\). The sixth excess has exactly one zero \(t_*\), negative below and positive above. With \(a_*=\pi^2/t_*\), \(7.474<a_*<7.475\); numerically \(t_*\simeq1.3204111\).
3. No analogous single-crossing principle holds in higher rank: for every \(n\ge1\) and every odd \(k\ge3\), there is an orthogonal rank-\(n\) lattice and a direction for which \(\Delta_{2k}\) has at least \(2n-1\) sign changes as a function of precision.

These are comparisons to a variance-matched real Gaussian, not comparisons to the larger Gaussian scale in a subgaussian upper bound.

## 1. All lattices: endpoints from dual activity and primal rarity

Let \(L^*=\{w:w\cdot L\subset\mathbb Z\}\), \(s=|u|^2/(2t)\), and \(\lambda_w=(\pi/t)u\cdot w\). Completing the square and using Poisson summation gives the moment generating function
\[
\mathbb E e^{zY_t}
=e^{sz^2/2}\frac{\sum_{w\in L^*}e^{-\pi^2|w|^2/t}\cos(\lambda_w z)}
{\sum_{w\in L^*}e^{-\pi^2|w|^2/t}}.
\]
For \(j\ge1\) write \(b_j\) for the normalized dual average of \(\lambda_w^{2j}\). Then \(v_t=s-b_1\). The \(j=0,1\) terms in the \(2k\)-th derivative of the moment generating function agree with the constant and linear terms from \((2k-1)!!(s-b_1)^k\). Indeed \(\binom{2k}{2}(2k-3)!!=k(2k-1)!!\). The remaining linear dual terms have alternating signs and are dominated as \(t\downarrow0\) by the term \((-1)^k b_k\). To be precise, put
\(\beta=\min\{|w|^2:w\in L^*,\ u\cdot w\ne0\}\). The active shell is nonempty because \(L^*\) spans. At every fixed \(j\), the terms after this shell in \(b_j\) and the effect of the denominator are exponentially smaller than that shell. The linear term with index \(j<k\) loses a factor \(t^{k-j}\) relative to \(b_k\); the higher powers of \(b_1\) from variance matching are exponentially smaller. Hence
\[
\Delta_{2k}(L,u,t)=(-1)^k\left(\frac\pi t\right)^{2k}e^{-\pi^2\beta/t}
\left[\sum_{\substack{w\in L^*\\|w|^2=\beta}}
|u\cdot w|^{2k}+O_{L,u,k}(t)\right].
\]
The coefficient is strictly positive inside brackets.

For \(t\to\infty\), use the first primal shell with a nonzero projection onto \(u\), of squared length \(\gamma\). The moment and the variance each have asymptotic a positive constant times \(e^{-\gamma t}\), by the same shell comparison. Since \(k>1\), the variance power in the comparison is of smaller order. This proves the opposite endpoint result, in particular at least one crossing for every odd \(k\ge3\).

## 2. Rank one: strict fourth and eighth excesses and a unique sixth crossover

Set \(a=\pi^2/t\), \(s=1/(2t)\),
\[
S_j(a)=\sum_{n\ge1}n^{2j}e^{-a(n^2-1)},\qquad
b(a)=\frac{2e^{-a}}{1+2e^{-a}S_0(a)},\qquad
u_j=b(a)(2a)^j S_j(a).
\]
Here the \(u_j\) are normalized moments of the dual frequencies relative to the real scale \(s\). In particular \(v_t/s=1-u_1>0\). Differentiating the preceding formula and subtracting the matched Gaussian moments gives exactly
\[
\begin{aligned}
s^{-2}\Delta_4&=u_2-3u_1^2,\\
s^{-3}\Delta_6&=15u_2-u_3-45u_1^2+15u_1^3,\\
s^{-4}\Delta_8&=u_4-28u_3+210u_2-630u_1^2+420u_1^3-105u_1^4 .
\end{aligned}
\]
All \(u_j\) are positive. On \(t\ge\pi\), the direct primal sum bounds the variance by \(2e^{-\pi}(1+(S_1(\pi)-1))<1/11\), the denominator being at least 1. Since \(|n|^{2k}\ge n^2\) for integers, the fourth, sixth and eighth excesses are then positive. The bound \(S_j(a)-1\le4^j e^{-3a}/(1-4^j e^{-3a})\), whenever its denominator is positive, follows from \(n\le2^{n-1}\) and \(n^2-1\ge3(n-1)\) for \(n\ge2\).

For the rest take \(a\ge\pi\). For the fourth excess use \(u_2\ge2a u_1>3u_1^2\) since \(0<u_1<1\). For the eighth, use \(u_1^2\le p u_2\) by Cauchy–Schwarz, where \(p=bS_0\) is the nonzero dual probability. Put \(P(x)=x^2-28x+210\). For \(n\ge2\), \(P(2an^2)\ge P(2a)\), since \(P\) is increasing beyond 14 and \(P(8a)-P(2a)=12a(5a-14)>0\). It follows that the eighth excess, divided by \(s^4u_2\), is at least
\[
P(2a)-630p\ \ge\ 4a^2-56a+210-1261e^{-a}.
\]
We used \(p\le2e^{-a}(1+(S_0(\pi)-1))\) and \(e^\pi>23\). The lower bound is positive for \(a\ge5\) because \(P\ge14\) and \(e^5>140\). On \([\pi,5]\) it is concave since \(e^5<150\), and both endpoints are positive (use \(\pi<22/7\), \(e^\pi>23\)). This proves the claimed global signs for orders four and eight.

For the sixth excess divide by \(s^3b(2a)^2\); its sign is the sign of
\[
H(a)=15S_2-2aS_3-45bS_1^2+30a b^2 S_1^3.
\]
If \(a\ge7.5\) all nonzero dual modes have \(2an^2\ge15\), so \(15u_2-u_3\le0\) and \(-45u_1^2+15u_1^3<0\). If \(\pi\le a\le7.4\), the geometric tail bound with \(e^\pi>23\) gives \(2a(S_3-1)<0.079\), \(45bS_1^2<91e^{-a}\). Therefore
\[
H(a)>15-2a-0.079-91e^{-a}>0.
\]
The last expression is concave and is positive at both endpoints, using \(\pi<22/7,\ e^\pi>23,\ e^{7.4}>1600\). In the remaining interval \([7.4,7.5]\), the geometric tail bound gives \(S_1<1.001\), and \(0\le-S_j'\le S_{j+1}-1\), with \(S_4-1<10^{-7}\). Also \(0<b<1/800\) and \(b'=-b+b^2S_1<0\). Differentiation and omission of negative terms give
\[
H'\le -2+2a(S_4-1)+45bS_1^2+90bS_1(S_2-1)+30b^2S_1^3<0.
\]
This proves the unique zero. The stated decimal bracket for \(a_*\) is certified by finite rational inequalities in the replay: bound \(e^a\) by its finite Taylor sum and a geometric remainder, and use the same geometric \(S_j-1\) bounds, giving \(H(7.474)>0\), \(H(7.475)<0\). Numerical root evaluation is not used for uniqueness.

## 3. Many crossings on orthogonal lattices

For a fixed dimension \(n\) and large \(R>1\), take
\(L_R=\operatorname{diag}(R^{i/2})_{i=1}^n\mathbb Z^n\) and \(u_R=(R^{i/2})_{i=1}^n\). Then the projection is \(\sum_i R^i N_i\), with \(N_i\) independent centered integer Gaussians of precisions \(tR^i\). At a test time \(t=x R^{-j}\), rescale the projection by \(R^{-j}\). Component \(j\) is exactly the rank-one law of precision \(x\). Each \(i<j\) tends to zero in \(L^{2k}\), since its \(2k\)-moment after rescaling is \(O(R^{k(i-j)})\) by the Gaussian Riemann sum bound as its precision tends to zero. Each \(i>j\) tends to zero in \(L^{2k}\) too: a polynomial in \(R^{i-j}\) is multiplied by \(e^{-xR^{i-j}}\). Thus the sign of the rescaled moment excess at that test time tends to the rank-one sign, if that sign is nonzero.

For odd \(k\ge3\), pick fixed \(0<x_-<x_+\) where the rank-one excess is negative and positive, respectively, using §1. Choose \(R>x_+/x_-\) sufficiently large. In increasing order, the test times are \(x_-R^{-n},x_+R^{-n},x_-R^{-(n-1)},x_+R^{-(n-1)},\ldots,x_-R^{-1},x_+R^{-1}\). Their signs alternate. The excess is analytic for positive precision (termwise differentiation of the Gaussian sums on compact precision intervals), so between each pair of sample times lies a sign-changing zero. There is no dimension-free bound on the number of these changes. The construction uses only independent coordinate Gaussians, not correlations or a nondiagonal lattice.

## Comparison

[Agostini and Améndola](https://arxiv.org/abs/1801.02373) derive lattice Gaussian moments from theta functions; [Regev and Stephens-Davidowitz](https://arxiv.org/abs/1502.04796) prove covariance is minimized by the centered coset (Corollary 3.2), giving a lower bound on the real moment generating function by the variance-matched Gaussian through exponential tilting; their Proposition 3.3 gives the nonnegative fourth excess in every dimension and cites earlier rank-one work. The short fourth-order proof here is included to contrast with the different higher-order behavior. That pointwise lower bound does not imply coefficientwise comparison of even moments, as the sixth moment already shows. The results here quantify the leading dual-shell term, settle the rank-one sixth crossover with rigorous uniqueness, and show that even orthogonal higher-rank lattices can have many crossings. They make no claim about cryptographic instances or sampling algorithms.

Replay: Node.js 18+, without dependencies or data.
