# CRT divisibility under a dyadic lattice Gaussian: when is it positively associated?

**Result.** For any dyadic cyclotomic ring and any odd rational modulus, take a decomposition into nontrivial CRT blocks. The binary indicators that a centered spherical discrete Gaussian is zero in those blocks are positively associated at every width **if and only if** there are at most two blocks. With at least three blocks they are strictly positively associated at sufficiently small widths, but not associated at any sufficiently large width. The first two dual shells induce a full-block interaction, invisible to every proper marginal at those orders. This yields a signed leading term for any two statistics on complementary blocks and a parity rule for conditional pair covariances.

**Scope and prior work.** [Regev–Stephens-Davidowitz, Theorem 5.1](https://arxiv.org/abs/1502.04796) gives nonnegative correlation for membership in two centered sublattices under a lattice Gaussian; that result remains valid here at every width. A union of two incomparable sublattices need not be a sublattice, so their theorem does not settle association of the binary indicator vector. Here even a CRT model with independent Haar coordinates does not have this stronger property at broad finite widths. The CRT setting is the one described in [Lyubashevsky–Peikert–Regev, §2.5.5 and Lemma 2.19](https://sites.cc.gatech.edu/fac/cpeikert/pubs/toolkit.pdf). We use ordinary CRT and Poisson summation; the claims are about a standalone probability law and event aggregation, not a modification of a cryptographic reduction or a result about a scheme or secret.

## 1. Model and statement

Let \(d\) be a power of two, \(R=\mathbb Z[\zeta]\) with \(\zeta^d=-1\), and use the unscaled canonical norm
\[
\|x\|_{\mathrm{can}}^2=\operatorname{Tr}(x\bar x)=d\sum_{j=0}^{d-1}x_j^2,\qquad x=\sum_j x_j\zeta^j.
\]
The identity follows by summing the odd \(2d\)-th roots of unity to the power \(j-k\); this sum is zero for \(0<|j-k|<d\). For \(d=1\), use \(R=\mathbb Z\). Let \(X\) have probability mass on \(R\) proportional to \(\exp(-\pi\|x\|_{\mathrm{can}}^2/s^2)\). Take an odd integer \(q\ge3\) and pairwise comaximal proper ideals \(I_1,\ldots,I_r\) with product \(qR\). The \(I_i\) may be grouped products of prime powers. Write
\[
G=R/qR=\prod_{i=1}^r G_i,\qquad G_i=R/I_i,\qquad M_i=|G_i|,\qquad Y_i=\mathbf{1}_{X\in I_i}.
\]
For a uniform element of \(G\), the corresponding vector has independent Bernoulli law \(\mathbb P_0\) with \(p_i=1/M_i\). Define
\[
 v=e^{-\pi d/s^2},\qquad t=e^{-\pi s^2/(d q^2)},\qquad
 A_d(t)=2dt+2d(d-1)t^2,
 \qquad h_i(1)=1,\quad h_i(0)=-\frac{1}{M_i-1}.
\]

For \(t\le (16d)^{-1}\) the probability of every pattern \(y\in\{0,1\}^r\) satisfies
\[
 \frac{\mathbb P_s(Y=y)}{\mathbb P_0(Y=y)}
 = 1+A_d(t)\prod_{i=1}^r h_i(y_i)+e_y,\qquad
 |e_y|\le 800 d^3t^3. \tag{1}
\]
In particular, every proper marginal has relative errors bounded by the same \(800d^3t^3\) without the \(A_d(t)\) term. For a partition of the indices into nonempty \(S,T\), and real functions \(f,g\) on the respective zero-indicator subvectors, put
\[
 \Delta_S f=\sum_{u\in\{0,1\}^S}(-1)^{|S|-\sum_i u_i} f(u)
\]
and define \(\Delta_T g\) the same way. For fixed moduli and functions as \(s\to\infty\),
\[
 \operatorname{Cov}_s(f,g)
 = A_d(t)\frac{\Delta_S f\,\Delta_T g}{q^d}+O_{d,f,g}(t^3). \tag{2}
\]
The implicit error can be taken independent of \(q\) and of the partition if the sup norms of \(f,g\) are bounded. A zero product of differences does not determine the eventual sign.

Recall that a vector is positively associated when the covariance of every two coordinatewise nondecreasing real functions of it is nonnegative. For the vector \(Y\):
* If \(r\le2\), it is positively associated at every \(s>0\).
* For **every** \(r\), it is positively associated if \(v\le(16d)^{-1}\), with strict inequality for every pair of nonconstant increasing functions.
* For \(r\ge3\), define \(F=Y_1\lor Y_2\) and \(H=\prod_{i=3}^r Y_i\). Then
\[
 \operatorname{Cov}_s(F,H)
 =-\frac{2dt+2d(d-1)t^2}{q^d}+O_d(t^3), \tag{3}
\]
and the sign is strictly negative whenever
\[
 t\le\frac{1}{60d\sqrt{M_1+M_2-1}}. \tag{4}
\]
The labels 1 and 2 can be any two of the blocks. Both functions in this obstruction are increasing and depend on disjoint coordinates. For instance, \(R=\mathbb Z[\zeta_8]\), \(q=17\) has four blocks, obtained by evaluating \(\zeta_8\) at the roots \(2,8,9,15\) of \(x^4+1\) modulo 17. Here \(H\) is membership in \(I_3I_4\), while \(F\) is membership in \(I_1\cup I_2\). Equivalently, one can group \(I_3I_4\) into a single third block. By the small- and large-width signs and continuity, the covariance for this choice takes both signs and is zero at least once; uniqueness is not asserted.

## 2. Poisson calculation

Write \(k=(k_0,\ldots,k_{d-1})\in\mathbb Z^d\) also for the element \(\sum_j k_j\zeta^j\). Use additive characters
\[
 \chi_k(x)=\exp(2\pi i \sum_j k_jx_j/q).
\]
In coefficients \(X\) has independent weights proportional to \(\exp(-\pi d x_j^2/s^2)\). In one coordinate, Poisson summation on \(q\mathbb Z+a\) expresses the residue probability as
\[
 \frac1q\frac{\sum_{\ell\in\mathbb Z}t^{\ell^2}\exp(2\pi i\ell a/q)}
                  {\sum_{\ell\in\mathbb Z}t^{q^2\ell^2}}.
\]
Changing the sign of all characters would give the same formula. Tensorization gives the density on \(G\) relative to uniform
\[
 D_s(x)=\frac{\sum_{k\in\mathbb Z^d}t^{\|k\|_2^2}\chi_k(x)}
                   {\theta(t^{q^2})^d},\qquad
 \theta(z)=\sum_{\ell\in\mathbb Z}z^{\ell^2}. \tag{5}
\]
To pass from this to zero-indicator patterns, the sum of a nontrivial character of \(G_i\) vanishes on all of \(G_i\). Its average conditional on zero is 1 and conditional on nonzero is \(-1/(M_i-1)\). For a trivial character both averages are 1. Thus the conditional average of \(\chi_k\) over a uniform residue with pattern \(y\) equals \(\prod_{i:\chi_k|_{G_i}\ne1}h_i(y_i)\).

The coefficient pairing \(\sum_j k_j x_j\) is the constant coefficient of \(x\bar k\) reduced by the defining polynomial \(Z^d+1\). For \(k=1\) the resulting character is nontrivial on every nontrivial CRT block. Indeed, if it were trivial on one block, the constant coefficient of \(x\) would be zero modulo \(q\) for every element \(x\) of that block regarded as an ideal in \(G\). For every \(j\), multiplication by \(\zeta^{-j}\) preserves the ideal and exposes coefficient \(j\), so the entire block would be zero. If \(k\) is a unit in \(G\), multiplication by \(\bar k\) is an automorphism of each block, and \(\chi_k\) remains nontrivial on every block.

Every squared-norm-one vector \(k\) is a signed monomial and hence a unit. Every squared-norm-two vector is a signed sum of two distinct monomials and is also a unit modulo \(qR\). To see this, in any residue field of any maximal ideal of \(G\), the root \(\zeta\) has order \(2d\): its \(d\)-th power is \(-1\) in odd characteristic and \(d\) is a power of two. No power \(\zeta^j\) for \(0<j<d\) can be \(\pm1\). Consequently such a binomial vanishes in no residue field and lies in no maximal ideal of \(G\). There are exactly \(2d\) norm-one and \(4\binom d2=2d(d-1)\) norm-two vectors, including both signs. All their pattern contributions are the same full product of the \(h_i\).

Here is an explicit error bound. For \(0<z\le r_0=(16d)^{-1}\),
\[
 \theta(z)^d-1
 \le \exp(2dz/(1-z))-1\le 3dz,
\]
using \(\theta(z)\le1+2z/(1-z)\) and \(e^u-1\le u/(1-u)\) for \(0\le u<1\). The coefficient sum of terms of degree at least 3 in \(\theta(t)^d\) is bounded by \((t/r_0)^3(\theta(r_0)^d-1)\le768d^3t^3\). Equation (5) has denominator \(1+\delta\), with \(0\le\delta\le3dt^{q^2}\le3dt^9\). Also \(A_d(t)\le1/4\). Every pattern character average has absolute value at most 1, so removing the denominator and the higher terms gives error at most \(768d^3t^3+(5/4)3dt^9\le800d^3t^3\). This proves (1). At every proper marginal the leading term averages to zero, since \(\mathbb E_0 h_i(Y_i)=0\) for every omitted coordinate.

For \(S\) and \(T\) as in (2), independence under \(\mathbb P_0\) and
\[
 \mathbb E_0\!\left[f(Y_S)\prod_{i\in S}h_i(Y_i)\right]
 =\left(\prod_{i\in S}p_i\right)\Delta_S f
\]
give (2). For bounded \(f,g\), the error follows by applying (1) to \(fg\) and separately to each proper marginal, then expanding the product of the marginal expectations. Here \(\prod_i M_i=q^d\). For \(F,H\) above, the respective top differences are \(-1\) and \(1\). To check (4), let \(x_0=800d^3 t^3<1\), \(u_0=\mathbb E_0 F\), \(w_0=\mathbb E_0 H\). Their marginal errors are bounded in absolute value by \(x_0 u_0\), \(x_0 w_0\); the error for their product expectation from (1) is at most \(x_0 u_0 w_0\). Thus the error in (3) is at most
\[
 x_0(3+x_0)u_0w_0 \le 3200d^3t^3\,\frac{M_1+M_2-1}{q^d}.
\]
Under (4) this error is less than \(dt/q^d\), whereas the magnitude of the leading negative term is at least \(2dt/q^d\).

One may also condition on a particular pattern \(y'\) of all coordinates different from \(i,j\). For fixed \(q,d\), (1) gives
\[
 \operatorname{Cov}_s(Y_i,Y_j\mid Y_{[r]\setminus\{i,j\}}=y')
 = A_d(t)p_i p_j\prod_{k\notin\{i,j\}}h_k(y'_k)+O_d(t^3).
 \tag{6}
\]
Indeed, the conditioning probability divided by its Haar value is \(1+O_d(t^3)\). After conditioning, each of the individual means has no first-two-shell term, and the product mean acquires the term shown. Unless there are no remaining coordinates, different conditioning patterns therefore give both signs for all sufficiently large widths, with the negative sign exactly when the number of non-memberships in the conditioning pattern is odd. Unconditional singleton covariances are nonnegative throughout by the sublattice theorem and, when \(r>2\), have zero first-two-shell term.

## 3. Small widths and the two-block case

In primal coefficients the zero vector has weight 1; each of the \(2d\) shortest nonzero vectors is a unit, has weight \(v\), and gives the all-zero indicator pattern. The zero vector gives the all-one pattern. For nontrivial increasing events \(B,C\) on the cube, \(B^c,C^c\) both contain the all-zero pattern and neither contains the all-one pattern. Set \(L=\theta(v)^d-1\), so their individual probabilities are at most \(L/(1+L)\) and their intersection probability is at least \(2dv/(1+L)\). Consequently
\[
 \operatorname{Cov}_s(\mathbf1_B,\mathbf1_C)
 =\operatorname{Cov}_s(\mathbf1_{B^c},\mathbf1_{C^c})
 \ge \frac{2dv(1+L)-L^2}{(1+L)^2}>0
 \qquad(0<v\le(16d)^{-1}).
\]
The last inequality uses \(L\le3dv\) and \(9d^2v^2\le(9/16)dv<2dv\). Every increasing function on the finite cube is a constant plus a nonnegative linear combination of increasing-event indicators, with a positive coefficient for a nontrivial one if it is nonconstant. This proves the claimed strict association at small widths, uniformly over the CRT choice. More precisely, the probability of each of \(B^c,C^c,B^c\cap C^c\) is \(2dv+O_d(v^2)\) as \(v\to0\); the next terms have total mass bounded by \(v^2 r_0^{-2}(\theta(r_0)^d-1)\), independently of the choice of the events. So all such covariances have the same leading primal term \(2dv\). Continuity in \(s\) follows from locally uniform summability of the primal weights.

If \(r=1\), all increasing events are nested. If \(r=2\), the only two mutually incomparable nontrivial increasing events are respectively \(Y_1=1\) and \(Y_2=1\). Their covariance is nonnegative for all \(s\) by Regev–Stephens-Davidowitz applied to the two ideal sublattices (or after rescaling to unit width). Two nested events have covariance \(\mathbb P(B)(1-\mathbb P(C))\ge0\) when \(B\subseteq C\). The same decomposition into indicators proves association for all widths. More generally the sublattice theorem gives nonnegative correlations for intersections over any two index sets, and those correlations remain valid after conditioning on simultaneous sublattice memberships, since the conditional Gaussian is a centered Gaussian on the intersection lattice. Neither that implication nor the CRT decomposition entails cutwise association, as (3) and (6) show.

**Replay.** Run `python3 verify-crt-divisibility-association.py` with the neighboring verifier. It uses only integer arithmetic and exact rational interval bounds on omitted primal and Poisson terms, for two synthetic CRT examples (one over a small cyclotomic ring, one over the integers with a composite CRT block). The general claims are proved above; the script checks the shell arithmetic, explicit sign reversal, and the conditional signs in these examples.
