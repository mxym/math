# Statistical information after losing the pairing of dyadic noisy observations

Discarding the matching between independently uniform coefficients and their noisy responses is quite different from merely changing the coding of each matched row. We quantify this distinction in a broad-noise model: a hidden permutation of an arbitrarily large group leaves the leading total variation and information of just one matched row. With several independently shuffled groups, we identify the fixed-label Gaussian comparison window and a strong list-information converse. Nothing here assumes a method for finding the original permutation or a bound on computation.

## 1. Model and main conclusions

Fix odd \(q\ge3\), dyadic \(d\to\infty\), \(R=(\mathbb Z/q)[X]/(X^d+1)\), and \(b=\beta/d\) for fixed \(\beta>0\). At a fixed **unit** label \(s\in R^\times\), a matched row is \(A\sim U_R\) and \(Y=As/q+E\) in the coefficient torus, with independent scalar noises of density \(f_b(x)=\sum_h b^{h^2}e^{2\pi i h x}\). Write \(g_b=q^{-1}\sum_a f_b(\cdot-a/q)\). At a unit label, the marginal response law is \(\nu=g_b^{\otimes d}\).

Let there be \(G=G_d\ge1\) known groups. Group \(j\) has \(n_j\ge1\) matched rows and then releases the ordered design sequence and the response sequence after an independent uniform permutation within that group. The permutation is not recorded. Let \(P_s\) denote the full released law and \(Q\) the product reference: in each group the designs and responses are mutually independent with their same individual marginals. The group sizes are deterministic, otherwise arbitrary, with **no bound** on their growth or disparity. Put \(\mu_d=2G d b^2\).

* If \(\mu_d\to0\), uniformly over group sizes,
  \[
    \operatorname{TV}(P_s,Q)\sim\sqrt{\mu_d/(2\pi)},\qquad
    \operatorname{TV}(P_s,P_t)\sim\sqrt{\mu_d/\pi}\quad(s\ne t\ \text{units}).
  \]
  In particular with one group, no matter how large, the leading TV equals its one matched row value.
* If \(\mu_d\to\mu\in(0,\infty)\), the two limits are respectively
  \[
        2\Phi(\sqrt{\mu}/2)-1,\qquad 2\Phi(\sqrt{\mu/2})-1 .
  \]
  More precisely for any fixed number of distinct unit labels, their likelihood ratios jointly under \(Q\) converge to independent \(e^{\sqrt\mu Z-\mu/2}\), where \(Z\) is standard Gaussian. These assertions concern fixed-label comparisons, not simultaneous recovery of a growing collection. If \(\mu_d\to\infty\), both TV distances tend to 1.
* For a uniform hidden label in any deterministic set of \(M\) distinct units, a list of size at most \(L<M\) has success tending to zero if \(\log(M/L)\to\infty\) and \(Gdb^2\le(1-\epsilon)\log(M/L)\) for some fixed \(\epsilon>0\). This is true even with unrestricted computation and arbitrarily many total rows. For example, when \(\log(M/L)\) is of order \(d\), this criterion is on the order of \(d^2\) known groups, not on the total number of observations.

The unit assumption matters: for a nonunit the marginal distribution of a response can itself depend on an ideal. There is no corresponding claim about an unknown marginal design, recorded matching information, or an implementation.

## 2. One group: orthogonal expansion and exact spectral second moment

At the unit label \(s\), under the independent reference for one pair write
\[
 L_s(a,y)=\prod_{p=1}^d \frac{f_b(y_p-(as)_p/q)}{g_b(y_p)},\qquad D_s=L_s-1 .
\]
The centered kernel \(D_s\) integrates to zero in either variable separately. For a group of size \(n\), the released likelihood is the average over permutations of \(\prod_i(1+D_s(a_i,y_{\pi(i)}))\). The terms with exactly one factor \(D_s\) sum to
\[
 T_s=\frac1n\sum_{i,j=1}^n D_s(a_i,y_j).
\]
Functions involving different supports in the design or response indices are orthogonal whenever a variable occurs only in one of the supports, by the two centering identities. In particular \(T_s\) is orthogonal to every higher-order term, and \(E_Q T_s^2=\|D_s\|_2^2\) (in the double sum only pairs with both indices the same contribute).

For clarity the spectral second moment can be derived directly. The integral operator with real kernel \(L_s\) maps \(L^2(\nu)\) to \(L^2(U_R)\); let \(\lambda_i\) denote the eigenvalues of its squared singular-value operator, omitting the constant eigenvalue 1. This is a finite-rank positive operator. Its remaining eigenvalues are nonnegative and their sum is \(\sigma=\|D_s\|_2^2\). In the second moment of the released likelihood, two permutations contribute according to their relative permutation \(\rho\). Integrating either variable on each cycle of length \(l\) gives \(\operatorname{Tr}[(L_s L_s^*)^l]=1+\sum_i\lambda_i^l\), where products denote operators. This is the general cycle calculation used in [Paslev–Huleihel, Lemma 1 and equation (71)](https://arxiv.org/pdf/2311.05874), here written for differing marginal spaces and squared singular values. Counting permutations by their cycles therefore gives
\[
 E_Q L_{\rm group}^2=[z^n]\exp\!\left\{\sum_{l\ge1}
           (1+\textstyle\sum_i\lambda_i^l)z^l/l\right\}
   =[z^n]\frac1{1-z}\prod_i\frac1{1-\lambda_i z}.                 \tag{1}
\]
The coefficient of degree 1 from the last product is \(\sigma\). Its degree \(l\) coefficient (a complete homogeneous polynomial) is at most \(\sigma^l\) by nonnegativity. Consequently the squared norm of the contribution beyond \(1+T_s\) is at most \(\sigma^2/(1-\sigma)\), whenever \(\sigma<1\), uniformly in \(n\).

For the dyadic location law the paired density is a product over \(d\) independent coordinates under the reference, because \(as\) is uniform when \(s\) is a unit. Since \(f_b/g_b=1+2b\cos(2\pi x)+O(b^4)\) uniformly, the scalar centered second moment is \(2b^2+O(b^4)\). The scalar linear term itself is centered under \(\nu\) and under the uniform shift. Thus
\[
 \sigma=(1+2b^2+O(b^4))^d-1=2db^2+O(d^2b^4).
\]
If each scalar centered term is replaced by its first harmonic, the squared norm of the error in the paired kernel is \(O(db^8+d^2b^4)\): the scalar errors have squared norm \(O(b^8)\), and the products using two or more distinct coordinates are orthogonal and sum to \(O(d^2b^4)\). In \(T_s\), an error with zero integral in either variable has squared norm exactly that of the pair kernel, independent of \(n\), by the same double-sum calculation. We have proved, for one group uniformly in size and label,
\[
       L_{\rm group,s}=1+F_s+R_s,\qquad
       \|R_s\|_{L^2(Q)}=O(db^2),                                \tag{2}
\]
where
\[
 F_s=2b\sum_{p=1}^d\operatorname{Re}(U^s_p V_p),\quad
 U^s_p=n^{-1/2}\sum_i e^{-2\pi i (a_i s)_p/q},\quad
 V_p=n^{-1/2}\sum_j e^{2\pi i y_{j,p}}.
\]
Here \(F_s\) serves to calculate probability distances. It is not a reconstruction of the joint matching or of an unspecified label.

## 3. Small total variance and the uniform pair constant

For a given unit \(s\), the pairs \(U^s_p,V_p\) in the displayed sum are independent across \(p\), with zero means, second absolute moments 1, and complex second moments 0. The last two facts follow from the uniform finite shift and the invariance of \(g_b\) under the \(1/q\) shifts (odd \(q\ge3\)); independence between \(U\) and \(V\) is under the reference. Their real product has variance \(1/2\) and any fixed absolute moment is bounded uniformly over \(n\). Indeed normalized sums of the bounded, centered independent variables have uniformly sub-Gaussian real and imaginary parts by Hoeffding. Thus \(E_Q F_s^2=2db^2\). Also the covariance \(E_Q F_s F_t\) is zero for distinct units, since the remaining same-coordinate term from the design is the mean character of the nonzero image ideal \((s-t)R\).

We need more than a zero covariance for the small-variance pair comparison. Put \(\Delta_p=U^s_p-U^t_p\). Uniformly in both unit labels and the group size,
\[
       E_Q\sum_p|\Delta_p|^2=2d,\quad
       \operatorname{Var}_Q\!\left(\sum_p|\Delta_p|^2\right)=O(d),
       \qquad \sum_p E_Q|\Delta_p|^4=O(d).                       \tag{3}
\]
For the variance, the separate squared-norm sums for \(U^s\) and \(U^t\) have variance \(O(d)\) by independence across coordinates within each label. For the cross sum write \(\sum_p \overline{U^s_p}U^t_p=n^{-1}\sum_{i,j} H_{ij}\), where \(H_{ij}=\sum_p\overline{u^s_{i,p}}u^t_{j,p}\) and \(u^s_{i,p}=e^{-2\pi i (a_i s)_p/q}\). A diagonal term has mean zero and second absolute moment \(d\): the image \(a_i(s-t)\) is uniform in a nonzero ideal, and no signed monomial or signed binomial in distinct coordinates belongs to its coefficient-dot annihilator. These are units in the odd dyadic ring, by the exact order \(2d\) of \(X\) in every residue field. For an off-diagonal term the same second moment \(d\) follows from independent rows and coordinate product marginals for either unit label. In the squared sum, an off-diagonal term can pair only with itself or its reverse, since otherwise a row appears once and is centered. Distinct diagonals are independent and centered, and a diagonal paired with an off-diagonal also has a row appearing once. Cauchy–Schwarz bounds each remaining term by \(d\). This gives \(O(d)\) after division by \(n^2\). The fourth moment bound in (3) follows from the individual uniform coordinate bounds and \(|U^s-U^t|^4\le8(|U^s|^4+|U^t|^4)\).

All groups under \(Q\) are independent. For a given \(s\), a Lyapunov bound over group-coordinate terms shows \(\sum_j F_{j,s}/\sqrt{\mu_d}\Rightarrow N(0,1)\). For the pair, condition on all design arrays. The terms \(\operatorname{Re}(\Delta_p V_p)\) over all groups and positions are now independent with variances \(|\Delta_p|^2/2\); their fourth moments are bounded by a constant times \(|\Delta_p|^4\). By (3), the summed conditional variance is \((1+o_{\mathbb P}(1))Gd\), and the summed fourth moments divided by \((Gd)^2\) tend to zero in probability. The conditional Lyapunov argument thus gives \(\sum_j(F_{j,s}-F_{j,t})/\sqrt{2\mu_d}\Rightarrow N(0,1)\) under \(Q\). Second moment bounds also give convergence of absolute first moments. This justification permits arbitrary growth or disparity of group sizes and arbitrary distinct unit-label sequences.

When \(\mu_d\to0\), the full product likelihood differs in \(L^2(Q)\) from \(1+\sum_j F_{j,s}\) by \(O(Gdb^2)\). In fact, products of the centered group likelihoods on distinct subsets of groups are orthogonal. Each centered group squared norm is \(O(db^2)\) by (1). The sum of products involving at least two groups has squared norm \(O((Gdb^2)^2)\); the single-group remainders (2) sum with squared norm \(O(G(db^2)^2)\) because their means vanish. Thus the error is \(o(\sqrt{\mu_d})\). The two CLTs and the factor \(1/2\) in TV give both stated leading constants.

## 4. Finite Gaussian window for any fixed label family

We first justify a replacement of a group likelihood by the positive density
\[
       \widehat L_s=e^{F_s-a_s},\qquad a_s=\log E_Q e^{F_s}.
\]
Uniformly in \(n\), \(a_s=db^2+O(db^3)\) because \(\operatorname{Re}(U^s_p V_p)\) is centered with variance \(1/2\) and has a uniformly bounded exponential moment in a fixed neighborhood of zero. The exponential moment follows from the sub-Gaussian bounds above and \(|UV|\le(|U|^2+|V|^2)/2\). Also
\(\|\widehat L_s-(1+F_s)\|_2=O(db^2)\): use the exponential Taylor remainder and Cauchy–Schwarz; the eighth moment of \(F_s\) is \(O((db^2)^4)\) by independence and centering, and \(E e^{4|F_s|}\) is bounded by \(E e^{4F_s}+E e^{-4F_s}\). On \(|F_s|\le1\), the density \(\widehat L_s\) is bounded below by a positive constant, so squared Hellinger distance there is \(O((db^2)^2)\) by (2) and the squared density error. Off that event, \(\Pr_Q(|F_s|>1)\le e^{-c d}\): in the scalar moment estimate one may use a fixed small positive or negative multiplier of \(F_s/b\), then choose it sufficiently small as a function of \(\beta\). Both true and replacement densities have bounded \(L^2(Q)\) norms. Cauchy–Schwarz therefore bounds their combined mass on the complement by \(O(e^{-c'd})\). The entire squared Hellinger distance of the group laws is \(O((db^2)^2)\). Hellinger tensorization gives TV \(o(1)\) after replacing all \(G\) groups when \(Gdb^2=O(1)\).

If \(\mu_d\to\mu>0\), then \(G\to\infty\). For a fixed set of distinct units, the vector of \(\sum_j F_{j,s}\) under \(Q\) converges to independent centered Gaussians of variance \(\mu\): covariance is exactly diagonal, and each group coordinate has fourth moment \(O((db^2)^2)\) by the within-label product calculation. For a fixed linear combination the same order follows by the elementary fixed-dimensional fourth moment inequality. Lyapunov over independent groups proves the vector CLT. The normalizers sum to \(\mu/2+o(1)\); the products of replacement densities have uniformly bounded second moments. It follows that TV for the replacement experiments tends to the corresponding Gaussian likelihood-ratio comparison, and the Hellinger estimate transfers it to the actual experiments. It also transfers joint likelihood-ratio weak convergence under the common \(Q\), since each density differs by \(o(1)\) in \(L^1(Q)\).

For the null comparison the limiting density is \(e^{\sqrt\mu Z-\mu/2}\) and the event on which it exceeds 1 gives \(2\Phi(\sqrt\mu/2)-1\). For a pair, the likelihoods are independent such lognormal densities under the common reference. On the event that the first exceeds the second, their log difference is Gaussian with variance \(2\mu\) and mean \(+\mu\) under the first tilted law and \(-\mu\) under the second. This gives \(2\Phi(\sqrt{\mu/2})-1\). Finally when \(\mu_d\to\infty\), keep a deterministic subset of groups with \(\mu_d\) approaching any prescribed finite positive level. TV cannot increase by discarding the other groups. Letting the chosen level tend to infinity proves the last TV limits.

## 5. Label list converse and its dispersion centering

Write \(D_{j,d}=\operatorname{KL}(P_{j,s}\|Q_j)\) for a single group. Its law and value are the same for all unit labels under the bijection \(a_i\mapsto a_i s\). Uniformly over group sizes,
\[
    D_{j,d}=db^2+O((db^2)^2),\qquad
    \operatorname{Var}_{P_{j,s}}(\log L_{j,s})=(2+o(1))db^2.           \tag{4}
\]
For detail, \(u=L_{j,s}-1=F_s+R_s\) has \(E_Q u=0\), \(E_Q u^2=(2+o(1))db^2\) by (2). For every fixed \(\eta>0\),
\[
        E_Q[u^2{\bf1}_{|u|>\eta}]=o(db^2)
\]
uniformly: use \(E R_s^2=O((db^2)^2)\), \(E F_s^4=O((db^2)^2)\), and split between \(|F_s|\) and \(|R_s|\) exceeding \(\eta/2\), using Cauchy–Schwarz for the cross tail. The ratios of \((1+u)\log(1+u)-u\) and \((1+u)(\log(1+u))^2\) to \(u^2\) are bounded for \(u\ge-1\) and tend at zero to \(1/2\) and 1 respectively, first giving the leading terms in (4). Also \(x|\log x|^3/(x-1)^2\) is bounded on the positive half-line, so \(E_{P_{j,s}}|\log L_{j,s}|^3=O(db^2)\).

To obtain the stated sharper mean, reuse the exponential replacement \(\widehat L_s=e^{F_s-a_s}\). If \(L=L_{j,s}\), then
\[
 \operatorname{KL}(P_{j,s}\|\widehat L_s Q_j)=O((db^2)^2).        \tag{5}
\]
On \(|F_s|\le1\), the nonnegative normalized entropy integrand \(\widehat L_s h(L/\widehat L_s)\) with \(h(x)=x\log x-x+1\) is at most \(C(L-\widehat L_s)^2\) since \(h(x)\le(x-1)^2\). On the complementary event the reference mass is exponentially small by §4. There use \(|x\log x|\le C(1+x^{3/2})\), the bounded second moments of both densities, and \(\log\widehat L_s=F_s-a_s\). Hölder bounds the \(L^{3/2}\) contribution by a constant times the fourth root of the reference mass. Cauchy–Schwarz and the fourth moment bound for \(F_s\) make the term \(L|F_s|\) exponentially small there as well. This proves (5).

In fact \(E_Q[L F_s]=2db^2\) **exactly**. The sample-support orthogonality of §2 reduces this inner product to that of the one-pair density and its sum of first harmonics. Within each coordinate the latter's expectation under the true paired density is \(2b\int f_b(x)\cos(2\pi x)\,dx=2b^2\). Consequently
\[
 D_{j,d}=\operatorname{KL}(P_{j,s}\|\widehat L_s Q_j)+2db^2-a_s
          =db^2+O((db^2)^2)
\]
using \(a_s=db^2+O(db^3)\) and \(b=\beta/d\). This proves the mean estimate without needing a uniformly bounded third moment of the true density.

Under the common reference of an independent uniform label and observations from \(Q\), any size-\(L\) list event has probability at most \(L/M\). Change measure to the joint true law, splitting by whether \(\sum_j \log L_{j,S}\) exceeds \(\log(M/L)-\gamma\). In the lower part, the probability in the true law is at most \(e^{-\gamma}\). The remaining upper-tail probability is for a sum of independent random variables at every fixed label, and its law is identical across labels. Its mean is \(\sum_j D_{j,d}\), and variance \(O(Gdb^2)\) by (4). Choosing \(\gamma=\epsilon\log(M/L)/3\) and using Chebyshev proves the strong converse. If additionally \(Gdb^2\to\infty\) and \((Gdb^2-\log(M/L))/\sqrt{2Gdb^2}\to z\in\mathbb R\), Lyapunov from the third-moment bound gives a \(\limsup\) list success of at most \(\Phi(z)\) (use any \(\gamma\to\infty\) of smaller order than the denominator). Indeed \(\log(M/L)\le d\log q\) implies \(Gdb^2=O(d)\) in this window, so the total mean correction in (4) is \(O(1)\) and can be discarded at the scale \(\sqrt{2Gdb^2}\). No achievability of growing-label lists is asserted.

## 6. Prior and scope

[Paslev–Huleihel](https://arxiv.org/abs/2311.05874) analyze unknown permutations and eigenvalue-based bounds for dependence tests, including an all-group-size weak-detection obstruction. [Elimelech–Huleihel](https://proceedings.mlr.press/v202/elimelech23a.html) give analogous phase comparisons for Gaussian features. We use the known cycle method as the starting point, not as a claimed novelty. The refinements here are the sharp small-signal TV constants, comparison of two specified non-null unit labels, the exact Gaussian limit across known groups of unrestricted sizes, and the growing-label information converse in the stated mixed finite/torus model. They concern loss of pairing in a probability experiment. They do not recover a permutation, assess an outside system, or bound the complexity of ordinary matched Ring-LWE.
