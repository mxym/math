# Uniform posterior bounds when the prior is chosen from the public design

In a random-design experiment the choice of prior *before* the coefficients are drawn is not equivalent to a choice that sees all coefficients but none of the responses. We give a simultaneous conditional result for the latter quantifier, covering arbitrary prior weights, feature maps, and list sizes. We also exhibit a mathematically different design-dependent prior at higher rank for which the usual full-batch Gaussian critical limit fails. The independent-noise model is unchanged; the change is exclusively in how labels are selected.

## 1. Setting and results

Fix odd \(q\ge3\), \(\beta>0\), dyadic \(d\), \(R=(\mathbb Z/q)[X]/(X^d+1)\), and an arbitrary positive integer rank \(r=r_d\). Take \(k\) independent uniform rows \(A_i\in R^r\), \(b=\beta/d\), and \(t_d=kb^2\) in a fixed compact subinterval of \((0,\infty)\). After observing just the design \(A\), a prior \(\pi_A\) on \(R^r\) is specified. Draw \(S\) from it, then take \(Y_i=\langle A_i,S\rangle_R/q+E_i\) in the coefficient torus, with independent scalar errors of density \(f_b(y)=\sum_{h\in\mathbb Z} b^{h^2}e^{2\pi i h y}\). The prior may have any support and need not be bounded in entropy.

Let \(\nu\) be the independent product response reference with scalar density \(g_b=q^{-1}\sum_a f_b(\cdot-a/q)\). Given the design, write \(L_s=dP_s(\cdot\mid A)/d\nu\). Under the observed law put
\[
 Z=\log L_S(Y),\qquad W=-\log\pi_A(S).
\]
Conditional on \(A\), the random variable \(Z\) is independent of \(S\) and is a sum of \(kd\) scalar terms \(\log(f_b(E)/g_b(E))\). For any feature \(F=f_A(S)\) fixed by the design and label only, let \(W_F=-\log P(F\mid A)\) and \(H_F=-\log P(F\mid A,Y)\), both evaluated at the true feature value. Use \(H_S=-\log P(S\mid A,Y)\).

There exist constants \(C,c>0\) such that on one event of designs of probability at least \(1-Ce^{-c(r+1)d}\) both of the following hold **simultaneously** for every prior, feature and list cap \(L\) at that design:
1. The true-label and feature surprisals satisfy, for all \(u\ge0\),
\[
 \begin{split}
 \Pr\big[|H_S-(W-Z)_+|>C\sqrt{r+1}+u\mid A\big]&\le C e^{-u},\\
 \Pr\big[|H_F-\min\{W_F,(W-Z)_+\}|>C\sqrt{r+1}+u\mid A\big]&\le C e^{-u/2}.
 \end{split}                                                     \tag{1}
\]
2. Let \(p_L(A,\pi)\) be the best conditional probability of covering the true label by a list of at most \(L\ge1\) labels, without a computation cap. Then
\[
 \big|p_L(A,\pi)-\Pr[Z>W-\log L\mid A]\big|
       \le C\min\{1,(\sqrt{r+1}+\log(d+1))/\sqrt d\}.              \tag{2}
\]
In particular the usual \(\sqrt d\)-scale label list window holds uniformly even for design-selected priors when \(r=o(d)\). At \(r=o(d^2)\), any sure fixed linear margin between \(W-\log L\) and the true location \(t_dd\) gives the corresponding first-order success or failure uniformly: use the more precise brackets in §4, rather than the normal-scale error term in (2).

Conversely, take a fixed odd prime \(q\) and choose \(r_d/d^{3/2}\to\kappa\in(0,\infty)\), \(\sqrt d(t_d-\log q)\to\xi\in\mathbb R\). There are design-dependent priors with exactly \(q^d\) equiprobable labels such that the conditional optimal success at \(L=1\) converges in probability over designs to
\[
           \Phi\!\left( \frac{\xi-\kappa\beta^2}{\sqrt{2\log q}}\right)
      \quad\text{rather than}\quad
           \Phi\!\left( \frac{\xi}{\sqrt{2\log q}}\right).        \tag{3}
\]
The latter would follow from a design-independent-prior information profile at the same prior entropy. This does not claim that the sufficient \(r=o(d)\) condition in (2) is optimal; ranks between the one positive range and the high-rank example are not settled. There is no computational recovery, testing of a concrete scheme, or choice of prior based on actual response values.

## 2. One design event for every pair of labels

For a nonzero difference \(\Delta\in R^r\), the value \(\langle A_i,\Delta\rangle_R\) is uniform in the nonzero ideal \(J=\sum_j \Delta_jR\). For fixed odd \(q\) and sufficiently large \(d\), every such ideal is a product of copies of a base ideal at a fixed dyadic degree \(d_0=d_0(q)\), interleaved by coefficient indices mod \(d/d_0\). Indeed the common irreducible mod-\(p\) factor degree for \(X^d+1\) is \(\operatorname{ord}_{2d}(p)\), which doubles past a fixed base; the base irreducible factors substitute \(X^{d/d_0}\) and have exactly the larger factor degree. Their monic coprime Hensel lifts also substitute, and each local factor over \(\mathbb Z/p^e\) has only powers of its prime ideal. Grouping the free coefficient vectors over the fixed base and taking CRT over \(p\mid q\) proves the product property; see also [the full base-ideal argument](https://github.com/mxym/math/blob/ce786bb5e0060a7574add4ea103adb7c200c0a4f/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-common-law-ambiguity.md#3-uniform-coherence-from-the-fixed-base). Every coordinate projection of a nonzero ideal is nonzero, by multiplying by \(X\) to rotate coordinates with signs. Hence a fundamental coefficient character averages to zero on that ideal.

Set
\[
 T_A(\Delta)=\sum_{i=1}^k\sum_{j=1}^d
                  \cos(2\pi(\langle A_i,\Delta\rangle_R)_j/q).
\]
This is a sum of \(kd/d_0\) independent centered block terms bounded in absolute value by \(d_0\). Hoeffding gives, uniformly in nonzero \(\Delta\),
\[
  \Pr_A(|b^2 T_A(\Delta)|>x)
       \le 2\exp[-x^2/(2d_0 kd b^4)] .
\]
Since \(kd b^4=O(1/d)\), union over at most \(q^{rd}\) nonzero differences shows that \(\sup_{\Delta\ne0}|b^2T_A(\Delta)|\le C_1\sqrt{r+1}\) except with the probability asserted in §1 (take \(C_1\) sufficiently large). This event is defined without reference to any selected prior or feature.

For a fixed design and distinct labels the scalar product calculation, uniform in the two phases, gives
\[
 \log\big(\mathbb E_\nu L_s L_v\big)
       =2b^2 T_A(s-v)+O(kd b^4).
\]
In detail the conditional scalar ratio equals \(1+2b\cos(2\pi(y-u/q))+O(b^4)\), the \(g_b\) integral of each single ratio equals 1 exactly, and the product of the first harmonics contributes \(2b^2\cos(2\pi(u-u')/q)\). The terms of order three vanish (or are absent from this ratio expansion); the log linearization contributes \(O(b^4)\). Thus on the same design event,
\[
             \sup_{s\ne v}\mathbb E_\nu L_s L_v \ \le\ C_0,
         \qquad \log C_0\le C_2\sqrt{r+1},\quad C_0\ge1.          \tag{4}
\]

## 3. Uniform information spectrum after fixing the design

For a fixed design satisfying (4), set \(T_S=\sum_{v\ne S}\pi(v)L_v(Y)\). Under the true joint law,
\[
        \mathbb E T_S=\sum_{s\ne v}\pi(s)\pi(v)
                 \mathbb E_\nu L_s L_v\le C_0.
\]
The mixture density is \(m=e^{Z-W}+T_S\). Bayes' identity makes the difference \(H_S-(W-Z)_+\) equal to \(\log m-(Z-W)_+\). Its positive tail is bounded by Markov applied to \(1+T_S\); its negative tail is bounded by \(\Pr[m(Y)<e^{-u}]\le e^{-u}\), since \(Y\) has density \(m\) and the negative difference can occur only when \(Z-W<0\). This proves the first claim with a shift \(O(\log(2+C_0))\). The argument is valid for all priors at this same fixed design.

For the feature \(F\), let \(m_F(y)=\sum_{s:f_A(s)=F}\pi(s\mid F)L_s(y)\) denote the density conditional on the true feature. Under that conditional law the same overlap bound applies with the restricted prior, so
\[
  \log m_F=(Z-W+W_F)_+ + \mathrm{error}
\]
with the same one-sided tail estimates and shift, uniformly in the feature value. Now \(H_F=W_F+\log m-\log m_F\); subtract the two estimates and use
\[
 W_F+(Z-W)_+-(Z-W+W_F)_+
                   =\min\{W_F,(W-Z)_+\}.
\]
Dividing the surplus threshold between the two errors gives the second bound in (1).

## 4. A list sandwich that works at the atom for \(L=1\)

Fix \(A\) satisfying (4). For all \(\gamma\ge0\),
\[
 \Pr[Z-W+\log L>\gamma\mid A]-C_0e^{-\gamma}
 \ \le p_L(A,\pi)\le\
 \Pr[Z-W+\log L\ge-\gamma\mid A]+e^{-\gamma}.                      \tag{5}
\]
For the upper bound restrict to candidate labels with \(\pi(s)L_s(y)<e^{-\gamma}/L\) inside an output list. At each \(y\), their joint mass against \(\nu(dy)\) is at most \(e^{-\gamma}\), regardless of how the list was chosen. The remainder is the displayed information-spectrum event. For the lower bound use only the existence of the largest-posterior-mass size-\(L\) decision. If the true weight \(\pi(s)L_s(y)> e^\gamma/L\) and it was not included, at least \(L\) distinct wrong weights are at least this large. Then \(T_S>e^\gamma\), a bad event of probability at most \(C_0e^{-\gamma}\). This proves (5) and handles exact single-label comparison without moving a threshold past an atom of posterior surprisal at zero. It is not an efficiency bound or a method to compute the posterior.

The conditional distribution of \(Z\) is design and label independent because \(g_b\) is invariant under all grid shifts. Its scalar summands are uniformly \(O(b)\), with means \(b^2+O(b^4)\), variances \(2b^2+O(b^4)\), and absolute centered third moments \(O(b^3)\) by the first harmonic expansion and circle integration. Thus \(E Z=t_dd+O(d^{-1})\), \(\operatorname{Var}Z=2t_dd+O(d^{-1})\), and Berry–Esseen gives Kolmogorov error \(O((kd)^{-1/2})\) from its standardized Gaussian. In particular its probability in any interval of length \(2\gamma\) is \(O(\gamma/\sqrt d+d^{-3/2})\), uniformly in the interval's location. Because \(Z\) and \(W\) are independent conditional on \(A\), the same bound applies to the uncertain interval in (5). Choosing \(\gamma=\log C_0+2\log(d+1)\) proves (2); tightness near linear margins follows directly from (5) and \(\gamma=o(d)\) if \(r=o(d^2)\).

## 5. A failure of the unchanged profile at higher rank

For an odd prime \(q\), the dyadic ring is a product of a fixed number of finite fields each of cardinality \(e^{\Omega(d)}\). Look at the first \(r-1\) rows of the design. Their matrix has full row rank in every field factor with probability \(1-o(1)\), even though \(r\) grows: in a field of size \(Q\), for an \((r-1)\times r\) uniform matrix, the failure probability is bounded by \(\sum_{i=0}^{r-2} Q^{i-r}\le1/(Q(Q-1))\) by successive independent rows. A finite union bounds the factors. On this event the null module of these rows is free of rank one over \(R\). Equivalently choose any nonzero generator of the null line in each field and combine them; the resulting \(h\in R^r\) is nonzero in each field factor, so the map \(x\mapsto hx\) is a bijection from \(R\) to that null module. The choice is a deterministic function of only the first \(r-1\) rows.

Define \(\pi_A\) to be uniform on this null module, or (on the vanishing exceptional event) on any fixed set of \(q^d\) distinct labels. All first \(r-1\) responses on the main event have conditional law independent of \(S\), even after observing every design row. For each subsequent independent row the coefficient \(\langle A_i,h\rangle_R\) is uniform on \(R\), since the map is onto on every field factor; these effective coefficients are independent conditional on the first rows. Thus the remaining statistical experiment on the scalar parameter \(x\in R\) is exactly the usual rank-one experiment with \(k'=k-r+1\) rows. No selection uses the responses. In the claimed regime \(r<k\) eventually and
\[
      \sqrt d(k'b^2-\log q)\ \longrightarrow\ \xi-\kappa\beta^2 .
\]
Apply (5) and (2) in rank one to this induced random design, now with the ordinary uniform prior on \(x\). The CLT in §4 yields the conditional success limit in (3). By contrast the surrogate probability based on all \(k\) coordinates while using \(W=d\log q\) has the stated larger Gaussian limit. This illustrates why a prior chosen from the realized design can matter, not how to recover a label from ordinary observations.

## 6. Relation to earlier results

[Lyubashevsky–Peikert–Regev](https://web.eecs.umich.edu/~cpeikert/pubs/ideal-lwe.pdf) give the ring model and worst-case/average-case search and decision reductions under separate hypotheses. The [repository theorem on arbitrary fixed priors](https://github.com/mxym/math/blob/15a25c0d1d01551372cfb03794958adc753ca3b6/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-posterior-surprisal-coarsenings.md) already proves averaged first-moment overlap and corresponding posterior and list results for priors specified before the design. [Polyanskiy–Poor–Verdú](https://people.lids.mit.edu/yp/homepage/data/finite_block.pdf) provide the general finite-block information-spectrum context. The new assertion is one high-probability event for *all* possible priors and features after design, and a strict higher-rank separation showing that the unchanged second-order conclusion cannot be presumed under that stronger quantifier. Neither this conditional information result nor the example addresses the classical polynomial-time problem or any deployment.
