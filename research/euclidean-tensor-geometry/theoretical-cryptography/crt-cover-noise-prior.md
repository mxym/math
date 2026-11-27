# CRT cover versus preservation of the noise prior in a normal-form simulation

## Scope and result

[Lyubashevsky–Peikert–Regev, *A Toolkit for Ring-LWE Cryptography*, Lemma 2.24 and Claim 2.25](https://web.eecs.umich.edu/~cpeikert/pubs/toolkit.pdf) use a single invertible coefficient to change the hidden prior in a standard normal-form proof, with a nonnegligible unit fraction for their cyclotomic setting. If coefficients in a more general finite quotient are rarely units, several rows can cover all local factors. The resulting simulation can still have an exact law, but the new prior is a CRT **recombination** of independently drawn errors, in general not the original prior. We quantify this distinction.

Everything below is a distribution identity under a specified abstract model. It concerns a positive normal-form simulation into a different explicitly identified prior, and conditions under which that prior agrees or is close to the original one. It neither extracts the hidden value from samples nor claims security or insecurity of any concrete construction. The verification program uses only small synthetic probability spaces.

## 1. Exact simulated prior under a CRT cover

Let \(A=\prod_{j=1}^g A_j\) be a finite commutative ring written as a product of finite local rings, and let \(U=\prod_j U_j\) be a finite unital \(A\)-module, using the decomposition by the CRT idempotents. Write \(q_j>1\) for the size of the residue field of \(A_j\). Choose \(m\) **prefix** observations independently conditional on any fixed common hidden value \(s\in U\); the row coefficients \(a_i\) are independent uniform on \(A\). In the noisy experiment, the right member is \(b_i=a_i s+e_i\) with independent errors \(e_i\sim\chi\) on \(U\) independent of the coefficients. In the reference experiment, the right members are independent uniform on \(U\) and independent of the coefficients. Any later observations are fresh, with the same independent uniform coefficients and a specified fresh error law \(\psi\) in the noisy experiment; \(\psi\) need not equal \(\chi\).

A **cover** means each \(j\) has at least one index \(i\le m\) such that \((a_i)_j\) is a unit. Its probability in both experiments is exactly
\[
p_{\mathrm{cover}}=\prod_{j=1}^g(1-q_j^{-m}),\qquad
1-p_{\mathrm{cover}}\le\sum_j q_j^{-m}\le g\,2^{-m}.
\tag{1}
\]
Indeed the unit condition in each finite local ring is nonzero image in its residue field, and the entries of the coefficient array are independent across rows and local factors. Conditional on cover, choose any row index \(T_j\) having a unit in factor \(j\) by a rule depending only on the prefix coefficients and optional independent randomness. Form the formal pivot by local projection: its coordinates are \((a_0)_j=(a_{T_j})_j\), \((b_0)_j=(b_{T_j})_j\). The first is a unit in the product. In the noisy experiment \(b_0=a_0s+E_0\) with
\[
(E_0)_j=(e_{T_j})_j.
\]
Consider the partition \(\pi\) of \(\{1,\ldots,g\}\) into sets that share the same \(T_j\). Conditional on the entire coefficient selection, \(E_0\) has the product law \(\bigotimes_{B\in\pi}\chi_B\), where \(\chi_B\) is the \(B\)-marginal of the original error. Thus the hidden prior in the successful simulation, with the prefix discarded, is exactly
\[
\mathcal R(\chi)=\mathbb E_{\pi\mid\mathrm{cover}}\bigotimes_{B\in\pi}\chi_B.
\tag{2}
\]
For clarity on the normal-form distribution step, applying the usual affine recentering to a fresh pair \((a,b)\) uses \(a'=-a_0^{-1}a\) and \(b'=b+a'b_0\). In the noisy experiment this identity gives \(b'=a'E_0+e\), with \(a'\) uniform and the fresh \(e\sim\psi\) unchanged and independent. For a whole batch, these become conditionally independent samples with common new prior \(E_0\); there is no per-sample refresh of it. In the reference experiment \(b\) was independently uniform, so even conditionally on the pivot the transformed fresh data are independent and uniform. These assertions use only the indicated finite module and iid model; they do not postulate approximation of \(\chi\) by a centered Gaussian or factorization of any canonical error. If an argument expects the new hidden prior to remain \(\chi\), replacing (2) by \(\chi\) incurs at most \(d_{\rm TV}(\mathcal R(\chi),\chi)\) in the **entire batch** by data processing from the one draw of the prior. No multiplicative factor for the number of fresh rows is necessary for this one prior comparison.

## 2. First-available selection: retention coefficients and the exact fixed points

For the rule choosing the first available row in each factor, the labels \(T_j\), conditional on cover, are independent and
\[
p_{j,i}:=\Pr(T_j=i\mid\mathrm{cover})
=\frac{(1-q_j^{-1}) q_j^{-(i-1)}}{1-q_j^{-m}},\quad 1\le i\le m .
\tag{3}
\]
The condition factors across \(j\), so no hidden coefficient dependence has been omitted. For any nonempty \(S\subseteq[g]\), the chance its coordinates come from a single row is
\[
c_S=\sum_{i=1}^m\prod_{j\in S}p_{j,i}
=\frac{\prod_{j\in S}(1-q_j^{-1})}{\prod_{j\in S}(1-q_j^{-m})}
  \frac{1-\left(\prod_{j\in S}q_j^{-1}\right)^m}{1-\prod_{j\in S}q_j^{-1}}.
\tag{4}
\]
For instance, with two factors of residue size two and a growing number of prefix rows, the pair retention tends to \(1/3\), not one.

For any distribution \(\chi\), equation (2) preserves every one-factor marginal. For any pair \(i,j\) the retained joint law is exactly
\[
(\mathcal R\chi)_{\{i,j\}}
=c_{\{i,j\}}\chi_{\{i,j\}}+(1-c_{\{i,j\}})\chi_i\otimes\chi_j,
\tag{5}
\]
where the same statement holds for other coefficient-only selectors with their corresponding pair co-selection probability. Hence \(d_{\rm TV}(\mathcal R\chi,\chi)\) is at least
\((1-c_{\{i,j\}})d_{\rm TV}(\chi_{\{i,j\}},\chi_i\otimes\chi_j)\).
For general dependence an upper bound is
\[
d_{\rm TV}(\mathcal R\chi,\chi)
\le \sqrt{\tfrac12\,\mathbb E_{\pi\mid\mathrm{cover}}\bigl[\sum_{B\in\pi}H(\chi_B)-H(\chi)\bigr]},
\tag{6}
\]
with entropy in nats. For this bound, use convexity of total variation in the first argument, Pinsker's inequality with \(D(\chi\Vert \bigotimes_B\chi_B)=\sum_B H(\chi_B)-H(\chi)\), and Jensen. Coordinates of zero mass pose no problem since the product of the corresponding marginals is positive on the support of \(\chi\).

There is an exact characterization under first-available selection and \(m\ge2\):
\[
\mathcal R\chi=\chi
\quad\Longleftrightarrow\quad \chi=\bigotimes_{j=1}^g\chi_j .
\tag{7}
\]
To prove the converse direction, each recombined law in (2) has entropy at least \(H(\chi)\), with equality only if \(\chi\) factorizes along that partition, by the nonnegative relative entropy formula used in (6). Entropy concavity implies that a fixed point must give equality in every partition of positive support. By (3), every bipartition can be obtained by assigning its two sides to rows 1 and 2, so every singleton is independent of its complement. The chain rule for the distribution now gives independence of all coordinates. The forward implication from independence is immediate. For \(g=1\) the condition is vacuous, as expected; for \(m=1\) the prior is unchanged whenever the pivot is accepted.

## 3. Exact effects on higher-order interactions

There are two descriptions that do not presume pairwise dependence is enough.

* For an additive character \(\omega=(\omega_j)\) of \(U\), let \(\omega_B\) mean its restriction to the coordinates in \(B\), extended by the trivial character on the rest. Taking the expectation in each recombined block yields the exact Fourier law
  \[
  \widehat{\mathcal R\chi}(\omega)
  =\mathbb E_{\pi\mid\mathrm{cover}}\prod_{B\in\pi}\widehat\chi(\omega_B).
  \tag{8}
  \]
* Relative to any strictly positive product law \(\nu=\bigotimes_j\nu_j\), let
  \(\chi=\nu(1+\epsilon f)\), where \(\mathbb E_\nu f=0\) and \(\epsilon\) is small enough that this is a distribution. In the Hoeffding decomposition \(f=\sum_{\varnothing\ne S\subseteq[g]}f_S\), each \(f_S\) depends only on \(S\) and has zero expectation integrating over **any** coordinate in \(S\). The \(B\)-marginal of \(\chi\) has density \(1+\epsilon\sum_{S\subseteq B} f_S\) relative to \(\nu_B\). Multiplying these densities over the blocks in (2) gives
  \[
  \mathcal R\chi=\nu\left(1+\epsilon\sum_{\varnothing\ne S}c_S f_S+O(\epsilon^2)\right)
  \tag{9}
  \]
  on the fixed finite space. The remainder is in sup norm at fixed \(f\) and \(g\). If \(f\) consists of a single pure interaction \(f_S\), (9) is **exact** with no remainder: either all of \(S\) is kept together or every block sees a zero marginal of that interaction. In this case the TV error is exactly
  \((1-c_S)d_{\rm TV}(\chi,\nu)\).
  
These formulas quantify why marginal matching alone cannot justify the original prior in the new proof. For a general coefficient-only rule the same formulas use its partition co-selection probabilities rather than (4).

## 4. Limit for arbitrary coefficient-only selectors

Suppose each \(U_j\) has at least two elements. Choose \(\chi\) supported on two common tags: choose a uniform bit, and in every factor place the designated matching representative of that bit. If a partition has \(r_\pi\) blocks, the recombined tags are independent from block to block, and the chance all match is \(2^{1-r_\pi}\). Conditional on matching, the two diagonal outcomes are still equally likely. Consequently
\[
d_{\rm TV}(\mathcal R\chi,\chi)=1-\mathbb E[2^{1-r_\pi}\mid\mathrm{cover}]
\ge\tfrac12\Pr(\text{no single unit row}\mid\mathrm{cover}),
\tag{10}
\]
for **any** coefficient-only CRT selection rule. Indeed a single selected row would be a unit in every factor. The unit probability of one whole row is \(\prod_j(1-q_j^{-1})\); thus, when the residue field sizes are uniformly bounded and the number of factors grows, any polynomial number of rows has a negligible chance of containing one unit, by the union bound. On the other hand \(m\) logarithmic in the number of factors suffices for cover by (1). This illustrates that cover alone cannot imply small error of the prior in arbitrary abstract finite products. Equation (10) uses a standalone synthetic law and is not an assertion about a Gaussian or a real cryptosystem.

## 5. The change is also visible in a centered canonical Gaussian model

Consider the power-of-two cyclotomic ring \(R=\mathbb Z[\zeta_{2^r}]\) in its usual Euclidean canonical embedding, with dimension \(n=2^{r-1}\) under the convention that a complex embedding pair contributes twice its squared modulus. The coefficient powers \(1,\zeta,\ldots,\zeta^{n-1}\) are orthogonal of squared length \(n\), since their inner products are the traces of the corresponding powers and vanish for each nonzero difference in this range. Its first nonzero lattice shell is the \(2n\) vectors \(\{\pm\zeta^j\}\), all units. In this family the codifferent differs by a scalar from \(R\); rescaling both the canonical width and the lattice gives the same assertion in that module, with \(n\) in the exponent below replaced by its squared shortest length.

Reduce a centered discrete Gaussian of width \(\sigma\) on this ring modulo any fixed quotient \(qR\) with at least two local factors. Put \(a=\exp(-\pi n/\sigma^2)\). As \(\sigma\to0\), for fixed \(n,q\) its law on the quotient is
\[
\chi_\sigma=(1-2n a)\delta_0+a\sum_{u\in\{\pm\zeta^j\}}\delta_{\bar u}+O_{\rm TV}(a^2).
\tag{11}
\]
The expansion follows from the shortest shell and the next-shell energy bound \(2n\); multiplicities after reduction do not change it. Every reduced vector in the first shell is nonzero in each local factor, because the original vector is a unit. In contrast, in a recombination with at least two blocks, the order-\(a\) contribution of any one first-shell draw is nonzero **only** in its proper block. Simultaneously drawing from two blocks is order \(a^2\). For a partition with \(r_\pi\ge2\), the order-\(a\) change is therefore positive only at proper nonempty support masks, negative at the origin by \((r_\pi-1)2n a\), and negative at full masks by \(2n a\). The sign locations are shared by all such partitions. Averaging them, and noting the unchanged one-block partition, gives
\[
d_{\rm TV}(\mathcal R\chi_\sigma,\chi_\sigma)
=2n a\,\mathbb E[r_\pi\mathbf 1_{r_\pi\ge2}\mid\mathrm{cover}]+O(a^2).
\tag{12}
\]
For first-available with \(g,m\ge2\), the prefactor is strictly positive. Thus exact preservation fails even for this abstract canonical Gaussian family; (12) gives the leading error at fixed quotient, not a uniform bound in dimension or a practical-parameter estimate.

## Primary comparison and replay

The one-pivot construction and the cyclotomic unit fraction are already in Toolkit Lemma 2.24 and Claim 2.25. The partition recombinators in (2) are also classical in a different context, e.g. [Baake, Baake and Salamat, *The general recombination equation*](https://arxiv.org/abs/1409.1378); the entropy and Fourier consequences above use ordinary probability on a product space. This note identifies the exact induced prior for the multiple-cover variant and quantifies which prior assumptions a positive normal-form proof can and cannot carry through it. No general hardness statement follows without the corresponding source and target assumptions and actual input model.

Run **node verify-crt-cover-noise-prior.js** for exact first-available partition probabilities, signed interaction checks, the synthetic common-tag comparison, and a replay of the Gaussian first-shell coefficient via finite coefficient arrays.
