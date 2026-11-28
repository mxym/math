# Sum-of-squares barriers for correlated sparse ring-equation orbits

Sparse random *ring rows* produce full families of cyclically related scalar equations. They are not independent scalar constraints. We prove a linear-degree gap for the standard coefficient-indicator sum-of-squares relaxation for these entire orbits, and a surviving growing-degree gap when the equations are expanded into ternary linear gates. The random design is sparse by definition; the result does not assert a gap for uniformly dense ring coefficients or for arbitrary proof systems.

## 1. Model and claims

Fix a prime \(q\), including \(q=2\), and let \(R=\mathbf F_q[X]/(X^d+1)\) for dyadic \(d\to\infty\). Let \(k\ge1\) independent ring rows \(A_i\) have independent coefficients of law
\[
 (1-p)\delta_0+p\,U_{\mathbf F_q},\qquad
 p=p_d\to0,\qquad \log(kd)=o(dp^2).                              \tag{1}
\]
For each row take *all* \(d\) scalar equations in \(A_i s=B_i\), with variables \(s_0,\ldots,s_{d-1}\in\mathbf F_q\). Let their coefficient vectors be \(a_{ij}\) and their right-hand sides \(b_{ij}\) for \(0\le j<d\). For given right-hand sides, the actual value is the largest fraction of the \(kd\) scalar equations satisfied by one assignment. This is also a rescaled maximum likelihood score for the elementary scalar error model \((1-\nu)\delta_0+\nu U_{\mathbf F_q}\) with fixed \(0<\nu<1\); only the normalized agreement problem is used in the proof.

With probability \(1-o(1)\) over the public ring rows, *simultaneously for every choice of right-hand sides*:

* The standard coefficient-indicator SoS relaxation has value 1 at degree \(\lfloor c_q d\rfloor\), for some \(c_q>0\). Here the representation has variables \(x_{j,a}=\mathbf1_{\{s_j=a\}}\) with the usual one-hot relations, and an equation indicator is the degree-\(\mathrm{wt}(a_{ij})\) polynomial for its satisfied assignments. The same pseudoexpectation treats each scalar equation as exactly satisfied against all allowed moment multipliers.
* Expand each equation into any binary tree of local addition/scaling gates summing its nonzero terms. Use one-hot variables for each gate, with the local gate relations (at most three field variables per gate) enforced exactly, and optimize the fraction of terminals matching their respective right-hand sides. There is a pseudoexpectation of degree \(\Omega_q(1/p)\) satisfying all local gates and all terminal pins. The true value of this expanded formulation is the same as the original value. No claim is made for circuits with arbitrary intervening auxiliary transformations.

If the \(B_i\) are independent uniform elements of \(R\), independent of the \(A_i\), then conditional on any fixed realized design, with probability at least \(1-e^{-d}\) the actual value is at most
\[
 \frac1q+\sqrt{\frac{\log q+1}{2k}}.                            \tag{2}
\]
This gives a constant gap for large fixed \(k\), and a gap tending to \(1-1/q\) when \(k\to\infty\). No independent-scalar-row assumption is used. In particular, the right-hand sides in the SoS statement can be arbitrary, whereas the bound on true value in (2) specifically concerns uniform independent right-hand sides.

## 2. Shift-dependent expansion from a read bound

For the coefficient pairing modulo \(q\), the scalar row has vector \(a_{ij}=X^j\overline{A_i}\), where the bar is \(X\mapsto X^{-1}\). This follows because the transpose of multiplication by the signed shift \(X\) is multiplication by \(X^{-1}\). Thus for each fixed row and shift, the underlying coefficient entries are permuted with signs, and the same output position across two distinct shifts of the same \(A_i\) reads two distinct coefficient entries.

Put \(L=\lfloor1/p\rfloor\). Fix a nonzero combination of \(\ell\) distinct scalar rows with nonzero multipliers \(c_{ij}\in\mathbf F_q\), where \(1\le\ell\le2L\). At each fixed output coordinate the sum
\[
 V=\sum_{(i,j)}c_{ij}a_{ij}
\]
uses \(\ell\) independent entries, even if several scalar rows come from the same public ring row. Their signs and nonzero multipliers preserve the law in (1). A sum of such entries is zero when all uniform components are absent; once any uniform component is present its law is uniform. Thus the marginal nonzero probability at each position is
\[
 \rho_\ell=(1-1/q)[1-(1-p)^\ell].                               \tag{3}
\]
Across positions the indicators are generally dependent. Each independent base entry is read in at most \(\ell\) output indicators, once for each shift of its ring row in the combination. This is a read-\(\ell\) family. By the read-family Chernoff bound,
\[
 \Pr\big[\mathrm{wt}(V)<d\rho_\ell/2\big]
           \le \exp[-d\rho_\ell/(8\ell)]\le e^{-c'_q dp}.         \tag{4}
\]
For the first inequality one may integrate over the independent base entries one at a time, applying Hölder with exponent \(\ell\) to the at most \(\ell\) currently dependent factors at each step (with a constant filler if necessary). This gives the moment bound
\(\mathbb E e^{u\sum Z_j}\le\prod_j (\mathbb E e^{u\ell Z_j})^{1/\ell}\).
The usual binomial lower-tail estimate then loses only the read factor \(\ell\). For the second inequality, \(p\ell\le2\) and
\(1-(1-p)^\ell\ge 1-e^{-p\ell}\ge (1-e^{-2})p\ell/2\).
This is where independent scalar row bounds cannot simply be substituted.

The number of combinations with \(\ell\le2L\) is at most \((2L)(qkd)^{2L}\). By (1) its logarithm is \(o(dp)\), so (4) holds for all these combinations at once with probability \(1-o(1)\). In particular no nonzero combination of support at most \(2L\) vanishes. If \(L\le\ell\le2L\), (3) is bounded below by a positive constant depending only on \(q\), because \(pL\ge1/2\) eventually. All these intermediate combinations therefore have weight at least \(\gamma_q d\) for some \(\gamma_q>0\). Separately the raw row weight is at most \(2pd\) for every \(i,j\) with probability \(1-o(1)\) by a scalar binomial bound on each \(A_i\): shifts have identical weight, and \(\log k=o(dp)\). Work on the intersection of these row events, which is independent of the right-hand sides.

## 3. Bounded-width derivations cannot reach a contradiction

Let \(w=\lfloor c_q d\rfloor\) for \(0<c_q<\gamma_q\), so that all raw scalar constraints have width \(o(w)\). Work in the space of pairs \((a,b)\in\mathbf F_q^d\times\mathbf F_q\), interpreted as linear equations \(a\cdot s=b\). The width is Hamming weight of \(a\). Start with the raw equations and \((0,0)\). The width-\(w\) closure \(\mathcal D_w\) allows field scaling and addition of already derived pairs when the output width is at most \(w\).

There is no \((0,b)\), \(b\ne0\), in this closure, for any values of the original \(b_{ij}\). In a derivation attach to every pair its provenance vector of coefficients over the original equation list, scaling and adding those vectors along the same steps. A contradiction has nonzero provenance, supported on more than \(2L\) original equations by §2. Starting at support 0 or 1, an addition yields support at most twice the larger parent support; scaling never increases it. Thus there must be a first step of support at least \(L\), and its support is at most \(2L\). By §2 that step has width at least \(\gamma_q d>w\), contradiction. This argument works for every possible provenance created by a derivation, without choosing a canonical representation of a linear combination.

It follows that a short vector \(a\) has at most one right-hand side \(b\) in \(\mathcal D_w\), since two different ones could be subtracted at width zero. Individual raw rows and all their scalar multiples have their required right-hand sides in the closure.

## 4. Explicit prime-field pseudoexpectation

Set \(\omega=e^{2\pi i/q}\) and \(\chi_u(s)=\omega^{u\cdot s}\). Define a functional on the span of label characters of coordinate weight \(\le w\) by
\[
 \widetilde{\mathbb E}\chi_u=
 \begin{cases}
    \omega^{b},& (u,b)\in\mathcal D_w,\\
    0,&\text{if no such pair exists}.
 \end{cases}                                                     \tag{5}
\]
It is normalized by \((0,0)\), and conjugation is preserved because scalar negation preserves derivability. For weights \(\mathrm{wt}(u),\mathrm{wt}(v)\le\lfloor w/2\rfloor\), define \(u\sim v\) when \(u-v\) is derivable. This is an equivalence relation: transitivity uses addition with output vector \(u-z\) of weight at most \(w\). Entries \(\widetilde{\mathbb E}\chi_{v-u}\) vanish between different classes. Within a class, let \(b_u\) be the right-hand side for \(u-u_0\) relative to its representative. Addition and uniqueness show \(\widetilde{\mathbb E}\chi_{v-u}=\omega^{b_v-b_u}\); thus each class moment matrix is rank one and positive semidefinite. Hence \(\widetilde{\mathbb E}|F|^2\ge0\) for any linear combination \(F\) of the weight-\(\lfloor w/2\rfloor\) characters.

Substitute \(x_{j,a}(s)=q^{-1}\sum_{c\in\mathbf F_q}\omega^{-ca}\chi_{ce_j}(s)\) into a real polynomial of total degree at most \(w\). Its Fourier support has weight at most \(w\), so (5) acts on it. This defines a real degree-\(w\) pseudoexpectation, with positivity from the moment matrix, and it satisfies all one-hot identities because they are identities of the substituted functions.

For any raw row \(a\) with right-hand side \(b\), and any vector \(u\) for which both \(u\) and \(u+c a\) have weight at most \(w\),
\[
 \widetilde{\mathbb E}\chi_{u+ca}=\omega^{cb}\widetilde{\mathbb E}\chi_u
                                                     \quad(c\in\mathbf F_q).
\]
Indeed derivability of one implies the other by adding or subtracting the raw scaled equation, and the right-hand sides then differ by \(cb\). Expanding the satisfied-row indicator \(I_{a,b}=q^{-1}\sum_c\omega^{-cb}\chi_{ca}\) now gives
\(\widetilde{\mathbb E}[P(I_{a,b}-1)]=0\)
for every multiplier \(P\) under the usual degree budget \(\deg(P)+\mathrm{wt}(a)\le w\). Thus every equation has expected score 1. This is the maximum possible: since \(2\mathrm{wt}(a)\le w\), the one-hot relations give \(I_{a,b}^2=I_{a,b}\) at that degree, and positivity of \((1-I_{a,b})^2\) gives \(\widetilde{\mathbb E}I_{a,b}\le1\) for any feasible pseudoexpectation. To justify the identity, expand pairs of satisfied local assignments: unequal assignments vanish by the coordinate one-hot orthogonality relations, and equal assignments reduce by the idempotence relations. All products used have degree at most \(2\mathrm{wt}(a)\).

For expanded circuits, assign each gate variable its exact partial linear form in the input variables. A gate within an equation of weight at most \(K=\lceil2pd\rceil\) depends on at most \(K\) underlying coordinates. Replacing its one-hot variable by the indicator of that partial linear form therefore maps any degree-\(m\) polynomial to a field function of coordinate degree at most \(Km\), and one may use the standard multilinear indicator representation of the pullback. Choose \(m=\lfloor w/K\rfloor\), which is \(\Omega_q(1/p)\). Pull back before applying (5). Positivity follows from the base bound since the pullback of a degree-\(\lfloor m/2\rfloor\) polynomial has degree at most \(\lfloor w/2\rfloor\). Internal gate equations and all one-hot equations become exact identities of functions. A terminal pin becomes a base raw satisfied-row indicator, so its multiplier condition follows by the same Fourier shift argument: a multiplier of degree \(\le m-1\) contributes at most \(K(m-1)\) coordinates, and adding the terminal row costs at most \(K\). This proves the local-gate claim. The substitution proves the **lower** degree bound and does not purport to characterize stronger encodings or the exact threshold.

Finally, for a fixed assignment under independent uniform \(B_i\), all \(kd\) scalar correctness indicators are independent Bernoulli \(1/q\), even conditional on any public design. Hoeffding's bound followed by a union over \(q^d\) assignments gives (2). Consequently the absence of control in the relaxation is a gap against the actual value on typical null instances, not just against another relaxation.

## 5. Earlier results and limits

[Strongly Refuting Semirandom Linear Systems in Subexponential Time, §4, Theorem 4.2](https://arxiv.org/html/2609.30052v1#S4) proves a linear SoS gap for independent sparse binary coefficient rows. Its width argument is the close antecedent of §3. It does not establish the needed concentration for full rotation orbits of the same vector, or the fixed-prime character construction used here. The read-family probabilistic bound is from [Gavinsky–Lovett–Saks–Srinivasan](https://arxiv.org/abs/1205.1478); the new ingredient in §2 is that each individual combination at an output position reads distinct entries, while across positions a base entry is read at most as many times as there are shifted equations. The earlier [engineered sparse-unit SoS example](https://github.com/mxym/math/blob/6f434fa4abf32abfb96330cdfcb43f13a80d0c96/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-sparse-unit-sos-gap.md) relied on a constructed worst-case design rather than random full shift families.

This applies to the specified sparse ensemble and proof representations only. It is not a solver, a lower bound for unrestricted algorithms, or a result about uniformly dense designs or cryptographic implementations.
