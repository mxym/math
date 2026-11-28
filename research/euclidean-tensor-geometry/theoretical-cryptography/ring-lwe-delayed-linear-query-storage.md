# The delayed linear-query storage window in broad ring learning

A summary is formed **before** knowing which linear function of the hidden label will later be requested. We compute the optimal small success advantage at the statistical critical window, for a near-full summary with a growing information deficit. A phase split of the posterior reduces the problem to a noiseless one-way communication constant; a finite-field graph attains that constant asymptotically. This is a storage/communication result, not an efficient way of obtaining the posterior label.

## 1. Model and main result

Fix an odd prime \(q\), dyadic \(d\), \(R=\mathbf F_q[X]/(X^d+1)\), \(b=\beta/d\) for fixed \(\beta>0\), and \(B=\log q\). The unknown label \(S\) is uniform in \(R=\mathbf F_q^d\) in its coefficient basis. The public ring rows \(A_i\) are independently uniform. The sender sees all responses \(Y_i=A_iS/q+E_i\) modulo the coefficient torus, with iid scalar wrapped noise density \(f_b(y)=\sum_n b^{n^2}e^{2\pi i ny}\). Both parties know \(A\), only the sender sees \(Y\), and \(T\) is the number of rows with \(t_d=Tb^2\to B\).

The sender sends a single message. *After* the message, the receiver obtains \(U\) uniform in \(\mathbf F_q^d\), independent of everything so far, and must report the scalar \(U\cdot S\) in \(\mathbf F_q\). There is no feedback and no computational bound. Let \(P_*(A)\) be the optimal conditional success probability over all such procedures. Suppose an integer \(\ell=\ell_d\to\infty\) obeys \(q^\ell\sqrt{\log d}/d^{1/4}\to0\), and the classical message has at most \(L=q^{d-2\ell}\) possible values. Then
\[
 \mathbb E_A\left|
  q^\ell\big(P_*(A)-1/q\big)
     -(1-1/q)\Phi\!\left(\frac{\sqrt d(t_d-B)}{\sqrt{2t_d}}\right)
            \right|\longrightarrow0 .                         \tag{1}
\]
In particular, for \(\sqrt d(t_d-B)\to\xi\) this gives the success advantage coefficient \((1-1/q)\Phi(\xi/\sqrt{2B})\).

For comparison, the same formula holds if the classical message is replaced by an unassisted quantum system of dimension \(L\), or an entanglement-assisted quantum system of dimension \(q^{(d-2\ell)/2}\). The latter uses at most arbitrary finite preshared entanglement independent of the source and query. Since \(d\) is dyadic and even, that dimension is integral. These are optional information-theoretic comparisons for the same delayed-query problem; the main result is classical.

## 2. Two branches of the posterior, with a quantitative error

Let \(Q\) be the independent-coordinate reference with scalar density \(g_b(y)=q^{-1}\sum_{a\in\mathbf F_q} f_b(y-a/q)\). Write \(L_s=dP_{Y\mid A,s}/dQ\), \(F=q^{-d}\sum_s L_s\), \(\pi_s(Y)=L_s(Y)/(q^dF(Y))\), and \(Z=\log L_S(Y)\) at the true label. A finite overlap estimate is
\[
 \sup_{s\ne v}\mathbb E_{A,Q}L_s L_v\le 1+O(d^{-1}).             \tag{2}
\]
For completeness, for the scalar density ratio split its Fourier numerator into residues mod \(q\) and divide by \(g_b\); the resulting functions are orthogonal in \(L^2(g_b)\) by their distinct grid-translation characters. Their squared norms are \(1\) at residue zero, \(b^2+O(b^8)\) at \(\pm1\), and \(O(b^8)\) otherwise. For distinct labels, the difference shift in one public row is uniform on the nonzero ideal \(I=(s-v)R\). The row overlap sums products of the scalar squared norms over \(I^\perp\), the coefficient-dot annihilator. This is a proper ideal by the signed shift adjoint \(X\mapsto X^{-1}\). It contains no signed monomial or signed binomial at distinct positions, since each is a unit: in every residue field the image of \(X\) has exact order \(2d\). Thus the row overlap is at most \(1+O(db^8+d^3b^6)\) by bounding all terms with a higher residue weight or at least three signed sites. Multiplication over \(T=O(d^2)\) rows proves (2).

For the true experiment let \(R_S=q^{-d}\sum_{v\ne S} L_v(Y)\). Then \(\mathbb E R_S\le1+O(d^{-1})\) by (2), and
\(\pi_S=e^{Z-dB}/(e^{Z-dB}+R_S)\).
Set \(\gamma=20\log d\). When \(Z-dB\ge\gamma\) and \(R_S\le e^{\gamma/2}\), we have \(1-\pi_S\le e^{-\gamma/2}\); the second condition fails with probability \(O(e^{-\gamma/2})\) by Markov. When \(Z-dB\le-\gamma\) and \(F(Y)\ge e^{-\gamma/2}\), we have \(\pi_S\le e^{-\gamma/2}\). The latter condition fails with probability at most \(e^{-\gamma/2}\) under the true mixture for each \(A\), since it has reference density \(F\). These are bounds under the true experiment, not uniformly for arbitrary selected responses.

The law of \(Z\) is independent of \(S,A\): it is a sum of \(Td\) iid scalar log ratios \(\log(f_b(E)/g_b(E))\) with \(E\sim f_b\). The scalar cosine expansion gives mean \(b^2+O(b^4)\), variance \(2b^2+O(b^4)\), and third absolute centered moment \(O(b^3)\); terms odd in the first cosine integrate to zero. Thus the mean and variance of \(Z\) are \(t_dd+O(d^{-1})\) and \(2t_dd+O(d^{-1})\). The Berry–Esseen bound is \(O(d^{-3/2})\), since \(Td\,b^3=O(1)\). Put
\[
 p_d=\Phi\!\left(\frac{\sqrt d(t_d-B)}{\sqrt{2t_d}}\right),\qquad
 \varepsilon_d=\frac{\log d}{\sqrt d}.
\]
Then \(\Pr(|Z-dB|\le\gamma)=O(\varepsilon_d)\) and \(\Pr(Z>dB)=p_d+O(\varepsilon_d)\), the same conditional on any design.

Let \(M(Y)=\max_s\pi_s(Y)\), and let \(C=\{M(Y)>1/2\}\), with \(D=C^c\). The preceding estimates show
\[
 \begin{split}
 \mathbb E_A|\Pr(C\mid A)-p_d| &=O(\varepsilon_d),\\
 \mathbb E[(1-M(Y))\mathbf1_C]&=O(\varepsilon_d),\\
 \mathbb E\!\left[\mathbf1_D\sum_s\pi_s(Y)^2\right]
                  &=O(\varepsilon_d).                         \tag{3}
 \end{split}
\]
To verify, the probability that the true posterior weight belongs to \([d^{-5},1-d^{-5}]\) is \(O(\varepsilon_d)\). The event \(\{\pi_S>1/2\}\) agrees with \(\{Z>dB\}\) outside an event of this order. Conditional on \(Y,A\) its probability is exactly \(M(Y)\mathbf1_C\), the winning label being unique on \(C\). On \(C\), either \(1-M<d^{-5}\), or \(M\) lies in the middle interval and is sampled as \(\pi_S\) with conditional probability at least \(1/2\). This bounds the second line and, combined with the comparison at each design averaged over the errors, gives the first line. On \(D\), the collision term in expectation equals \(\mathbb E[\pi_S\mathbf1_D]\); since \(\pi_S\le1/2\) there, it is at most \(d^{-5}\) plus the middle-interval probability. This proves the third line.

An exact symmetry important below: conditional on any fixed \(A\) and on either \(C\) or \(D\) of positive probability, \(S\) is still uniform. Translating \(S\) by \(s_0\) and the responses by \((A_i s_0/q)_i\) translates the posterior labels without changing their weights or \(M\); therefore the event probabilities are identical under all choices of the true label.

## 3. The noiseless delayed-query benchmark

Let \(S\) be uniform in \(\mathbf F_q^d\), and suppose that the sender sees \(S\) itself. Write \(N=q^d\). For an unassisted quantum message of dimension \(L\) (including a classical alphabet of size \(L\)), the advantage over \(1/q\) is at most
\[
 (1-1/q)\sqrt{L/N}.                                             \tag{4}
\]
For a quantum message of dimension \(D_m\) with arbitrary finite entanglement assistance the bound is \((1-1/q)D_m/\sqrt N\). Here and below the query is uniform over the whole coefficient space, including its zero vector.

There is also a short entirely classical proof of (4). For a stochastic encoder with at most \(L\) messages, let \(K(j\mid s)\) be its transition probabilities. A message \(j\) with positive probability contributes
\(\frac1N\sum_s K(j\mid s)^2/\sum_s K(j\mid s)\le1/N\)
to the expected conditional collision probability of \(S\). Thus that expected collision is at most \(L/N\), and the scalar collision argument in §4 gives (4).

Here is a dimension-only proof of the quantum versions. Denote the states available at the receiver by \(\rho_s\). For unassisted communication take the reference \(\omega=I/L\), so \(\operatorname{Tr}(\rho_s\omega^{-1}\rho_s)\le L\). For the assisted case the receiver's retained marginal \(\tau\) before arrival of the message is independent of \(s\), by no signalling. With \(\omega=I_{D_m}/D_m\otimes\tau\), restrict to its support and use
\(\rho_s\le D_m I_{D_m}\otimes\tau=D_m^2\omega\).
Indeed write the positive matrix in message blocks; a quadratic form on a vector with block coordinates \(v_i\) is bounded by \((\sum_i \sqrt{\langle v_i,\rho_{ii}v_i\rangle})^2\), hence by \(D_m\sum_i\langle v_i,\tau v_i\rangle\). It follows that \(\operatorname{Tr}(\rho_s\omega^{-1}\rho_s)\le D_m^2\). These inequalities require no dimension bound on the preshared system except finiteness.

For a query \(u\) and answer \(a\), put
\[
 \Delta_{u,a}=\frac1N\sum_s(\mathbf1_{\{u\cdot s=a\}}-1/q)\rho_s .
\]
For two distinct labels \(s,v\), the chance over \(u\) that \(u\cdot s=u\cdot v\) is \(1/q\); this uses \(q\) prime and full uniform queries. Expanding the weighted squared norm yields
\[
 \mathbb E_u\sum_a \operatorname{Tr}(\Delta_{u,a}\omega^{-1}\Delta_{u,a})
   =\frac{1-1/q}{N^2}\sum_s\operatorname{Tr}(\rho_s\omega^{-1}\rho_s).
\]
For any special-to-query POVM \(M_{u,a}\), subtract \(I/q\) since \(\sum_a\Delta_{u,a}=0\). The sum of squared norms of \((M_{u,a}-I/q)\omega^{1/2}\) is at most \(1-1/q\), because \(0\le M_{u,a}\le I\) and \(\sum_aM_{u,a}=I\). Weighted Hilbert–Schmidt Cauchy–Schwarz and then Cauchy–Schwarz over \(u\) give (4) and the assisted bound. Conditioning on any public randomness shared before the message preserves these bounds.

A classical partition asymptotically attains (4) at \(L=q^{d-2\ell}\). As a finite-field labeling of the **noiseless** benchmark, identify \(s=(x,y,z,w)\), with \(x,y,z\) in \(K=\mathbf F_{q^\ell}\) and \(w\in\mathbf F_q^{d-3\ell}\) (\(3\ell\le d\) eventually). Partition labels by \((w,z-xy)\), giving cells of size \(q^{2\ell}\). Conditional on a cell, \((x,y)\) is uniform in \(K^2\). Every query is represented by a linear trace test in these three \(K\)-variables and a linear test on \(w\); this is just nondegeneracy of the field trace pairing. For a query whose \(z\)-coefficient \(c\ne0\), the conditional symbol has the form constant \(+\operatorname{Tr}_{K/\mathbf F_q}(a x+b' y+c xy)\). For any nonzero base-field Fourier parameter, summing over \(y\) cancels unless \(x=-b'/c\). Thus its distribution is
\[
 (1-q^{-\ell})\,U_{\mathbf F_q}+q^{-\ell}\delta_{a_0}
\]
for the symbol \(a_0\) attained at that special \(x\). The corresponding conditional advantage is \((1-1/q)q^{-\ell}\), for a fraction \(1-q^{-\ell}\) of independent uniform queries. All other queries can achieve at least \(1/q\). Hence the noiseless optimum lies between
\[
 (1-1/q)q^{-\ell}(1-q^{-\ell})
 \quad\text{and}\quad (1-1/q)q^{-\ell}
\]
in advantage. The same lower benchmark is available unassisted with a classical basis encoding, or with assisted message dimension \(D_m=\sqrt L\) by the standard \(D_m^2\)-symbol dense coding on a \(D_m\)-dimensional maximally entangled pair. These finite-field and quantum comparisons use no noisy-label solving procedure.

## 4. Transferring the benchmark to the noisy storage problem

For any posterior distribution \(\pi\) on \(S\), let \(\pi_{u\cdot}\) be the induced distribution of \(u\cdot S\). The Fourier collision identity
\[
 \mathbb E_u\sum_a (\pi_{u\cdot}(a)-1/q)^2
     =(1-1/q)\sum_s\pi_s^2
\]
is the same indicator orthogonality as above. For a fixed query, the best exact-symbol advantage over \(1/q\) is at most \(\sqrt{(1-1/q)\sum_a(\pi_{u\cdot}(a)-1/q)^2}\): if the largest deviation is \(x\), the other \(q-1\) deviations sum to \(-x\). By averaging, full noisily observed \(Y\) gives advantage at most \((1-1/q)\sqrt{\sum_s\pi_s(Y)^2}\) for that observation. A message without any feedback cannot beat access to \(Y\), even with preshared entanglement: conditional on the classical source, all later receiver statistics follow by a channel whose other randomness is independent of \(S\) given \(Y,A\).

For the upper bound, one may additionally reveal the branch flag to the receiver after the message. On \(D\), dropping the summary restriction and applying the preceding bound and (3) gives a contribution above baseline \(O(\sqrt{\varepsilon_d})\) in mean over \(A\). More precisely it is bounded for each \(A\) by \((1-1/q)\sqrt{\mathbb E[\mathbf1_D\sum_s\pi_s(Y)^2\mid A]}\). On \(C\), conditional on \(A\), the label is uniform by the exact symmetry, and the induced message is some channel from this uniform \(S\) to a state of the allowed form (average over \(Y\) conditional on \(S,A,C\)). In the assisted case the retained-system marginal is still fixed because no local choice of the sender changes it, even conditional on \(Y,A\). Thus this branch contributes above baseline at most \((1-1/q)q^{-\ell}\Pr(C\mid A)\) in all three cases.

For the lower bound, on \(C\) use the noiseless benchmark partition with the maximizing posterior label in place of the true label. This is a statistical existence argument over unrestricted encoders; no efficient posterior evaluation is given or claimed. The conditional probability that this substitution changes the label is \(1-M(Y)\); its total contribution to possible success loss is at most the second line of (3). On \(D\), transmit a fixed dummy symbol from the same alphabet, so there is no extra flag and no extra message capacity. Conditional on \(A,D\), the true label is uniform and the dummy is independent of it; for each nonzero query its predicted answer gives exactly \(1/q\) success, and the decoder predicts zero for the zero query. The same lower argument works when the classical message is sent as an unassisted basis state or by the assisted noiseless alphabet. The prior symmetry is what allows a dummy message without an additional decoding flag.

Combining the bounds, rescaling by \(q^\ell\) and using (3), the error averaged over designs is at most
\[
 O\big(q^\ell\sqrt{\varepsilon_d}
          +q^\ell\varepsilon_d+q^{-\ell}+\varepsilon_d\big)=o(1).
\]
This proves (1), including the required scale separation of the diffuse contribution from the communication advantage.

## 5. Prior and scope

[Cleve–van Dam–Nielsen–Tapp](https://arxiv.org/abs/quant-ph/9708019) analyze the binary inner product communication problem, including entanglement. The finite-field bilinear trace construction above is the standard Maiorana–McFarland form (see, for example, [the odd-characteristic vectorial setting](https://doi.org/10.1016/j.ipl.2013.10.011)); it is used here only as a partition for the known-label benchmark. The assisted transmission uses [Bennett–Wiesner](https://journals.aps.org/prl/abstract/10.1103/PhysRevLett.69.2881) and the general-dimensional [dense coding framework of Werner](https://arxiv.org/abs/quant-ph/0003070). The overlap in (2) is the product-noise case of the earlier [posterior-surprisal argument](https://github.com/mxym/math/blob/15a25c0d1d01551372cfb03794958adc753ca3b6/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-posterior-surprisal-coarsenings.md); the new step is the quantitatively controlled posterior branch split at the much smaller communication advantage scale, with exactly uniform conditional labels on both branches. Unlike the [full-field retention theorem](https://github.com/mxym/math/blob/7c2951bad619746414ac0f6f9f5af74502e7a81d/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-likelihood-field-rate-distortion.md), only one independently drawn future query is answered.

The result does not address fixed or adaptively selected queries, many repeated queries to one message, entanglement correlated with the data, larger storage deficits outside the stated scale, nonuniform labels, or efficient computation on broad ring observations.
