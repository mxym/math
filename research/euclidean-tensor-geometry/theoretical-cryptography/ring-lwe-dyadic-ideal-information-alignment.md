# Alignment of ideal-direction information in the odd dyadic torus model

## Statement

Let \(d\to\infty\) through powers of two, \(R=\mathbb Z[\zeta_{2d}]\), \(L=\sigma(R^\vee)\) for the codifferent \(R^\vee\), and \(G=K_{\mathbb R}/L\) with Haar probability \(U\). Use the Euclidean norm given by the sum over all \(d\) embeddings, including both embeddings at a complex place. Let \(p\) be the density relative to \(U\) of a centered continuous spherical Gaussian of width \(s\), with unwrapped density proportional to \(e^{-\pi\|x\|^2/s^2}\), reduced modulo \(L\). Write
\[
 b=e^{-\pi ds^2},\qquad \tau=db^2,\qquad X=\log p(E),\quad E\sim p\,dU .
\]
Allow any odd integer \(q\ge3\), possibly varying with \(d\), and any nonzero \(R\)-submodule \(J\le R^\vee/qR^\vee\). We regard \(J\) as a subgroup of \(G\) by \(j\mapsto \sigma(j/q)\bmod L\). Its translation-average operator is \(P_J\). Define the directional information density and its mean by
\[
 \ell_J(E)=\log\frac{p(E)}{P_Jp(E)},\qquad
 I_J=D(p\,dU\Vert (P_Jp)\,dU).
\]
Divergences below abbreviate their densities relative to \(U\); in particular \(D(h\Vert 1)=\int h\log h\,dU\). All logarithms are natural, and \(x_+=\max(x,0)\).

**Theorem.** All estimates are uniform in odd \(q\) and nonzero \(J\).

1. If \(0<\tau\le(1-\epsilon)\log d\) for fixed \(\epsilon>0\), then
   \[
   D(P_Jp\Vert1)=o(1),\qquad I_J=\tau+o(1),\qquad I_J/\tau\longrightarrow1.
   \tag{1}
   \]
   For \(0<\tau\le1\) the first divergence is \(O(\tau^3/d)\). For any *fixed* finite list of such directions, which may be chosen anew in every dimension,
   \[
   \left(\frac{\ell_{J_i}(E)-\tau}{\sqrt{2\tau}}\right)_i
      \ \Longrightarrow\ (Z,\dots,Z),\qquad Z\sim N(0,1).
   \tag{2}
   \]
   There is only one scalar Gaussian in the limit. In (1), the assertion \(D(P_Jp\Vert1)=o(1)\) also holds up to \(\tau\le\log d-h_d\) if \(h_d/\sqrt{\log d\,\log\log d}\to\infty\) and the range is nonempty.

2. For every fixed \(C>0\) and \(0<\tau\le C\log d\), there is a sharper upper estimate near the critical window:
   \[
   \mathbb E_p(X-\log|J|)_+-e^{-1}
     \ \le\ D(P_Jp\Vert1)\
     \le\ \mathbb E_p(X-\log d)_++O_C(1+\log\log d).
   \tag{3}
   \]
   Thus when \((\tau-\log d)/\sqrt{2\log d}\to c\in\mathbb R\), the limsup of \(D(P_Jp\Vert1)/\sqrt{2\log d}\) is at most \(\mathbb E(Z+c)_+\). **Conditional on** \(\log|J|-\log d=o(\sqrt{\log d})\) on the sequence in question, this limsup is a limit and an equality. In that case,
   \[
      \frac{\ell_J(E)-\log d}{\sqrt{2\log d}}
           \ \Longrightarrow\ \min(Z+c,0).
   \tag{4}
   \]
   The result does not assert the existence of odd-modulus ideals of this size along any infinite dyadic sequence.

These are one-error information statements for a known noise law in an exact, continuous, abstract torus. The meaning for search is explained at the end.

## 1. Coordinates and the ideal Fourier restriction

Use the character \(x\mapsto e^{2\pi i\operatorname{Tr}(ax)}\) for \(a\in R\), extending the trace to \(K_{\mathbb R}\). The Euclidean dual uses the conjugate of \(a\) under this convention, so the norm is unchanged. In the power basis \(a=\sum_{j<d}a_j\zeta_{2d}^j\),
\(\|\sigma(a)\|^2=d\sum_j a_j^2\), since the sum over the odd roots of any nontrivial basis frequency difference is zero. The character coordinates make \(U\) product Haar measure and give
\[
 p(z)=\prod_{j=0}^{d-1}f_b(z_j),\qquad
 f_b(u)=\sum_{k\in\mathbb Z}b^{k^2}e^{2\pi iku}.
 \tag{5}
\]
In particular \(p>0\), and \(p\) and its level sets are invariant under coordinate permutations.

The annihilator \(A_J=\{a\in R:\operatorname{Tr}(aj/q)\in\mathbb Z\text{ for every }j\in J\}\) is an ideal containing \(qR\). It is proper by the perfect trace pairing of \(R/qR\) with \(R^\vee/qR^\vee\), and \(P_J\) is the Fourier projection onto \(A_J\). Choose any maximal ideal \(\mathfrak p\supset A_J\). Its residue field has odd characteristic \(\lambda\mid q\), and the image \(\bar\zeta\) of \(\zeta_{2d}\) has order exactly \(2d\), because \(\bar\zeta^d=-1\ne1\) and \(2d\) is a power of two. Therefore \(\bar\zeta^j\) are pairwise distinct for \(0\le j<d\). No signed one-term or signed two-term word with coefficients \(\pm1\) and distinct positions is in \(\mathfrak p\): the two-term case would give either equal powers or a difference in exponents congruent to \(d\) modulo \(2d\). Consequently \(A_J\) contains no vector of coefficient squared norm 1 or 2.

For a coordinate-permutation orbit of a frequency word with \(r\) nonzero entries, assume some coefficient \(c\) is not divisible by \(\lambda\). Randomly assign its labeled nonzero entries to distinct positions. Condition on the placements of all but this marked coefficient. There is at most one of the \(d-r+1\) remaining positions for which the residue sum vanishes, by distinctness of the powers and invertibility of \(\bar c\). Labeling repeated coefficients does not alter the induced uniform law on the orbit. The fraction of the orbit in \(A_J\) is therefore at most \(1/(d-r+1)\).

We record two consequences of this argument. Put \(x=b^2\), \(\theta(x)=\sum_{v\in\mathbb Z}x^{v^2}\). If \(\tau\le1\), mark and delete any coefficient nonzero modulo \(\lambda\). For each remaining word and value of the deleted coefficient there is at most one restoration position. When the deleted value is \(\pm1\), the remaining squared norm must be at least 2. This yields
\[
 \begin{split}
 \|P_Jp-1\|_2^2
 &\le 2x\bigl(\theta(x)^d-1-2dx\bigr)
      +\Big(\sum_{|v|\ge2}x^{v^2}\Big)\theta(x)^d
      +\theta(x^{\lambda^2})^d-1\\
 &= O(\tau^3/d).
 \end{split} \tag{6}
\]
The last term counts words all of whose coefficients are divisible by \(\lambda\), other than the zero word. For the last equality, \(d x=\tau\le1\), \(\theta(x)-1-2x=O(x^4)\), the bracket is \(O(d x^4+(dx)^2)\), and \(\lambda\ge3\). This proves the small-\(\tau\) KL bound via \(D(h\Vert1)\le\log\int h^2\le\int(h-1)^2\).

For arbitrary permutation-invariant \(g\in L^2(U)\), let \(P_\lambda\) denote the Fourier projection onto words with every coefficient divisible by \(\lambda\), effected by independent uniform shifts modulo \(1/\lambda\) in every coordinate. Let \(B\) independently keep each coordinate with probability \(1-\gamma\) or replace it with Haar probability \(\gamma=d^{-3/4}\). As operators on densities these are positive, Haar-preserving contractions; they and \(P_J\) commute, since all are convolutions. The multiplier of \(B\) on an \(r\)-supported frequency is \((1-\gamma)^r\). By Parseval and the orbit bound,
\[
 \|P_J(I-P_\lambda)Bg\|_2^2
       \le (2/d+e^{-\gamma d})\|g\|_2^2 .
 \tag{7}
\]
Indeed the squared modulus of \(\widehat g\) is constant on each orbit; for \(r\le d/2\) the surviving fraction is at most \(2/d\), and larger supports have squared damping at most \(e^{-\gamma d}\).

## 2. Product likelihood and small reference divergence

For the remainder take \(0<\tau\le C\log d\) with any fixed upper constant \(C\). Taylor expansion of \(f_b=1+2b\cos(2\pi u)+O(b^4)\), uniformly in \(u\), shows that for \(U_0\) with density \(f_b\)
\[
 \mathbb E \log f_b(U_0)=b^2+O(b^3),\qquad
 \operatorname{Var}\log f_b(U_0)=2b^2+O(b^3),\qquad
 |\log f_b(U_0)|\le C_0 b.
 \tag{8}
\]
For example the mean integral is \(\int(1+w)\log(1+w)=\tfrac12\int w^2+O(\int|w|^3)\), where \(w=f_b-1\) has zero mean and \(\int w^2=2b^2+O(b^8)\). Under \(p\,dU\), \(X\) is the sum of \(d\) independent copies of \(\log f_b(U_0)\). In particular \(\mathbb E X=\tau+O(db^3)\), \(\mathbb E X^2=O(1+(\log d)^2)\), and
\[
 (X-\tau)/\sqrt{2\tau}\Longrightarrow Z,\qquad
 \sup_d\mathbb E_p[((X-\tau)/\sqrt{2\tau})^2]<\infty
 \tag{9}
\]
on all such sequences with positive \(\tau\). In fact the largest centered summand divided by \(\sqrt{2\tau}\) is \(O(d^{-1/2})\), the total variance after scaling tends to 1, and the centering error divided by \(\sqrt{\tau}\) is \(O(\tau/\sqrt d)=o(1)\).

Convolution by \(B\) on \(p\) replaces each \(f_b\) by \(1+(1-\gamma)(f_b-1)\). The logarithms differ by \(O(\gamma b)\) per coordinate uniformly. Thus \(\|p-Bp\|_1=O(\gamma d b)\) and more precisely
\[
 e^{-\delta_d}Bp\le p\le e^{\delta_d}Bp,\quad
 \delta_d=O_C(d^{-1/4}\sqrt{\log d})=o(1).
 \tag{10}
\]
Also \(P_\lambda p=\prod_j f_{b^{\lambda^2}}(\lambda z_j)\) satisfies \(\|P_\lambda p-1\|_\infty=O(d b^9)\), uniformly in \(\lambda\ge3\).

For \(\tau\le(1-\epsilon)\log d\), use the cutoff \(a=(1-\epsilon/2)\log d\), and let \(p_g,p_b\) be the conditional densities on \(X\le a\) and \(X>a\), with \(\beta=\mathbb P_p(X>a)\). Bernstein's inequality applied to (8) bounds \(\beta\le d^{-c_\epsilon}\) for large \(d\). Define \(p_g\) in the usual way if \(\beta=0\), and omit terms involving a zero-mass part. Then \(p_g\le M=e^a/(1-\beta)\), and \(\|p_g-p\|_1=2\beta\). Use (10), \(L^1\) contractions, (7), and \(P_\lambda p\) close to 1 to get
\[
 \begin{split}
 \|P_Jp_g-1\|_1
 &\le\|p_g-Bp_g\|_1+\|P_JP_\lambda Bp_g-1\|_1
         +\|P_J(I-P_\lambda)Bp_g\|_2\\
 &\le 6\beta+O(\gamma db+db^9)
              +\sqrt{(2/d+e^{-\gamma d})M}.
 \end{split} \tag{11}
\]
Here the last inequality uses \(\|p_g\|_2^2\le M\). On \(1\le u\le M\) one has \(u\log u\le (M\log M)/(M-1)(u-1)\) by convexity; below 1 the entropy integrand is nonpositive. Hence \(D(P_Jp_g\Vert1)=o(1)\), as (11) times \(O(1+\log M)\) tends to zero. For the other part, Jensen/data processing gives
\[
 \beta D(P_Jp_b\Vert1)\le \beta D(p_b\Vert1)
       =\mathbb E_p[X1_{\{X>a\}}]+\beta\log(1/\beta)=o(1)
 \tag{12}
\]
by Cauchy–Schwarz, (8) and the polynomial decay of \(\beta\). Convexity of KL then gives \(D(P_Jp\Vert1)=o(1)\). If instead \(\tau\le \log d-h_d\) as in the theorem, replace \(a\) by \(\log d-h_d/2\); unless the parameter range is empty, \(h_d\le\log d\). Bernstein gives \(\beta\le\exp(-c h_d^2/\log d)=o((\log d)^{-M_0})\) for every fixed \(M_0\). The last term in (11) is controlled by \(O(e^{-h_d/4})\) plus an exponentially small error. The same proof therefore works.

An exact identity, since \(\log P_Jp\) is \(J\)-invariant, is
\[
 I_J=D(p\Vert1)-D(P_Jp\Vert1),\qquad
 \mathbb E_p|\log P_Jp|=\int (P_Jp)|\log P_Jp|\,dU .
 \tag{13}
\]
For any density \(h\), \(\int h|\log h|\le D(h\Vert1)+2\,\operatorname{TV}(h,1)\): the magnitude of the negative part is at most \(\int_{h<1}(1-h)\), by \(-h\log h\le 1-h\). By Pinsker, (6) and (11)–(12) this makes \(\mathbb E_p|\log P_Jp|=o(\sqrt\tau)\) uniformly over the subcritical width range, including \(\tau\to0\). In the latter range one has even \(O(\tau^{3/2}/\sqrt d)\). Equations (8), (9), and (13) prove (1)–(2), with a union bound over the fixed finite list for (2).

## 3. Entropy near the critical window

The following upper-bound argument trims and **slices** the product likelihood, not its Fourier coefficients. First replace \(P_Jp\) by \(q_0=P_JBp\). Inequality (10) is preserved by \(P_J\). If \(h=P_Jp\), then
\[
 |D(h\Vert1)-D(q_0\Vert1)|
 \le\delta_d+(e^{\delta_d}-1)\int q_0|\log q_0|\,dU=o(1).
 \tag{14}
\]
The integral is \(O_C(1+\log d)\): use the negative-part bound after (13), data processing for \(P_JB\), and (8).

Choose \(A>0\) sufficiently large depending on \(C\). The event \(|X|>A\log d\) then has probability at most \(d^{-3}\) by Bernstein, and contributes \(o(1)\) to the convexity bound on \(D(q_0\Vert1)\) via the same argument as (12). Partition the complementary event into intervals of length at most one, at most \(O_C(\log d)\) of them. Let one interval have top \(v\), mass \(\beta_i>0\), and conditional density \(g_i\). Then \(g_i\le e^v/\beta_i\), \(g_i\le p/\beta_i\), and \(g_i\) is permutation-invariant. Consequently
\[
 \|P_JP_\lambda Bg_i\|_2^2\le\frac{1+O(db^9)}{\beta_i},\qquad
 \|P_J(I-P_\lambda)Bg_i\|_2^2\le
     (2/d+e^{-\gamma d})\frac{e^v}{\beta_i}.
\]
The first uses positivity and \(P_JBP_\lambda p\le1+O(db^9)\) to bound the \(L^\infty\) norm of a probability density; the second is (7). The two Fourier supports are orthogonal. Applying the upper bound by Rényi divergence of order 2 yields
\[
 D(P_JBg_i\Vert1)\le\log\|P_JBg_i\|_2^2
      \le -\log\beta_i+(v-\log d)_++O(1).
\]
Average by \(\beta_i\), use convexity of KL, and note that the label entropy is at most \(\log(O_C(\log d)+1)\), also when the omitted tail is counted as one label. Replacing \(v\) by \(X\) on each bin costs at most one. This and (14) yield the upper bound of (3).

The identity term of the average gives \(h=P_Jp\ge p/|J|\) pointwise. Under \(p\,dU\) the negative part of \(\log h\) has expectation at most \(e^{-1}\), since \(\int p(\log h)_-=\int h(\log h)_-\le e^{-1}\). Thus \(D(h\Vert1)\ge\mathbb E_p(X-\log|J|)_+-e^{-1}\), finishing (3). This also gives \(D(h\Vert1)\ge D(p\Vert1)-\log |J|\) by integrating the untruncated pointwise inequality.

At the critical scaling, (9) and uniform integrability give the mean limit in any positive-part term normalized by \(\sqrt{2\log d}\), with its center adjusted by the threshold in that term. If additionally \(\log|J|-\log d=o(\sqrt{\log d})\), it follows that the expectations of \((\log h)_+/\sqrt{2\log d}\) and \((X-\log|J|)_+/\sqrt{2\log d}\) have the same limit. The first dominates the second pointwise, so their difference tends to zero in \(L^1(p\,dU)\). The negative part of \(\log h\) is bounded in expectation as above. It follows that \(\log h/\sqrt{2\log d}\) differs by \(o_{L^1}(1)\) from \((X-\log d)_+/\sqrt{2\log d}\), which proves (4).

## Relevance and prior work

[Lyubashevsky–Peikert–Regev, Definitions 3.1–3.2](https://web.eecs.umich.edu/~cpeikert/pubs/ideal-lwe.pdf) define the codifferent torus model and the search problem. Their hardness theorem concerns a prescribed error family and a worst-case quantum reduction. [Peikert–Regev–Stephens-Davidowitz, Lemma 6.9](https://web.eecs.umich.edu/~cpeikert/pubs/rlwe-anyring.pdf) prove a sufficient smoothing-parameter bound for arbitrary ideals using norm/AM–GM; it is a different bound and does not directly give the entropy window here. The KL flatness quantity and the channel interpretation of the difference of two KL flatness quantities are standard; see [Luzzi–Ling–Bloch, Appendix B, Equation (43), Lemma 8 and Definition 10](https://arxiv.org/abs/2206.10443). Here the extra points are the uniform odd-ideal entropy bounds and the coupled information fluctuations. The raw Fourier second-moment method from deleting a coefficient only gives a direct small-error estimate of order \(b^2\theta(b^2)^d\) plus the all-divisible term, useful below the \(\tfrac12\log d\) scale rather than the scale in (1).

In the [simultaneous ideal search converse](ring-lwe-search-ideal-converse.md), each \(I_J\) is the mean information under the corresponding direction and the likelihoods are evaluated on the *same* error, not on independent fictitious noises. Here their common leading term is \(\tau\), and fixed-list correlations in (2) are complete at the stated fluctuation scale. This is a necessary-information calculation, not a sufficient sample bound, not an algorithm (classical polynomial-time or otherwise), and not a claim for the full reduction error family. There is no assertion for even modulus, correlated or discretized errors, deployed instances, or uniform simultaneous convergence over a growing list of ideal directions.

Nearby repository notes are distinct: [CRT divisibility association](crt-divisibility-association.md) studies zero-membership indicators under a discrete coefficient Gaussian; [joint ideal smoothing](dyadic-ideal-joint-smoothing.md) treats source coefficient laws reduced into finite quotients; [ramified ideal TV](ramified-ideal-tv-windows.md) studies even ramified layers; [the Gaussian quotient double window](gaussian-quotient-double-window.md) assumes a random quotient ensemble with fixed base. The companion arithmetic checker only verifies the finite root, marked-position, and support-energy ingredients on synthetic small cases; it does not replace the analytic proof.
