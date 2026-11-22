# Weighted three-free completion and actual balanced triprime removal in a one-tag covariance

The original marked shared-index covariance uses two prime factors of each slope. This note gives a different, **single-tag, squarefree-shared-index** calculation. In that actual covariance, after the large-free subtraction, one can eliminate an entire genuine triprime family, including all triprimes with largest prime at most \(x^{.427}\). The proof does not remove these triprimes from the earlier two-tag covariance, does not claim that all \(k\) can be taken squarefree, and does not bound the whole new covariance.

The analytic ingredient is a weighted *independent three-box* consequence of [Prahlad Sharma, arXiv:2303.06087v3, Theorem 1.2 and Lemma 5.2](https://arxiv.org/pdf/2303.06087), published in [Proc. London Math. Soc. 128 e12589](https://doi.org/10.1112/plms.12589). We do not apply his unweighted divisor-function Theorem 1.1 to independent individual weights. Instead we prove the needed three-box statement by direct completion, followed by the genuinely weighted dual bilinear theorem.

## 1. A weighted balanced-box theorem for squarefree moduli

Let \(X=X_1X_2X_3\), with \(X_i\ge1\) and \(\max_i X_i\le X^{.430}\). Then necessarily \(\min_i X_i\ge X^{.140}\). Fix smooth functions \(W_i\) supported in \([1/2,3]\) with \(\|W_i^{(j)}\|_\infty\ll_j(\log X)^{C_j}\), including \(j=0\). For squarefree \(q\) with \(X^{.51}\le q\le X^{.532}\), and **any** reduced residue \(t\bmod q\), one has for some absolute \(c>0\)
\[
 \sum_{n_1n_2n_3\equiv t\ (q)}\prod_i W_i(n_i/X_i)
 -\frac1{\varphi(q)}
       \prod_i\sum_{(n_i,q)=1}W_i(n_i/X_i)
 \ll \frac{X^{1-c}}{q}.                                      \tag{1}
\]
The bound is uniform over the residue, also when it depends arithmetically on this modulus. The constants in the weight derivative hypotheses can be fixed arbitrarily before taking the limit.

### Literal Fourier completion and exact removal of all zero axes

Poisson sum each variable over its residue class. The difference on the left of (1) is
\[
 \frac{X}{q^3}\sum_{h_1,h_2,h_3\in\mathbb Z}
 \prod_i\widehat W_i(h_i X_i/q)
 \left({\cal C}_q(\bm h;t)
       -\frac{c_q(h_1)c_q(h_2)c_q(h_3)}{\varphi(q)}\right),       \tag{2}
\]
where \({\cal C}_q\) is the complete exponential sum over three units with product \(t\), and \(c_q\) denotes the Ramanujan sum. All signs in the complete transform have the same convention \(e(h_i r_i/q)\); the sign of one \(h_i\) will be fixed on each dual box. For sufficiently small absolute \(\xi>0\), truncate with independent smooth cutoffs to \(|h_i|\ll X^\xi q/X_i\), each cutoff being one up to \(X^\xi q/X_i\). Rapid Fourier decay gives an arbitrarily strong power-saving tail: differentiating the primal test costs only log powers and \(|{\cal C}_q|\le q^2\). In the retained range \(|h_i|<q\) eventually.

By the squarefree CRT split, at a prime \(p\mid q\) the local phases are scaled by units, and if exactly \(j\) of the three \(h_i\)'s vanish modulo \(p\), the two local complete kernels in parentheses agree for \(j=1,2,3\). Their respective values are \(1,-(p-1),(p-1)^2\): if at least one \(h_i=0\bmod p\), choose the corresponding coordinate as the dependent variable and sum the other two independently. On the unit-model side these are the products of three local Ramanujan sums divided by \(p-1\). It follows in particular that if **any integer coordinate \(h_i=0\)** the entire parenthesis is exactly zero, regardless of the others.

For the remaining nonzero frequencies, prescribe for each \(p\mid q\) its exact subset of vanishing coordinates. Write \(d,q_1,q_2,q_3\) for the products of primes with respectively \(0,1,2,3\) vanishing coordinates. Put \(B=q_1^2q_2\). Then \(q=dq_1q_2q_3\). If \(d=1\) the entire difference is again zero. At active \(d\), the true kernel is
\(d\,\widetilde{\rm Kl}_3(t_0 h_1h_2h_3;d)\), with \(t_0\) a unit incorporating the CRT dilation and \(t\); the inactive part has total absolute value at most \(q_2q_3^2\). Here
\[
 \widetilde{\rm Kl}_3(a;d)=\frac1d
     \sum_{u,v\bmod d}^{*} e_d(a u+v+\overline{uv})
\]
is the literal normalized trace in Sharma, agreeing with the unit product hyper-Kloosterman sum for \(a\) a unit. The corresponding unit-model active factor is \((-1)^{\omega(d)}/\varphi(d)\), independent of the residue. Scaled to the target \(X/q\), its total size per mask is \(O(X^{-1+O(\xi)+o(1)})\): if \(g_i\) is the product of primes for which the \(i\)-th coordinate vanishes, then \(\prod_i g_i=q_1q_2^2q_3^3\), and the remaining frequencies have product of lengths at most
\[
 D_0=X^{O(\xi)}\frac{q^3}{X\,g_1g_2g_3}
       =X^{O(\xi)}\frac{d^3 B}{X}.
 \tag{3}
\]
Use \((q_2q_3^2)/(q^2\varphi(d))\) as the normalized model prefactor. There are \(8^{\omega(q)}=X^{o(1)}\) masks, so this model term is harmless. For the **true** active term the normalized prefactor is exactly \(d q_2q_3^2/q^2=1/(dB)\).

### All dual coprimalities with their actual conductor losses

Write \(h_i=\pm g_i v_i\), \(v_i\ge1\), and expand each remaining \((v_i,q/g_i)=1\) indicator by divisors \(b_i\mid q/g_i\). These may be nonunits at the active primes: in any summand the active modulus \(d\) is reduced by every prime dividing \(b_1b_2b_3\). This is an exact local reduction, since
\(\widetilde{\rm Kl}_3(0;p)=1/p\): sum first over \(u\), for each nonzero \(v\) the reciprocal additive sum equals \(-1\), and then \(\sum_{v\ne0}e_p(v)=-1\). The CRT-scaled version has the same value. The remaining argument multiplier is always a unit at the remaining active primes.

Dyadically group the three new variables and choose the smallest length slot as the short variable. To apply the elementary alternative correlation below with a genuine unit short argument, also split this variable by its exact gcd \(g\) with the active modulus still retained. For \(n=g n'\) in this class, the modulus is again reduced by \(g\) with normalized trace factor \(1/g\), and \((n',d')=1\) where \(d'\) is the final active modulus. That same slot remains shortest after being shortened. Put \(E=d/d'\) and let \(b\) be the product of all divided indices in these steps, including \(g\). Then \(b\ge E\), the trace has a factor \(1/E\), and the dual product \(D\) of the effective lengths obeys
\[
 D\ll X^{O(\xi)}\,d^3 B/(X b).
 \tag{4}
\]
Only \(X^{o(1)}\) divisor lists are introduced. No short-unit condition is incorrectly assumed of an unexpanded weight. If \(d'\le X^{.498}\), the elementary normalized Deligne bound \(|\widetilde{\rm Kl}_3|\ll X^{o(1)}\) on squarefree moduli (including the reduced nonunits by CRT) gives, relative to \(X/q\), \(O(X^{O(\xi)+o(1)}d'^2/X)\), since the prefactor is \(1/(dBE)\) and \(b\ge E\). This saves a fixed power. This argument includes \(d'=1\).

### Dual weighted gluing and the actual Sharma bounds

For \(d'>X^{.498}\), let \(N_0\) be the shortest effective length and \(M_0\) the product of the other two, so \(D\asymp M_0N_0\). Before any divisor shortening, the product of the two largest dual lengths is at most
\[
 X^{2\xi}\frac{q^2}{\min_{i\ne j}X_i X_j}
 \le X^{.494+2\xi},
\]
because \(\max_i X_i\le X^{.430}\). Shortening only reduces this bound. Also
\(N_0\ll D^{1/3}\ll X^{.199+O(\xi)}\), by \(D\le X^{O(\xi)}q^3/X\).
Consequently \(M_0\ll d'\) with fixed slack, and
\(N_0\le d'^{1/2}(1+M_0/d')^{-2}\) with fixed slack, the exact size condition of Sharma's Theorem 1.2.

The two longer variables have actual independent smooth Fourier weights. On dyadic cutoffs, their normalized derivatives of order \(j\) are \(O_j(X^{j\xi}(\log X)^{C_j})\), because the normalized dual argument is at most \(O(X^\xi)\). Separate them by Mellin on the imaginary axis, with smooth supported dyadic partition functions. One may restrict each Mellin variable to \(|t|\le X^{3\xi}\) with a power-small tail of any fixed order and \(L^1\) cost \(X^{O(\xi)}\), by integration by parts in the compact logarithmic coordinate. When grouping the two variables \(m_2m_3=m\), their separate powers become exactly \(m^{it_2}\sigma_{i(t_1-t_2)}(m)\). The \(m^{it_2}\) factor sits in the smooth \(m\)-test (normalized derivatives at most \(X^{3j\xi}\) up to log powers). Append a smooth product cutoff equal to one on the two dyadic product support. With the full Mellin integrals this is exact; after truncation the inverse-Mellin tails are uniformly power-small at every positive point, even at factorizations outside the original intervals, because the contours are imaginary. Summing these errors over the compact product support costs at most the ordinary divisor moment. The actual short coefficient stays independently bounded and supported on units. These are the Eisenstein coefficients in Theorem 1.2, with its spectral parameter and smoothness exponents met by taking \(\xi\) smaller than its \(\varepsilon\); neither two-prime coefficients nor arbitrary grouped divisor weights are furnished to that theorem.

Writing \(N_0=N'\), \(M_0=M'\), \(D=M'N'\), Theorem 1.2 now supplies, up to \(X^{O(\varepsilon)}\),
\[
 d'^{3/8}D^{1/2}N'^{1/4}
       +d'^{-1/4}D N'^{1/2}+d'^{3/4}N'.                    \tag{5}
\]
Here \(M'\ll d'\) was checked directly, so no loss from its \((1+M'/d')\) factors. For rigor about the other bound, one may use the squarefree instance of his **Lemma 5.2** and repeat its completion, rather than rely on the modulus wording of the preceding Lemma 5.1. With the unit short variable just retained, its complete correlation for the normalized trace is bounded by
\(X^{o(1)}d'^{1/2}\sum_{b_0\mid d'} b_0^{1/2}1_{n_1=n_2\,(b_0)}1_{h=0\,(b_0)}\).
Complete the long Cauchy sum of size \(M'\) modulo \(d'\); its effective Fourier range is \(d'/M'\) times a harmless small-power cutoff. The numbers of pairs and frequencies for each \(b_0\) are at most
\(O(N'(1+N'/b_0))\) and \(O(1+d'X^{O(\varepsilon)}/(M'b_0))\).
After the \(M'/d'\) Poisson factor and divisor summation, the second moment is
\(O(X^{O(\varepsilon)}(M'N'+N'^2d'^{1/2}(1+M'/d')))\).
Cauchy with the usual divisor-square moment for the Eisenstein coefficient gives
\[
 D/\sqrt{N'}+ D^{1/2}\sqrt{N'}\,d'^{1/4}                    \tag{6}
\]
up to the same small-power allowance. These calculations are uniform in the retained multiplier, which only has to be a unit of \(d'\).

The last term of (6) is \(O(D^{2/3}d'^{1/4})\). Minimize each of the three terms of (5) against \(D/\sqrt{N'}\); the maxima of these minima are respectively
\[
 D^{2/3}d'^{1/4},\qquad Dd'^{-1/8},\qquad D^{2/3}d'^{1/4}.
\]
Thus every dual box has bound \(X^{O(\varepsilon)}(D^{2/3}d'^{1/4}+D d'^{-1/8})\). By (4) and \(d'=d/E\), its normalized contributions after \(1/(dBE)\) are at most
\[
 X^{O(\varepsilon)+O(\xi)}
       \left(q^{5/4}X^{-2/3}+q^{15/8}X^{-1}\right).
 \tag{7}
\]
For example the exact first factor before dropping small divisors is \(d^{5/4}X^{-2/3} B^{-1/3} b^{-2/3}E^{-5/4}\); the second is \(d^{15/8}X^{-1} b^{-1}E^{-7/8}\). Both improve with divisor shortening. At \(q=X^{.532}\) the powers save \(1/600\) and \(1/400\) respectively. Choose the small exponents sufficiently below these margins. The divisor lists and all dyads cost \(X^{o(1)}\), which finishes (1). This uses only the true weighted bilinear trace inputs, not the unweighted \(d_3\) theorem or a generalized Voronoi formula.

## 2. The exact single-tag marked covariance and prior transfers

Let \(N=2x\), \(Y=\sqrt x\), \(L=\log x\), \(\ell=\log L\), \(z=\exp(L/\ell^2)\), \(R_z(y)=1_{P^-(y)>z}\), and take the genuine box
\[
 d,e\in[.65Y,.8Y],\qquad k\in[Y,1.1Y],\quad (dek,N)=1.
\]
Here restrict \(k\) to be squarefree. The mark is now
\(\beta_1(e)=\sum_{p\mid e,\ x^{.029}\le p\le x^{.031}}1\), with a single true prime \(p\); use the same mark on \(d\). Given \(e\)'s label \(p\) write \(e=p h_0\). For eligible \((p k,N)=1\) the literal modulus is \(A=k p\) and the residue \(y\equiv N\bmod A\), with \(y=N-ek\in I_k=[N-.8Yk,N-.65Yk]\). The physical unit test for \(h_0=(N-y)/A\) is equivalent to \((y,N)=1\). If \(p\mid k\) the label can be discarded at power-saving cost: before divisor weights, its \(e,k\) count is \(\ll\sum_{p\ge x^{.029}}(Y/p+1)^2\ll x^{1-.029}\) on the actual prime band. The outer \(d\)-length is \(O(Y)\). All weights are bounded by fixed divisor powers and cost \(x^{o(1)}\) on this power error. On all remaining labels \(A\) is squarefree. The choice to restrict to squarefree \(k\) is retained as an actual restriction, not dismissed as a small exceptional tail.

We record explicitly why the earlier two relevant score transfers continue to hold in this different ledger. Put
\[
 A_{\rm p}(y)=\log y\,1_{y\ {\rm prime}},\quad
 b_z(y)=R_z(y)\big/\prod_{p'\le z}(1-1/p'),\quad
 K(y)=R_z(y)\sum_{\substack{rs=y\\ r>x^{.505}}}\mu(r)\log s.
\]
For this step first allow the incidental sharing \(p\mid k\) on the transferred leg, so the short prime coefficient is exactly independent of the long slot; discard those labels afterwards by the power estimate above. In the proof of [the above-root \(F_R-b_z\) transfer](https://github.com/mxym/math/commit/48786012bff7073486a373df69f35611a803e916), replace only the long factor \(p_3h_0 k\) by \(h_0 k\); the short coefficient is still the **genuine independent** prime \(p\). More precisely, for each fixed \(d\) the long coefficient includes \(k\)'s arbitrary real row coefficient and squarefree mask, and is divisor-bounded after the same log clipping. The short slot size is \(x^{.029-.031}\), the actual residue at \(N\bmod r m\) is unchanged when the short rough expansion \(m\le x^{o(1)}\) is opened, and the true output product \(p h_0 k\) stays on the earlier \([.65x,.88x]\) scale. Thus the original [Fouvry, Cor. 1](https://www.numdam.org/article/ASENS_1987_4_20_4_617_0.pdf) rails remain strictly above the needed .506 and its uniform residue size condition as before. All partial summation, unit restrictions, short harmonic \(\mu(r)/\varphi(r)\) model and rough Bonferroni terms are functions of \(n=e k\) and are identical. The ordinary reduced progression main after that proof is the same \(\mathfrak S(Nn)\) for \(F_R\) and \(b_z\). The proof uses neither the second prime tag nor a particular restriction on \(k\) beyond the permissible long coefficient. Finally, true prime-power errors are \(O(x^{1+o(1)})\) with an opposite \(d\)-sum, as in that proof. This gives precisely the same signed replacement of \(A_{\rm p}-b_z\) by \(K\) in the **single-tag restricted covariance**, not an inference between the two different covariances.

Use the **base** cutoff of [the combined free-branch proof](../full_free_hb_splice/Proof.md), namely \(T_0(s)=\min(x^{.766}s^{-1/2},x^{.918}/s)\), and let \(F\) be its exact free score with the original \(ca>x^{.505}\). Both parts of that base proof apply here. For its one-free reciprocal inequality the summed gcd bound is over actual \(A\)'s dominated by all integers at the same scale; replacing two tags by one reduces the maximum exponent from .6092 to .5312 without altering any multiplier or unit mask. The inequalities for relative errors \(Q S<x\) and \(Q^{5/4}<W\sqrt S\) only improve, and the no-wrap criterion does not require the original lower bound .6038. The elementary two-free rectangle proof likewise only improves its first bound \(x^{.082}Q^{3/2}\); full-period errors are controlled by the same independent interval lengths. The harmonic outer mark sum in both proofs is now \(\sum_p1/(k p)\ll Y^{-1}\). Restricting \(k\) to squarefree (and dropping the sharing labels already paid above) is an admissible outer restriction. No reliance on the two-tag factored annulus is made in this single-tag result.

## 3. New actual two-medium-free score

Put \(C_0=x^{.001}\) and \(\mu_3=\mu*\mu*\mu\). Define
\[
 G(y)=R_z(y)
 \sum_{\substack{s a b c=y,\ c\le C_0\\
                  \max(s,a,bc)\le x^{.427}}}
               \mu_3(c)\log s.                                 \tag{8}
\]
All variables are positive integers. The *output* variables \(s,a,bc\), not the separate \(b\), are bounded by \(x^{.427}\). They are automatically at least \(x^{.146}\) on physical \(y\ge x\), so \(a,b\) are both genuine medium free slots (not necessarily prime). In the notation above \(r=y/s>x^{.573}\), so the original \(r>x^{.505}\) is automatic.

Equation (8) is an **exact** branch of the same five-term finite Möbius identity at \(U=x^{.24}\). In each convolution tuple select two free slot indices in their index order, placing \(a\) at the first index and \(b\) at the second. The remaining product is \(c\le C_0\); hence no other free slot in a selected tuple is medium, and all remaining truncated factors are unrestricted. The remaining convolution is \(\mu_3(c)\). After summing the choices of positions, the coefficient is
\[
 \sum_{j=3}^5(-1)^{j-1}\binom5j\binom{j-1}2=10-15+6=1.
\]
The values \(a,b\) are ordered in the actual sum, so this convention also holds if \(a=b\); there is no hidden assumption that \(r\) is squarefree. None of the selected free \(a,b\) can be huge at the base cutoff (every \(s\le x^{.427}\) has \(T_0(s)\ge x^{.491}\)), and the rest of the free slots are \(\le c\). Thus (8) is disjoint in the original identity from the previously removed huge-free branch.

On every **actual squarefree triprime** \(y\) with largest prime at most \(x^{.427}\), only \(c=1\) is possible in (8); each of the three true primes may be \(s\), with the other two in either order as \(a,b\). Thus \(G(y)=2\log y\) there. In \(K\), every nonzero \(s\) is a prime singleton: a prime \(r\le x^{.427}\) is too small, while the product of the other two is \(>x^{.573}\). Hence \(K=\log y\). The base \(F\) has only \(a=r,c=1\) at each such \(s\), since proper divisors of \(r\) are below \(x^{.427}\); thus \(F=-\log y\). We conclude \(K-F-G=0\) on this whole physical family, which contains every near-equal true triprime but is not limited to nearly equal exponents. Any prime factor \(\le z\) would make all scores zero anyway. Earlier exact all-squarefree-semiprime deletion is unaffected, since (8) has three polynomially large outputs and cannot contain a semiprime.

## 4. Unconditional fixed-target signed cancellation of (8)

For every \(B>0\) and \(D\) fixed, uniformly in \(N\) and \(|u_{d,k}|\le L^D\tau(d)^D\tau(k)^D\tau(N-dk)^D\), the actual single-tag, squarefree-\(k\) region has
\[
 \sum_d\left|\sum_{e,k}\beta_1(e)u_{d,k}G(N-ek)\right|
      \ll_{B,D} x^{3/2}L^{-B}.                              \tag{9}
\]
As before, nonunit rough \(y\) can be dropped before opening roughness: it is a multiple of a large prime \(p'>z\) dividing \(N\), costing \(O(xL/z+L)\) possible \(y\)'s. Fixed divisor moments in \(y,N-y,N-dk\) handle multiplicities with an extra free \(O(Y)\) factor. Keep \((c,N)=1\); dropping the masks on the remaining rough factors in (8) therefore has an arbitrary-log cost. The whole residue \(N\bmod A\) and \((A,N)=1\) are maintained.

Fix \(c,A,k\) and expand the true rough factors \(R_z(s),R_z(a),R_z(b)\) independently at \(J=\lceil C_B\ell\rceil\) using divisors \(\lambda_s,\lambda_a,\lambda_b\le z^J=x^{o(1)}\). The \(R_z(c)\) factor remains exact. The triple replacement error is bounded by telescoping, using \(|P(v)|\le\tau(v)\) for each truncated rough polynomial and bounding each error by \(\binom{\omega_{\le z}(y)}{J}\). Its fixed high moments have factorial tails as in [the one-free proof, §2](../long_free_mu2_row/Proof.md); hence it is negligible against the full divisor envelope with the \(N-y\) multiplicity. No pairwise coprimality of these three opened divisors is required. On the literal unit equation only \((c\lambda_s\lambda_a\lambda_b,A)=1\) terms are present. Upon dividing the three variables by their respective labels the residue is \(N\overline{c\lambda_s\lambda_a\lambda_b}\bmod A\), a unit to which (1) applies uniformly.

All three underlying free lengths have product \(X\asymp x/(c\lambda_s\lambda_a\lambda_b)\), between \(x^{.999-o(1)}\) and \(O(x)\). The upper bounds come from the three actual outputs \(s,a,bc\). On independent boxes they are \(\max X_i\le x^{.427+o(1)}\le X^{.430}\), and \(A\le x^{.531+o(1)}\le X^{.532}\), \(A\ge X^{.51}\). These exponent inequalities include the entire \(c\le x^{.001}\) range and leave a fixed small reserve. The independent smooth boxes can be chosen with log-power derivatives: for each true \(c\), split the \(a,b,s\) windows into relative \(L^{-J_0}\) intervals, and split \(k\) on the same relative mesh to keep the \(I_k\) endpoint test independent. Only the two original radial boundaries and small smooth transitions at the individual output endpoints are changed. At radial boundaries the physical \(e\)-window changes by \(O(YL^{-J_0})\), giving \(O(xL^{-J_0}+Y)\) pairs \(e,k\) before divisor weights; for an individual output endpoint, at fixed \(c\) and two other variables the transition has length \(O(X_i L^{-J_0})\) on that free length. Over dyads the total length contribution before divisor weights is \(O(xL^{-J_0}\log^C x)\) by summing \(1/c\), and the floor term saves a fixed power because the other two output lengths are at most \(x^{.854+o(1)}\) and \(c\le x^{.001}\). Artificial mesh joins can be smoothed with even smaller relative widths, as in the previous proof. Higher divisor moments pay the boundary losses with arbitrary log precision, including the \(\log s\) factor. The smooth normalized \(\log s\) is allowed on its actual independent slot.

Applying (1) and the divisor-power multiplicity of \(A=k p\) incurs a power-saving aggregate per fixed \(d\): the scale factor is \(X/A\), and the outer \(c\)-sum costs \(\sum_{c\le C_0}\tau(c)^C/c\ll L^C\). The opened-divisor lists have \(x^{o(1)}\) cost, harmless in this power part. The pointwise divisor envelope on \(d,k,y'\) likewise costs \(x^{o(1)}\) only after a fixed power has been gained. The remaining sum over \(d\) costs \(O(Y)\). Log-size tails and boundary terms above use true moment bounds.

The reduced model in (1) is also elementary. Each of its three free unit sums has main \((\varphi(A)/A)\) times the corresponding real interval integral, with error \(\ll\tau(A)\) times weight variation by ordinary Möbius counting. Since each free length exceeds \(x^{.140-o(1)}\), these errors are power-small after the same outer harmonic sum. Expanding and then completing all three rough scalar sums gives \(W_z(A)^3\) with \(W_z(A)=\prod_{p'\le z,p'\nmid A}(1-1/p')\). The true main for fixed \(A,k\) is therefore
\[
 \frac{\varphi(A)^2 W_z(A)^3}{A^3}
 \left(\sum_{\substack{c\le x^{.001}\\(c,AN)=1}}\frac{\mu_3(c)R_z(c)}{c}\right)
 \int_{\substack{s,a,v>0,\ \max(s,a,v)\le x^{.427}\\ s a v\in I_k}}
       (\log s)\,ds\,da\,dv .                               \tag{10}
\]
Here \(v=bc\) is the actual output slot; its Jacobian \(db=dv/c\) places the entire \(c\)-sum **outside** the integral. In particular no sharp \(c\)-dependent profile endpoint was silently replaced by a fixed one. Formula (10) has the correct reduced-unit coefficient \(\varphi(A)^2/A^3\), with one \(1/\varphi(A)\) from the model and three unit densities. It is not an aggregate main from a fictitious unrestricted \(d_3\) source.

The \(c\)-sum in (10) is \(O_B(L^{-B})\) by iterating the masked rough harmonic \(\mu/n\) result of [the one-free proof, (11)](../long_free_mu2_row/Proof.md). For clarity, expand the product of the three indicators \(1-1_{n_i>T^{1/3}}\) on the hyperbolic region \(n_1n_2n_3\le T\). The all-small sum is exactly the product of three truncated harmonic sums. Each nonempty subset of imposed large variables contributes one term in the finite inclusion–exclusion; choose any one of these variables and perform it last. Its lower endpoint is \(T^{1/3}\), its upper endpoint is either at least as large or the term is empty, and the other variables cost only log powers. The common mask \(R_z(n)1_{(n,AN)=1}\) is completely multiplicative, so all these hyperbola factorizations are exact. Here \(T=x^{.001}\) is polynomial. The integral in (10) is \(O(x L^3)\) by \(y=sav\). The sum of \(1/A\) over the true single marks and \(k\asymp Y\) is \(O(1)\), or \(O(Y^{-1})\) for fixed \(k\); use actual \(d,k\) divisor moments for the outer \(u\). This proves (9).

In particular, with \(w_d=\beta_1(d)\), \(w_e=\beta_1(e)\) and the exact unit box and squarefree \(k\) of §2,
\[
 \sum_{d,e,k}w_dw_e(A_{\rm p}-b_z)(N-dk)(A_{\rm p}-b_z)(N-ek)
 =\sum_{d,e,k}w_dw_e(K-F-G)(N-dk)(K-F-G)(N-ek)
   +O_B(x^{3/2}L^{-B}).
\]
One may instead discard the labels dividing \(k\) from each \(w\), with the same conclusion; the two versions differ by a power-small term. Each substitution is valid with the actual opposite row, and all fixed-degree score weights lie within the stated envelope. No unsupported independence of the two reflected values is used.

## 5. The removal is not absolutely small

Against an actual opposite genuine prime row, the positive and absolute negative divisor-labelled masses of (8) are each \(\gg x^{3/2}\ell^6\varphi(N)/N\). The estimate in §4 before the signed \(c\)-sum applies also to each of two fixed-sign restrictions: \(c=1\) with coefficient \(+1\), and \(c=p'\) genuine prime with \(x^{.0002}<p'<x^{.0006}\), where \(\mu_3(p')=-3\). For the absolute model restrict \(y\) to \([1.22x,1.26x]\subset I_k\) and the \(a,s\) exponents to \([.330,.334]\); then \(v=y/(as)\) has exponent in \([.332,.340]+O(L^{-1})\) and is permitted. The integral contributes \(\gg xL^3\) by the two harmonic measures and \(\log s\). After removing the finitely many prime factors of \(AN\), the reciprocal \(c\) mass is either \(1\) or a positive constant. The exact unit Euler multiplier satisfies
\[
 (\varphi(A)/A)^2 W_z(A)^3
 =V_z^3\prod_{\substack{p'\le z\\p'\mid A}}(1-1/p')^{-1}
          \prod_{\substack{p'>z\\ p'\mid A}}(1-1/p')^2
 \ge (1-o(1))V_z^3,\qquad V_z=\prod_{p'\le z}(1-1/p').
\]
Thus each sign slice has its natural true model at least \(x\ell^6/A\) per real admissible label, with the proved negligible errors.

For the actual opposite prime availability on **squarefree \(k\)**, one may use the earlier two-tag Maynard wedge as a subset of the single-tag support on the opposite side only; its mark multiplicity is at most a fixed multiple of \(\beta_1(d)\). Insert the exact squarefree indicator \(\sum_{f^2\mid k}\mu(f)\) there. The \(f>L^C\) physical tail is \(O(xL^{1-C})\) by \(\sum_{f>L^C}\#\{k:f^2\mid k,k\le1.1Y\}\ll Y/L^C\), and \(O(Y)\) possible marked \(d\)'s. For \(f\le L^C\), the earlier [Maynard prime-wedge proof with auxiliary divisor of \(k\), §1](https://github.com/mxym/math/commit/bafa9b8f) (also used in [the above-root proof, §3](https://github.com/mxym/math/commit/48786012bff7073486a373df69f35611a803e916)) applies to the real modulus \(df^2\), including the moving endpoints \(N-dk\); it asserts the requisite log precision for every polylogarithmic auxiliary divisor. Its main per \(d\), after the \(f\)-sum, is
\[
 \frac{|[Y,1.1Y]|\,d}{\varphi(d)}
       \prod_{p'\nmid N}\left(1-\frac{\varphi(d)}{\varphi(d p'^2)}\right).
\]
Only \((d,N)=1\) is included; terms \(f\) sharing \(N\) have zero true prime mass. The local ratio is \(1/(p'(p'-1))\) when \(p'\nmid d\), and \(1/p'^2\) otherwise, so that absolutely convergent product has a uniform positive lower bound. The two-tag rectangle is strictly inside the earlier Maynard wedge. Here the auxiliary parameter is \(j=f^2\le L^{2C}\); its exponent is \(o(1)\), and the distribution bound already sums these auxiliaries with fixed divisor powers. The truncated model tail is negligible by \(\varphi(d)/\varphi(df^2)\le 1/(f\varphi(f))\) for squarefree \(f\). The marked \(d\)-occupancy from the same wedge then gives \(\gg x\varphi(N)/N\) genuine opposite prime mass on squarefree \(k\). The previously bounded \(p\mid k\) sharing deletion does not diminish this lower bound. The harmonic single-tag sum in the \(e\)-row satisfies \(\sum_p1/(k p)\gg Y^{-1}\) uniformly for unit \(k\), even after excluding the finitely many prime factors of \(N k\). This completes the claimed lower bounds for the two actual opposing labels. It does **not** assert a uniform lower bound for the count of real triprimes in the removed region: that count is not inferred from a free-integer main.

In the earlier **two-tag** source \(A\) has exponent .604–.609 and (7) fails. The single-tag result therefore cannot be imported into that source by marginalization of one tag. Conversely the separate two-tag medium-slot calculation uses a genuinely different angle and the stated Jain triple theorem. No estimate for all sharps, non-squarefree \(k\), or the remaining higher rank/giant-factor covariance is claimed.

The accompanying checker replays the rational exponent rails, local cyclotomic and CRT identities, and selected literal rank-two and rank-three coefficient identities. It does not numerically validate the analytic distribution bounds.
