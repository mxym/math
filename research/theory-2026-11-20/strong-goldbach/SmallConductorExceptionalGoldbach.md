# A conditional pointwise Goldbach theorem at small-conductor exceptional zeros

**Literature status (2026-11-21).** These implications are retained as conditional calculations, not as coverage of any large even target. [Banks, Theorem 1.1 (October 2026)](https://arxiv.org/abs/2610.15483v1) gives a positive uniform lower bound for `(1 − β) log q₀` for primitive real Dirichlet characters; see also [Kerr's simplification](https://arxiv.org/abs/2610.21099v1). In the small-conductor window this product is bounded above by `c Δ₀ / √log N`; in the polynomial-conductor window it is at most `κ (log N)^(−A)` for fixed positive `A`. Both tend to zero. Thus Banks's result rules out the hypotheses for all sufficiently large `N`. This is independent of RH/GRH and does not settle ordinary binary Goldbach.

**Status.** This is a research proof of a pointwise theorem in a *conditional exceptional-zero regime*. It does not assert that such a zero exists, settle the no-exception regime, or prove unconditional strong Goldbach.

There are positive absolute constants \(c,\Delta_0\) such that the following holds for all sufficiently large even \(N\). Put \(L=\log N\). Suppose a primitive real nonprincipal character \(\chi\) of conductor \(q_0\) has a real zero \(1-\delta\), where
\[
 q_0\le \exp(c\sqrt L),\qquad 0<\Delta=\delta L\le \Delta_0.                 \tag{1}
\]
Assume the hard local condition
\[
 \chi(a)\chi(N-a)=-1 \quad
       \text{for all }a\bmod q_0\text{ with }(a(N-a),q_0)=1.              \tag{2}
\]
Then \(N\) is the sum of two primes in \((N/3,2N/3)\), one of each \(\chi\)-sign. More precisely, their representation sum with the log of the majority prime has lower bound \(\gg \delta N\mathfrak S(N)\). All implied constants below, including \(\Delta_0\), are fixed before varying \(N,q_0,\delta\).

Condition (2) is precisely the stratum \(C_\chi(N)=-1\) of [Matomäki–Merikoski, arXiv:2112.11412v2, Theorem 1.4 and Lemma 2.5, (16), (18)](https://arxiv.org/html/2112.11412v2#S2). In their notation \(q_0=2^e q'\), \(e\in\{0,2,3\}\), \(q'\) odd squarefree, and the ratio of their two character sums (using the minus reflection) is
\[
 C_\chi(N)=1_{\varphi(2^e)\mid N}(-1)^{N/\varphi(2^e)}\chi(-1)
                      \prod_{\ell\mid q',\ \ell\nmid N}\frac{-1}{\ell-2}.
\]
For \(e=0\) the 2-adic factor is 1 since \(N\) is even. For \(e=2\) the sign is \((-1)^{N/2}\); for \(e=3\) the factor vanishes unless \(4\mid N\), then its sign is \((-1)^{N/4}\). The average is over a nonempty set of reduced pairs by (16); it equals \(-1\) exactly if every product equals \(-1\). In particular all odd primes \(\ell\ge5\) dividing \(q_0\) divide \(N\) (otherwise the absolute local average is at most \(1/3\)); \(2\mid N\) already. The only possibly missing prime of the conductor is 3. Write
\[
 \mathfrak S(N)=\frac{N}{\varphi(N)}
                         \prod_{\ell>2,\ \ell\nmid N}
                            \left(1-\frac{1}{(\ell-1)^2}\right).
\]
We use the terms “majority” for \(\chi=-1\), “minority” for \(\chi=+1\), in the prime ranges of (1).

## 1. Relative error reserve and the signed high-conductor input

Use the effective quadratic bound \(1-\beta\gg q_0^{-1/2}(\log(2q_0))^{-2}\), e.g. [Bennett–Martin–O’Bryant–Rechnitzer, Proposition 1.12 and its proof](https://arxiv.org/pdf/1802.00085). Accordingly, after \(c>0\) in (1) is decreased, every error \(N\exp(-b\sqrt L)\) below, for the finitely many fixed \(b>0\) arising before that choice, is \(o(\delta N)\), even when \(\delta\) is smaller than every negative power of \(L\). A power saving is more than sufficient.

We will use two precise prime estimates:
1. **Ordinary exceptional-adjusted BV, with proof.** Fix \(\xi>0\) and \(C\ge0\). For \(Q\le X^{1/2-\xi}\), let \(R_*=e^{a_*\sqrt{\log X}}\), \(a_*>0\) sufficiently small. The one possible exceptional primitive real character \(\chi_*\) of conductor \(q_*\le R_*\) and real zero \(\beta_*\) in the effective zero-free cut is retained. Then
\[
 \sum_{d\le Q}\tau(d)^C
   \max_{\substack{1\le y\le X\\(b,d)=1}}
   \left|\theta(y;d,b)-\frac{y}{\varphi(d)}
          +1_{q_*\mid d}\chi_*(b)\frac{y^{\beta_*}}{\beta_*\varphi(d)}\right|
        \ll_{\xi,C} X e^{-b_*\sqrt{\log X}},                             \tag{BV}
\]
omitting the exceptional term when there is none. To see this, start with \(\Lambda\), expand in characters, and pass to their primitive conductors \(r\). The induction cost is \(\sum_{r\mid d,d\le Q}\tau(d)^C/\varphi(d)\ll_C(\log X)^{O_C(1)}\tau(r)^C/\varphi(r)\), by \(\varphi(ru)\ge\varphi(r)\varphi(u)\) and a fixed divisor moment; the imprimitive correction is \(O((\log X)^2)\) per modulus. For the dyadic conductors \(r\asymp F>R_*\), [Akbary–Hambrook, arXiv:1309.2730v1, Theorem 1.2 and (1.1)](https://arxiv.org/pdf/1309.2730v1), divided by \(F\), bounds the \(1/\varphi(r)\)-weighted primitive maximal sum by
\[
   (\log X)^{O(1)}(X/F+\sqrt X F+X^{2/3} F^{1/2}+X^{5/6}).
\]
Use \(\tau(r)^C\ll_\kappa r^\kappa\) with \(\kappa\) small in terms of \(\xi\): the first term saves exponentially at \(F\ge R_*\), and the other terms save a power. At \(r\le R_*\), use the ordinary effective zero-free region up to height \(T=e^{\sqrt{\log X}}\) and Landau–Page uniqueness; the contour stays on an effective line \(1-b_1/\sqrt{\log X}\) apart from the principal pole and the one real zero. The truncated explicit formula gives \(O(X e^{-b_2\sqrt{\log X}})\) in the primitive maximum after retaining these terms: for \(y\ge X e^{-b_3\sqrt{\log X}}\) the included zeros on the left of the line are summed using the local zero count and harmonic denominators; for smaller \(y\) use \(\Lambda\le\log X\) and the trivial bound for the retained terms. As usual one can choose the truncation heights in \([T,2T]\) and avoid integer endpoints by half-integers. There is no contribution from a reflected zero near 0 at size \(1/\beta_*\): the contour and the retained zero are near 1. Decrease \(a_*\) to absorb the count of small primitive characters with their \(1/\varphi(r)\) weight. Removing proper prime powers in the original AP maximum costs \(O(Q^{1+o(1)}\sqrt X(\log X)^2)\). This gives (BV) at the stated scale. At every \(X\ge c_3 N^\epsilon\) (\(c_3>0,\epsilon>0\) fixed) used below, take \(c\) in (1) small enough that \(q_0\le R_*\); \(\delta\le\Delta_0/L\) puts its zero inside the retained cut. The application also uses this small-conductor prime estimate in (7) below.
2. **Signed ABL high conductors.** From the proof of [Assing–Blomer–Li, arXiv:2005.13915v1, §4, printed pp. 13–19, especially (4.2)–(4.5) on pp. 17–18](https://arxiv.org/html/2005.13915v1#S4), use precisely this unconditional part of their GRH-range analysis: with \(X\asymp N\), \(R=N^\omega\) for a sufficiently small fixed \(\omega>0\), \(c_1,d_1\le N^{\omega_1}\) for sufficiently small absolute \(\omega_1>0\), \(d_1\mid c_1^\infty\), and \(Q\ll\sqrt N\), one has
\[
 \sum_{\substack{v\le Q\\(v,N)=1\\v\equiv v_0\bmod c_1}}
 \ \sum_{\substack{p'\le X\\p'\equiv a_0\bmod d_1}}
 \Lambda(p')\,u_R(p'\bar N;v)
      \ll c_1 N L^{O(1)} R^{-1/11}.                                    \tag{3}
\]
Here \((v_0,c_1)=(a_0,d_1)=1\), and \(u_R(n;v)\) is the normalized sum of characters of conductor \(>R\) mod \(v\). The numerator \(N\) satisfies their large-residue hypothesis \(|a_1|\le X^{1+\omega_1}\) after decreasing the exponents and taking \(N\) large, and \(a_2=1\). This estimate is **signed over moduli**, with arbitrary fixed residue class \(v_0\), not an absolute statement. The use of polynomial \(c_1,d_1,R\) in the high-conductor part must be read from that proof, not from the unconditional logarithmic parameter range in their Theorem 2.1. In §4 they bound \(S_2\) in (4.2): apply Proposition 4.1 to the balanced factorization cases of (4.3), and BFI/Deligne and Pólya–Vinogradov to the long-factor cases (4.5). These lines contain no GRH step. GRH enters only afterward in evaluating \(S_1\), which is **not** used as stated here. \(X\) can be any actual endpoint in a fixed compact subinterval of \((0,N)\); differences then give prime intervals. It is enough here to take \(c_1=d_1\) and \(v\le\sqrt{2N/3}\). At \(v\le R\) the high component is zero.

Fix \(\omega\) small enough for (3), and take a much smaller \(\eta>0\), with
\[
 40\eta<\omega/11,\qquad 11\eta<\omega_1,\qquad
 \omega+11\eta<1/10.
\]
All inequalities are to have strict slack (e.g. \(\eta\) can be decreased again). Choose a fixed \(\epsilon>0\) sufficiently small compared to \(\eta\), and put \(D=N^\eta\), \(z=N^\epsilon\). We use fundamental-lemma lower and upper weights for a dimension-at-most-two sieve at level \(D\) and threshold \(z\); choose \(\eta/\epsilon\) large enough that their model multiplicative sums are between fixed positive constants times the sifted Euler product. For this use of the fundamental lemma see Friedlander–Iwaniec, Opera de Cribro, Lemma 6.11 (also stated in [Kurlberg–Lester–Rosenzweig, §2.1](https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/superscars-for-arithmetic-point-scatters-ii/3CCB969E058792C1803466AE0EF29136)). They are supported on squarefree \(k\le D\) composed of eligible primes \(<z\) and are bounded by a fixed divisor power, as with the standard beta sieve. We also use the corresponding dimension-one upper sieve at level \(X^{1/8}\), threshold \(X^{1/100}\), in §5. These are ordinary fixed-parameter fundamental-lemma applications; no sieve beyond dimension two is needed.

## 2. Prime-row divisor decomposition with the summed power presieve

Let \(I=(N/3,2N/3)\). Set \(\lambda=1*\chi\) (nonnegative), \(m=N-p\), and
\[
 A_k=\sum_{\substack{p\in I\ {\rm prime}\\p\nmid N,\ \chi(p)=-1\\
                         (N-p,q_0)=1,\ k\mid N-p}}\log p\,\lambda(N-p).
\]
For any of our sieve weights \(w_k\), the following aggregate evaluation holds:
\[
 \sum_k w_k A_k
  = \frac{2\nu}{\varphi(q_0)}
        \int_I(1+t^{-\delta})\,dt
        \sum_{\substack{k\le D\\(k,Nq_0)=1}}w_k
        \sum_{\substack{d\ge1\\(d,Nq_0)=1}}
                    \frac{\chi(d)}{\varphi([d,k])}
       +O(N e^{-b\sqrt L}),                                           \tag{4}
\]
where \(\nu=\#\{a\bmod q_0:(a(N-a),q_0)=1,\ \chi(a)=-1\}\), and \([d,k]\) denotes the lcm. We explicitly check the overlap in \([d,k]\), the summed error, and the variable hyperbola boundary.

On the prime row \(m\) is a unit modulo \(Nq_0\) by the conditions and (2), with \(\chi(m)=+1\). Thus
\(\lambda(m)=2\sum_{d<\sqrt m,d\mid m}\chi(d)+1_{m=\square}\chi(\sqrt m)\).
The square boundary, and replacing \(\log p\) by \(\Lambda\) on the prime side if convenient, each cost \(N^{1/2+o(1)}\) in the fully weighted sums (there are \(O(\sqrt N\log N)\) possible squares or proper prime powers and divisor multiplicities are \(N^{o(1)}\)). Any \(k\) with \((k,Nq_0)>1\) is either outside the sieve or has zero term. For each remaining squarefree \(k\), write \(d=u v\), \(u\mid k^\infty,\ (v,k)=1\), put \(w=[u,k]\), and observe \([d,k]=w v,\ (w,v)=1\). Since \(k\) is squarefree,
\[
 k=\operatorname{rad}(w),\qquad
         \varphi(w)=\varphi(k)u/\operatorname{rad}(u).
 \tag{5}
\]
For fixed \(w\) the possibilities for \(u\) have multiplicity at most \(\tau(k)\) (only exponents 0 and 1 can coincide). This exact regrouping is how the overlap is handled; replacing \([d,k]\) by \(dk\) would not suffice.

Discard \(u>N^{10\eta}\) in the actual row at power-saving cost. Indeed for each \(u,k\), the prime log progression upper bound by Brun–Titchmarsh is \(\ll N/\varphi(wv)\) for \(d<\sqrt N\), since \([d,k]\le D\sqrt N\) and the residue \(N\) is reduced. The tail of \(\sum_{u\mid k^\infty}\operatorname{rad}(u)/u\) at \(U=N^{10\eta}\) is
\[
 \le U^{-1/2}\prod_{\ell\mid k}\left(1+\frac{\sqrt\ell}{1-\ell^{-1/2}}\right)
       \le U^{-1/2}k^{1/2}N^{o(1)}.                                    \tag{6}
\]
Here \(\prod_{\ell\mid k}O(1)=N^{o(1)}\). Sum in \(v\) and \(k\) with harmonic totient weights and the fixed divisor powers to retain the power saving.

On the surviving \(u\) range apply (3) with auxiliary \(d_1=c_1=q_0 w\), and variable modulus \(v\). The congruence for the prime modulo \(v\) is \(p'\equiv N\bmod v\). Its reduced residue modulo \(d_1\) specifies \(p'\equiv N\bmod w\) and one of the \(\nu\) allowed residues modulo \(q_0\). The \(v\)-weight \(\chi(d)=\chi(u)\chi(v)\) is constant after splitting \(v\) into unit classes modulo \(d_1\); this is an exact use of (3) on the signed weight. The number of classes costs at most \(d_1\), and (3) itself costs \(d_1\). Summing over \(w\le N^{11\eta}\), its divisor multiplicities and the \(q_0\) residue classes costs at most \(N^{33\eta+o(1)}\) total (the subpower factors include \(q_0\)). The asserted high-conductor saving follows by our parameter choices.

To retain the dependent boundary \(d<\sqrt{N-p'}\), partition \(I\) by a mesh of step \(N e^{-b_0\sqrt L}\) with a sufficiently small fixed \(b_0>0\), and on each interval freeze the cutoff in \(p'\). For each fixed \(d\), at most one adjacent interval can be misassigned; its actual AP weight is \(\ll L [N e^{-b_0\sqrt L}/[d,k]+1]\), by counting all integers. Summing gives error \(\ll N e^{-b_0\sqrt L} L^{O(1)}+N^{1/2+\eta+o(1)}\). Indeed \(\sum_{d\le\sqrt N,k\le D}|w_k|/[d,k]\ll L^{O(1)}\) by expanding \((d,k)=\sum_{r\mid(d,k)}\varphi(r)\). The same estimate controls the corresponding integral main-term variation, replacing \(1/[d,k]\) by \(1/\varphi([d,k])\) at log-power cost. Hence no independent endpoint is presumed and the number of high-conductor applications grows only subpolynomially.

It remains to justify the low-character terms in this **summed** calculation. For distinct roles of the moduli \(d_1\) and \(v\) with \((d_1,v)=1\), a character modulo \(d_1\) and one modulo \(v\) of conductor \(r_*\le R\) induce a primitive product of conductor \(s_* r_*\), where \(s_*\mid d_1,r_*\mid v\) and \((s_*,r_*)=1\). In absolute error sums there is no cost for the split into \(v\) residue classes: each \(v\) uses just its unique class. By (5) the coefficient multiplicities in the \(d_1\)-sum are bounded by a fixed divisor power of \(d_1\), besides the at most \(q_0\) choices of the prime residue. Imprimitive-character corrections from prime powers at excluded primes cost \(N^{1/2+11\eta+o(1)}\) in all by the trivial \(O(L^2)\) estimate per pair of moduli and residue. Inducing from the two primitive conductors costs at most
\[
 \left(\sum_{\substack{d_1\le q_0N^{11\eta}\\s_*\mid d_1}}
             \frac{\tau(d_1)^{O(1)}}{\varphi(d_1)}\right)
 \left(\sum_{\substack{v\le\sqrt N\\r_*\mid v}}\frac1{\varphi(v)}\right)
 \ll \frac{\tau(s_*)^{O(1)} L^{O(1)}}{\varphi(s_*)\varphi(r_*)}.
 \tag{7}
\]
Summing over conductor factorizations only adds a divisor power. Thus the total low-character error reduces, up to \(q_0 L^{O(1)}\) and the mesh size, to the primitive maximal Vaughan mean with weight \(\tau(f)^{O(1)}/\varphi(f)\) for \(f\le q_0N^{11\eta+\omega}\). For \(f\) above \(\exp(c_2\sqrt L)\), its dyadic bound \(O(L^C[N/f+\sqrt N f+N^{2/3}\sqrt f+N^{5/6}])\) gives exponential saving, with a divisor power absorbed as in §1. Below that cutoff the classical explicit formula retains just the principal term and the one Page zero, with exponential error uniformly; choose \(c_2\) small enough to absorb the sum over all small primitive characters, then \(b_0\) and \(c\) in (1) small enough to absorb the mesh and \(q_0\) losses. This treats \(p'\) endpoints \(\asymp N\); no long-range max-prefix issue is needed except the standard primitive maximal bound. The retained exceptional character is in the \(d_1\) character (since \(q_0\mid d_1\)); at every chosen majority residue its sign is \(-1\), giving \(1+t^{-\delta}\) on differentiating the two main terms. They therefore yield exactly the finite integral with \(d<\sqrt{N-t}\) in (4).

Finally extend the \(d\)-sum inside that integral to infinity. With the same \(u,v\) factorization, apply [ABL, Lemma 5.2](https://arxiv.org/pdf/2005.13915) to the coprime \(\chi(v)/\varphi(v)\)-tail beyond \(\asymp \sqrt N/u\). Its error for \(u\le N^{10\eta}\) is \(N^{-1/2+10\eta+o(1)}\), uniformly since \(q_0=N^{o(1)}\), and the \(\varphi(k)^{-1}\) harmonic factor and \(N^{o(1)}\) \(u\)-weights cause no loss of this saving. For \(u>N^{10\eta}\) use (6) and bounded log powers for the full and partial \(v\)-sums. Interchanging the finite \(k\)-sum and convergent \(d\)-sum is justified by these uniform tails. This proves (4).

## 3. The local sieve model and a lower bound for its main term

For the prime row put
\[
 T_\ell^{\rm pr}=1+\frac{\chi(\ell)}{(\ell-1)(1-\chi(\ell)/\ell)}
      \quad(\ell\nmid Nq_0),\qquad
 P_{\rm pr}=\sum_{(d,Nq_0)=1}\frac{\chi(d)}{\varphi(d)}
     =L(1,\chi)\prod_{\ell\mid N}(1-\chi(\ell)/\ell)
                     \prod_{\ell\nmid Nq_0}\left(1+\frac{\chi(\ell)}{\ell(\ell-1)}\right).
\]
The last product converges absolutely; factors with \(\chi=0\) are 1. For a squarefree \(k\) the inner sum in (4) is \(P_{\rm pr}\prod_{\ell\mid k}g_{\rm pr}(\ell)\), where for eligible \(\ell\)
\[
 g_{\rm pr}(\ell)=\frac{T_\ell^{\rm pr}-1+1/(\ell-1)}{T_\ell^{\rm pr}}
   =\begin{cases}(\ell^2-\ell-1)^{-1},&\chi(\ell)=-1,\\
                   (2\ell-1)/(\ell^2-\ell+1),&\chi(\ell)=+1.
     \end{cases}                                                       \tag{8}
\]
At \(\ell\mid Nq_0\) the density is zero. These identities replace the \(d\)-exponent zero local term 1 by \(1/(\ell-1)\) when \(\ell\mid k\); the other local terms are unchanged. They give a dimension-at-most-two model since \(0\le g_{\rm pr}(\ell)<1\) and \(g_{\rm pr}(\ell)\le2/\ell+O(\ell^{-2})\) for all \(\ell\ge3\), with all constants absolute. Write \(M_{\rm pr}=P_{\rm pr}\prod_{\ell<z,\ell\nmid Nq_0}(1-g_{\rm pr}(\ell))\). The lower sieve applied to the **nonnegative** \(\lambda(m)\) sequence gives
\[
 A_{\rm rough}:=\sum_{\substack{p\text{ as in }A_1\\ P^-(N-p)\ge z}}
                       \log p\,\lambda(N-p)
       \gg N\frac{2\nu}{\varphi(q_0)} M_{\rm pr}-O(N e^{-b\sqrt L}).
 \tag{9}
\]
The inequalities are applied before expanding the signed divisor sum for \(\lambda\). No truncation error from replacing the original positive sequence by a signed lower pointwise approximation is being asserted.

Obtain a lower bound on the local main by comparison with an elementary one-point sift. Consider integers \(m\in I\) with \((m,Nq_0)=1,\ \chi(m)=+1\), weighted by \(\lambda(m)\), and divisibility tests \(k\mid m\). The same hyperbola formula counts these by elementary floors, with aggregated error \(N^{1/2+\eta+o(1)}\), since each \(k,d\) costs at most \(q_0\tau(N)=N^{o(1)}\) floor errors (split the \(\chi\) classes and insert the coprimality with \(N\) by inclusion-exclusion). Conditions are compatible by \((d k,N q_0)=1\). Removing the square diagonal and completing the harmonic \(d\)-sum uses exactly the \(u,v\) argument from §2, now with \(1/[d,k]\) in place of \(1/\varphi([d,k])\) and ordinary coprime character sums from Pólya–Vinogradov. Its model is
\[
 \begin{gathered}
 H_N=\prod_{\ell\mid Nq_0}(1-1/\ell),\qquad
 P_{\rm int}=L(1,\chi)\prod_{\ell\mid N}(1-\chi(\ell)/\ell),\\
 T_\ell^{\rm int}=(1-\chi(\ell)/\ell)^{-1},\qquad
 g_{\rm int}(\ell)=1-\frac{1-1/\ell}{T_\ell^{\rm int}}
 \quad(\ell\nmid Nq_0),\\
 M_{\rm int}=H_N P_{\rm int}
                  \prod_{\ell<z,\ell\nmid Nq_0}(1-g_{\rm int}(\ell)).
 \end{gathered}
\]
The factor \(H_N\) comes from taking half the reduced \(q_0\)-classes and excluding divisors of \(N\) outside \(q_0\), multiplied by the factor 2 of the hyperbola. This model is likewise dimension at most two. Its **upper** sieve shows the corresponding sifted physical sum is \(\ll N M_{\rm int}+O(N^{1-b_1})\). But it is at least twice the number of actual minority primes in \(I\), which is \(\gg\delta N\): the adjusted prime-log asymptotic on the union of their \(q_0\)-classes is \(\frac12\int_I(1-t^{-\delta})\,dt+O(N e^{-b\sqrt L})\asymp\delta L N\). Divide by logs \(\asymp L\). The error is negligible relatively by §1. Therefore \(M_{\rm int}\gg\delta\).

The ratio is explicit. On admissible unit pairs, (2) means the reflection involution pairs opposite signs, so
\[
 \frac{2\nu}{\varphi(q_0)}
     =\prod_{\ell\mid q_0,\ \ell\nmid N}\left(1-\frac1{\ell-1}\right).
\]
All conductor primes are \(<z\) for \(N\) large. Comparing the displayed products for \(M_{\rm pr},M_{\rm int}\), on \(\ell<z,\ell\nmid Nq_0\) the ratio is
\((1-1/(\ell-1))/(1-1/\ell)=1-1/(\ell-1)^2\).
The same factor on \(\ell\mid q_0,\ell\nmid N\) arises from \(2\nu/\varphi(q_0)\) and \(1/H_N\); primes dividing \(N\) contribute \(N/\varphi(N)\). At primes \(\ell\ge z,\ell\nmid N\) the ratio is \(1+\chi(\ell)/[\ell(\ell-1)]\), differing from the corresponding Goldbach local factor by \(1+O(\ell^{-2})\). Thus
\[
       \frac{2\nu}{\varphi(q_0)}\frac{M_{\rm pr}}{M_{\rm int}}
              =\mathfrak S(N)(1+O(1/z)),\qquad
       A_{\rm rough}\gg \delta N\mathfrak S(N).                         \tag{10}
\]
This computes the relevant positive lower scale without presuming a quantitative \(L(1,\chi)\) asymptotic from how close its zero is to 1.

## 4. Every surviving squarefree composite is entirely minority

On a squarefree \(m\) with \(\chi(m)=+1\),
\(\lambda(m)=\prod_{\ell\mid m}(1+\chi(\ell))\), so it vanishes unless **each** prime factor of \(m\) has sign \(+1\), in which case it equals \(2^{\omega(m)}\). For powers we use the preliminary bound: a \(z\)-rough squareful \(m\) in \(I\) is encountered at most \(O(N/z+\sqrt N)\) times, by summing over prime squares, and \(\log p\,\lambda(m)\le N^{o(1)}\); thus this costs a power saving. Since \(z=N^\epsilon\), the squarefree \(r\)-fold rank is bounded by \(1/\epsilon\), fixed.

For primes \(\ell\ge z\), adjusted PNT on the actual minority classes gives
\[
       \sum_{\substack{z\le\ell\le N\\\ell\ {\rm prime},\ \chi(\ell)=+1}}
                       1/\ell\ll \delta L.                             \tag{11}
\]
For clarity, on each fixed ratio dyad with \(X\ge z/2\), the minority prime count is \(\ll \delta X+X e^{-b\sqrt{\log X}}\), after converting log weight (density \(1-t^{-\delta}\ll \delta\log X\)). The exponential remainder summed over \(O(L)\) dyads is negligible relative to \(\delta L\) by choosing \(c\) in (1) small enough depending on fixed \(\epsilon\). Alternatively Matomäki–Merikoski Lemma 4.1 gives precisely this harmonic bound here, since \(z>q_0^{1/2+\xi}\) for each fixed \(\xi>0\) when \(N\) is large. This establishes (11) without using a frequency-averaged \(\chi\) sign heuristic.

## 5. Switching the anchor bounds the entire composite contamination

For any squarefree composite survivor \(m\), select its largest prime \(s\) and write \(m=r s\). The cofactor \(r>1\) is composed only of distinct minority primes \(\ge z\); their rank is bounded, and
\(\sum_{r>1}1/r\ll_\epsilon\delta L\) over these cofactors by (11) and the finite-rank positive expansion (or the Euler-product upper bound). We keep the **actual same-prime** condition \(\chi(s)=+1\) on the varying prime \(s\). For each fixed \(r\) put \(X=N/r\), so \(X\gg z\) in this sum and \(s\in I/r\asymp X\). We can drop the largest-factor filter for the upper bound. We may assume \((r,Nq_0)=1\), as follows already from the prime row.

Apply the upper sieve to primality of \(N-rs\), over the variable \(s\) in its \(\chi(s)=+1\) prime APs. For \(\ell\nmid rNq_0\), the excluded class is \(s\equiv N\bar r\bmod\ell\), reduced, with local factor \(1/(\ell-1)\). The excluded primes dividing \(r\) cost \(r/\varphi(r)=1+O_\epsilon(1/z)\); those dividing \(q_0\) but not \(N\) cost at most one factor 2 (only 3 by (2)). Hence the upper-sieve density is \(\ll_\epsilon\mathfrak S(N)/\log X\). For each squarefree upper-sieve divisor \(d\le X^{1/8}\), \((d,q_0)=1\), the congruence modulus is exactly \(q_0 d\), with \(\phi(q_0)/2\) possible \(s\)-residue classes; all are reduced and have the *same* exceptional sign \(+1\). The log-weighted AP principal-minus-exceptional main has size \(O(\delta X\log X/\varphi(d))\) after summing over those classes. The map \(d\mapsto q_0d\) is injective, and \(q_0d\le X^{1/4}\) for large \(N\), so estimate 1 of §1 bounds the summed remainder \(O(q_0 X e^{-b\sqrt{\log X}})\), including fixed divisor weight, which is exponentially small relative to \(\delta X\) uniformly for \(X\gg z\). Thus
\[
  \sum_{\substack{s\in I/r,\ s\ {\rm prime},\ \chi(s)=+1\\
                                 N-rs\ {\rm prime}}}
                      \log s\ll_\epsilon \delta X\mathfrak S(N).
 \tag{12}
\]
No residue condition is imposed on the other prime beyond primality, and no assertion of two independent minority signs on a fixed AP is made. One minority saving comes from the actual prime \(s\) with its exceptional sign; the second comes from the **fixed cofactor** already known to contain a different minority prime. Since \(\log(N-rs)/\log s\ll_\epsilon1\), and \(\lambda(r s)\le 2^{1/\epsilon}\) in the original squarefree composite sum, summing (12) with \(X=N/r\) and (11) gives
\[
   A_{\rm rough,\ composite}
          \ll_\epsilon (\delta L)\,\delta N \mathfrak S(N)
                    +O(N^{1-b_2}).                                    \tag{13}
\]
In particular the individual relative errors do **not** accumulate with the number of \(r\)'s: their bounds carry \(N/r\), and the sum of the actual cofactor harmonic weights is \(\ll\delta L\) (even the unrestricted harmonic bound would be only log powers). The argument includes the situation where the largest minority factor is larger than \(\sqrt N\).

Taking the fixed \(\Delta_0\) in (1) small enough compared to the constants in (10),(13) proves the claimed positive remainder, consisting only of \(m\) prime with \(\lambda(m)=2\). The preceding bounds are at the necessary minority scale \(\delta N\), not at the much larger \(N\) scale.

## 6. Scope and comparison

Matomäki–Merikoski use nonnegative exceptional-character proxies and a bilinear evaluation with small- and large-factor pieces in their §§2,5. Their principal two-prime term cancels on (2), with remainder too big to prove positivity. The proof here keeps one side a genuine majority prime in the main and uses a \(\lambda\)-weighted dimension-two sieve with the lcm treatment (5) and signed high-conductor ABL input. A bare hyperbola cutoff without this extra input would not suffice: after a power presieve the prime modulus can be \([d,k]q_0>\sqrt N\), and the lower model is only \(\delta N\). [Merikoski’s lower illusory sieve, arXiv:2108.01355](https://arxiv.org/pdf/2108.01355), Theorem 15, uses a different distribution criterion (a general exponent above about \(0.616\)); it is not assumed here. No use is made of recent claimed proofs of Dirichlet GRH or of absence of exceptional zeros. If there is no exceptional character in (1), this argument yields no binary-prime estimate. Nor does it presently cover conductors above the exponential square-root cut, non-tiny \(\delta L\), or a finite verification bridging the remaining targets.

For comparison, [Bhowmik–Grimmelt, arXiv:2607.27282v2, Proposition 8.1](https://arxiv.org/html/2607.27282v2#S8) gives an exceptional-zero formula after a power-size exceptional set is removed, with a remainder on the scale \(N(\delta\log N)^{c'}\) rather than the necessary minority lower scale. [Gou–Wang–Xu, arXiv:2611.18825v1](https://arxiv.org/abs/2611.18825), treats the integer problem under quantitative ratios assumptions and an unconditional analogue in function fields, not this integer exceptional branch. These are scope comparisons, not a priority claim.

[Bhowmik–Grimmelt, §8, Proposition 8.1](https://arxiv.org/html/2607.27282v2#S8) quantifies the connection between sparse Goldbach asymptotics and exclusion of exceptional zeros, using an exceptional set. It does not give the specific minority-scale lower bound on the hard stratum proved here. No claim is made about whether zeros satisfying (1) actually occur.
