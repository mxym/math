# The actual long-prime-modulus covariance after bilateral rough conditioning

Rough conditioning the two prime legs does reduce their unsigned diagonal. But it also reduces the genuine negative alias correction, by substantially more, and the reflected odd norm then equals its **literal physical** odd norm at arbitrary-log accuracy. This gives a fixed-target obstruction to a specific preconditioning strategy for the sign in [LongPrimeModulusGoldbachCovariance.md](https://github.com/mxym/math/commit/b73b2635). All three prime variables below are genuine. It is not a bound in the sign direction necessary to prove Goldbach.

## 1. Statement

Let \(N\to\infty\) run through even integers; write \(L=\log N\), \(T=\log L\). Fix \(B>1\), \(K>1\), and take
\[
 Q=N/L^B,\qquad H=2L^B,\qquad z=\exp(L/T^K),\qquad
 \rho_y(N)=\prod_{p\le y,\ p\nmid N}\left(1-\frac1{p-1}\right),\quad
 \kappa_N=\left(\frac{\rho_z(N)}{\rho_H(N)}\right)^2.
\]
Prime products are over primes. Fix a nonnegative nonzero \(w\in C_c^\infty(0,1)\), symmetric around \(1/2\) and nonincreasing away from its center, and nonnegative nonzero \(g\in C_c^\infty(1,2)\). Write
\[
 f(v)=\int w(t)w(t-v)\,dt,\quad f(0)=\int w^2>0,
 \quad a^{(z)}_p=(\log p)w(p/N)\mathbf1_{P^-(N-p)>z},\quad A_z=\sum_p a^{(z)}_p,
 \quad \Delta_z=\sum_p(a^{(z)}_p)^2 .
\]
Here \(P^-(1)=\infty\); the support is bounded away from both endpoints. For each modulus prime \(q\) in \(g(q/Q)\), put \(W_q=(\log q)g(q/Q)\), \(G_Q=\sum_{q\ {\rm prime}}W_q\), and denote the normalized modulus mean by \(\langle F\rangle_Q=G_Q^{-1}\sum W_q F\). Define 
\[
 A_{q,z}(a)=\sum_{p\equiv a(q)}a^{(z)}_p,\quad E_{q,z}(0)=0,\quad
 E_{q,z}(a)=A_{q,z}(a)-A_z/(q-1)\ (a\ne0),
\]
\[
 V_{q,z}=\sum_a E_{q,z}(a)^2,\qquad
 \Gamma_{q,z}(N)=\sum_a E_{q,z}(a)E_{q,z}(N-a).
\]
Let \(R_w(N)\) be the actual ordered central prime-pair log weight without the rough cut. The cut leaves that weight exactly unchanged for all large \(N\), since if \(p+p'=N\) and both weights are nonzero then \(p,p'>z\).

Uniformly in the prescribed target, there is a **positive actual** debit \(D_N=\Delta_z-\langle V_{q,z}\rangle_Q\), for which
\[
 \begin{split}
  D_N&\asymp_{w,g,B,K}N\mathfrak S(N)\kappa_N,
     &\kappa_N&\asymp_B\frac{T^{2K+2}}{L^2},\\
  \langle V_{q,z}\rangle_Q&=\Delta_z-D_N,\qquad
  \langle\Gamma_{q,z}(N)\rangle_Q&=R_w(N)-D_N+O_A(NL^{-A}),\
  \Delta_z&=(1+o(1))e^{-\gamma}N\mathfrak S(N)T^K\int w^2.     \tag{1}
 \end{split}
\]
The inverse-log error holds for every fixed \(A>0\), with \(B,K,w,g,A\) fixed before \(N\) grows. In particular, with \(E^-_{q,z}(a)=(E_{q,z}(a)-E_{q,z}(N-a))/2\),
\[
      \left\langle\sum_a E^-_{q,z}(a)^2\right\rangle_Q
        =\tfrac12(\Delta_z-R_w(N))+O_A(NL^{-A}).               \tag{2}
\]
At a bad even target the odd norm is still the physical half-diagonal, to arbitrary-log accuracy. The strict negative gap in \(\langle\Gamma\rangle_Q\), relative to the diagonal, has shrunk to \(\asymp T^{K+2}/L^2\). Without conditioning the relative gap of the long-prime-modulus comparison is \(\asymp \mathfrak S(N)/L\) at a hypothetical bad target. Thus the chosen genuine rough filter worsens the relative sign requirement, even though it greatly reduces the ordinary variance.

## 2. Genuine rough-prime progressions and the ternary aliases

The small-modulus prime model for \(a^{(z)}_p\) is available with arbitrary log reserve here. Fix any logarithmic size \(r\le L^C\). For a unit residue \(a\) modulo \(r\) to be admissible require also \(a\not\equiv N\pmod \ell\) for every prime \(\ell\mid r\) (automatic if \(\ell\mid N\)). Nonunits or inadmissible classes are empty on the support for large \(N\): primes on this support exceed \(r\), and \(N-p\) must avoid every prime \(\ell\mid r\le z\). For an admissible residue, sieve the remaining primes \(\ell\le z,\ \ell\nmid rN\) on the linear difference \(N-p\). The local density relative to the prime progression is \(1/(\ell-1)\). The prime condition at any \(\ell\mid N\) is automatic, since an exceptional prime equal to \(\ell\le z\) is outside the support.

Use adjacent even/odd Bonferroni truncations of rank \(J\asymp_{A,C}T\) with a large enough constant. Indeed \(\sum_{\ell\le z}1/(\ell-1)\ll T\), and \((C_1T)^J/J!\) beats any prescribed inverse-log power with this choice. Each progression in the truncated expansions has modulus \(rd\) with \((r,d)=1\) and \(rd\le L^C z^J=N^{o(1)}\) since \(K>1\). For fixed \(r\), each modulus is indexed at most once per truncation; the progression class is reduced, using \((d,N)=1\). The maximal Bombieri–Vinogradov theorem therefore pays their errors with arbitrary log reserve, uniformly in the residue and in all prefixes on the fixed support. Apply partial summation to the bounded smooth test or \(w(t/N)e(\beta t)\) with \(|\beta|\le L^C/N\), absorbing the log variation by the initial reserve. For the latter test the answer is
\[
  \frac{\rho_z(N)}{\varphi(r)}\prod_{\ell\mid r,\ell\nmid N}
             \left(1-\frac{1}{\ell-1}\right)^{-1}V(\beta)
       +O_{A,C}(NL^{-A}),\quad V(\beta)=\int w(t/N)e(\beta t)\,dt.       \tag{3}
\]
The same argument with a different fixed smooth weight gives \(A_z=N\rho_z\int w+O_A(NL^{-A})\) and \(\Delta_z=(1+o(1))NL\rho_z\int w^2\), using \(\log p=L+O_w(1)\). Mertens and the convergent Goldbach tail give \(\rho_z=(1+o(1))e^{-\gamma}\mathfrak S(N)/\log z\), uniformly: for the target-dependent tail use \(\sum_{p\mid N,\ p>z}1/p\le L/(z\log z)\). This proves the last line of (1).

For each \(0<|h|\le L^B\), let \(T_h^+\) and \(T_h^-\) be the true weighted counts of
\[
 p+p'-h q=N,\qquad p-p'-h q=0,
\]
respectively, in \(a^{(z)}_p a^{(z)}_{p'}W_q\). Both have the uniform estimate
\[
 T_h^\pm=NQ\,\mathfrak A_z^\pm(N,h)\int_0^\infty g(u) f(huQ/N)\,du
                   +O_A(NQ L^{-A}).                            \tag{4}
\]
The two archimedean convolutions agree because \(w(1-t)=w(t)\). Here are details of the analytic passage. Write \(S_z(\alpha)=\sum a^{(z)}_p e(\alpha p)\) and \(U(\alpha)=\sum W_q e(\alpha q)\). The integrands are \(S_z(\alpha)S_z(\pm\alpha)U(-h\alpha)\) with the respective target phase. On the minor region **use the supremum of the unconditioned genuine modulus sum** \(U\), not one of the rough prime sums. For a chosen large exponent \(C\), if \(-h\alpha\) belongs to a \(Q\)-scale major arc of denominator \(r\le L^C\) and radius \(2L^C/Q\), then \(\alpha\) lies within \(2L^C/(Q|h|)\) of a rational of denominator at most \(|h|r\), by lifting the integer part and reducing. All such arcs fit in a union for \(\alpha\) of denominators \(\le L^{C+B+2}\) and radii \(L^{C+B+2}/N\). On its complement Vinogradov–Vaughan at scale \(Q\) gives \(U(-h\alpha)\ll_A Q L^{-A}\) by taking \(C\) large; see [Bhowmik–Grimmelt, Proposition 4.1](https://arxiv.org/html/2607.27282v2#S4.SS3). Parseval \(\int |S_z|^2\ll NL\) pays the entire minor integral. On the enlarged log-major arcs use (3) for each rough source and Siegel–Walfisz for the modulus sum; since \(|h|Q\le N\), all phase variation losses are fixed log powers. The product of the prime-size main bounds times the arc lengths and the arbitrary log errors leaves \(O_A(NQ L^{-A})\).

For the singular series at a prime \(\ell\le z\), the normalized one-leg residues are uniform on
\[
     A_\ell=\mathbb F_\ell\setminus\{0,N\bmod\ell\},\qquad k_\ell=|A_\ell|,
     \qquad r_\ell=k_\ell/(\ell-1).
\]
The physical mass of these residues among units is \(r_\ell\). For \(\ell>z\) the model is uniform on units, with \(r_\ell=1\). Non-squarefree conductors in the character expansion give no reduced additive Fourier contribution from these one-leg models, since the distributions lift uniformly from the squarefree kernel. At each prime the local normalized factor is the weighted fraction (times \(\ell\)) satisfying the appropriate affine equation, with two independent summand residues and one independent unit modulus residue. Its product, times the physical \(\rho_z^2=\prod r_\ell^2\), equals \(\mathfrak A_z^\pm(N,h)\). For completeness the normalized local nonconstant Fourier term is \(O(\ell^{-2})\) for \(\ell\nmid h,\ \ell\ge5\), and \(O(\ell^{-1})\) for \(\ell\mid h\): each summand coefficient at a nonzero frequency is at most \(2/(\ell-2)\), the modulus coefficient is the Ramanujan factor \(c_\ell(h)/(\ell-1)\), and there are \(\ell-1\) frequencies. The primes 2, 3 cost fixed constants. Rankin at exponent \(1/2\) then bounds the series tail beyond the major denominator cutoff by a negative power of that cutoff times \(\tau(|h|)^{O(1)}\). The factor \(\rho_z^2\le1\) causes no loss. This gives arbitrary log reserve by enlarging the arc exponent first. Rapid decay of the smooth \(V\) extends the Archimedean integral to the full real line. Ordinary Fourier inversion gives (4), with each sign of \(h\) retained. No ternary result with polynomial modulus variable or polynomial roughness has been assumed.

## 3. Literal local factors and the shrunk endpoint

For \(\ell\le z\), the sets \(A_\ell\) are invariant under \(a\mapsto N-a\). If \(\ell\mid h\), either ternary equation has exactly \(k_\ell\) admissible summand pairs and an arbitrary unit modulus residue. If \(\ell\nmid h\), exactly the \(k_\ell\) summand pairs that solve the target equation would force the modulus residue to zero; every other pair gives a unique unit modulus residue. Thus the **unnormalized** local factors, including \(r_\ell^2\), are identical for the sum and the difference, namely
\[
  s_\ell=\frac{\ell k_\ell}{(\ell-1)^2}\quad(\ell\mid h),
  \qquad d_\ell=\frac{\ell k_\ell(k_\ell-1)}{(\ell-1)^3}\quad(\ell\nmid h).       \tag{5}
\]
The first is the ordinary binary Goldbach factor, including 2. At 2, and additionally at 3 if \(3\nmid N\), \(k_\ell=1\) and \(d_\ell=0\). Hence admissible nonzero aliases require \(m_0\mid h\), where \(m_0=2\) or \(6\) is the product of the zero-factor primes. At \(\ell>z>H\), every considered \(h\ne0\) has \(\ell\nmid h\); the local factors are the unconditioned ternary ones, which are \(1+O(\ell^{-2})\) for either sign. Consequently the actual *offzero* major factors for the two signs agree up to a multiplicative \(1+O(1/z)\) wherever nonzero, and are zero on the same set.

Freeze all primes \(\ell>H\) in their common-in-\(h\), nondividing branch. Denote their product in the sum case by \(D_{>H}\) (the difference is identical up to \(1+O(1/z)\)). By (5), for \(H<\ell\le z\),
\[
  \frac{d_\ell}{r_\ell^2}=\frac{\ell(k_\ell-1)}{(\ell-1)k_\ell}=1+O(\ell^{-2});
  \qquad D_{>H}=\kappa_N(1+O(1/H)).                              \tag{6}
\]
The formulas at primes \(>z\) give the same asserted error after multiplication. Write \(s_0=\prod_{\ell\mid m_0}s_\ell\), \(C_H=s_0 D_{>H}\prod_{\ell\le H,\ell\nmid m_0}d_\ell\), and let \(\lambda_H\) be multiplicative, supported on squarefree divisors of \(\prod_{\ell\le H,\ell\nmid m_0}\ell\), with
\[
 \lambda_H(\ell)=s_\ell/d_\ell-1\ \ge0.
\]
For \(0<|h|\le L^B\) the literal modeled local product is \(C_H\mathbf1_{m_0\mid h}\sum_{d\mid h}\lambda_H(d)\). Two exact Euler identities are
\[
  \mathcal P_H:=\frac{C_H}{m_0}\sum_d\frac{\lambda_H(d)}d=D_{>H}\rho_H^2,
  \qquad
  \mathcal E_H:=C_H\sum_d\lambda_H(d)=D_{>H}\mathfrak S_H(N),   \tag{7}
\]
where \(\mathfrak S_H\) is the binary product truncated at \(H\). The first follows from \((1-1/\ell)d_\ell+s_\ell/\ell=r_\ell^2\), including the forced primes with \(d_\ell=0\); the second from \(d_\ell(1+\lambda_H(\ell))=s_\ell\). Uniformly \(\mathfrak S_H(N)\sim\mathfrak S(N)\), since the large target-divisor tail is at most \(L/(H\log H)=o(1)\); likewise \(\rho_H\sim e^{-\gamma}\mathfrak S(N)/\log H\). Mertens in the ratio in (6), with this same large target-divisor bound, gives \(\kappa_N\asymp(\log H/\log z)^2\). Also \(\rho_H^2/\mathfrak S_H=o(1)\) since \(\mathfrak S(N)\ll \log L\). These elementary estimates use \(B>1\).

Because \(w\) is symmetric unimodal, its autocorrelation \(f\) is even and nonincreasing on \([0,\infty)\): use layer-cake, where every level set in each convolution factor is an interval with the same center before translation. For \(t>0\) put
\[
  \delta_f(t)=\sum_{k\ne0}f(kt)-t^{-1}\int_{\mathbb R}f,
       \qquad -f(0)\le\delta_f(t)\le0,
       \qquad \delta_f(t)\longrightarrow-f(0)\ \ (t\to0).      \tag{8}
\]
The upper bound is the right-endpoint Riemann inequality on \(\mathbb R_{>0}\); the lower bound follows from Poisson since \(\widehat f=|\widehat w|^2\ge0\); the limit follows from smooth rapid decay in the Poisson sum. Let \(v=uQ/N\). Open the divisor sum in (7) and sum over nonzero positive and negative \(h\); the compact support kills all \(|h|>L^B\) for \(u\in(1,2)\). This gives the exact model formula
\[
 \sum_{h\ne0}\mathfrak A_z^+(N,h) f(hv)
      =\frac{\mathcal P_H}{v}(\int w)^2
        +C_H\sum_d \lambda_H(d)\,\delta_f(m_0d v).             \tag{9}
\]
Here the extension of the finite \(H\)-local model to larger \(h\) is only a formal convenience on terms with weight zero.

The last term of (9) is bounded between two strictly negative constant multiples of \(\mathcal E_H\), uniformly. Its magnitude is at most \(f(0)\mathcal E_H\) by (8). For a lower magnitude, with probability proportional to \(\lambda_H(d)\), prime inclusions are independent with probability \(\lambda_H(\ell)/(1+\lambda_H(\ell))=(\ell-k_\ell)/(\ell-1)\le2/(\ell-1)\). For a small fixed \(\epsilon>0\), the probability of no selected prime in \((H^\epsilon,H]\) is \(\gg_\epsilon1\), by Mertens and positivity of the finite local exclusion probabilities. Conditional on this event the remaining prime inclusions are unchanged and their expected log product is \(\ll \epsilon\log H\) by the Chebyshev sum \(\sum_{\ell\le y}(\log\ell)/\ell\ll\log y\). Choose \(\epsilon\) so small that Markov gives conditional probability at least one half of \(d\le H^{1/2}\). There \(m_0d v\to0\) uniformly in \(u\in[1,2]\), so \(\delta_f\le-f(0)/2\) for large \(N\). This proves the strict scale assertion. The discrepancy between the first term of (9) and \(\rho_z^2 v^{-1}(\int w)^2\) is \(O(\rho_z^2)\), since \(v^{-1}\ll H\) and (6) holds. It is \(o(\mathcal E_H)\) by \(\rho_H^2/\mathfrak S_H=o(1)\), so it cannot erase the sign. This explains the actual transition from a full singular-series deficit to one multiplied by \(\kappa_N\).

## 4. Actual centering and the odd leg

Let \(C^+_{q,z}\) and \(C^-_{q,z}\) be the weighted modular pair counts with \(p+p'\equiv N\pmod q\) and \(p-p'\equiv0\pmod q\). Opening the integer aliases is exact. Their zero-alias contributions are respectively \(R_w(N)\) and \(\Delta_z\) identically for every \(q\). Sum (4) over \(0<|h|\le L^B\) with the log reserves increased by \(B\). By (5), and the relative \(1+O(1/z)\) tail comparison, their **full true nonzero** alias totals agree to \(O_A(NQ L^{-A})\). To see that the multiplicative tail error has room, (9) bounds the positive modeled alias mass by \(O(N^2\rho_z^2+NQ\mathcal E_H)\); multiplication by \(1/z\) beats all log powers relative to \(NQ\). They both have in (9) the same correction to their common principal, a strict negative \(\asymp NQ\mathcal E_H\) after integrating \(g\).

All modulus primes are below the summand support at large \(N\), hence the zero class contains none. In the difference case, \(V_{q,z}=C^-_{q,z}-A_z^2/(q-1)\) exactly. In the sum case, \(C^+_{q,z}-v_N(q)A_z^2=\Gamma_{q,z}-2A_z E_{q,z}(N\bmod q)\mathbf1_{q\nmid N}/(q-1)\), with \(v_N(q)=(q-\nu_q(N))/(q-1)^2\). Both principal terms have modulus average
\[
  \frac{N^2\rho_z^2(\int w)^2}{G_Q}\int_0^\infty g(u)\frac{du}{u}
           +O_A(NL^{-A}),                                      \tag{10}
\]
using (3) at modulus one, PNT in \(q\), and \(v_N(q),1/(q-1)=1/q+O(q^{-2})\). The linear term in the sum is \(O_B(L^{2B+1})\) per modulus by counting integers in a literal class. Both this and the \(q^{-2}\) error are \(O_A(NL^{-A})\). Division by \(G_Q\sim Q\int g\), (6)–(10), and \(\kappa_N\asymp T^{2K+2}/L^2\) prove (1). Taking half of the variance-minus-covariance identity proves (2); all odd comparison errors are absolute at the displayed log reserve.

## Scope and nearby techniques

This fixes one specific candidate improvement to the [actual unconditioned long-moduli test](https://github.com/mxym/math/commit/b73b2635): drop true p rows whose other summand has a small factor, then try to dominate surviving antisymmetry by the reduced variance while keeping the old full endpoint reserve. The true local and ternary computations show that reserve does **not** survive. The method uses the same classical complementary-divisor principle as [Harper, arXiv:2412.19644v1, §3](https://arxiv.org/html/2412.19644v1#S3), but genuine prime moduli and target-reflected sieve conditions give the actual coinciding sum/difference aliases above. Ordinary BDH on total variance alone does not give (1)–(2). Nothing here excludes other nonnegative/signed detectors or a much stronger genuinely prime-specific odd-sector bound. In particular we make no transfer to polynomial \(z=N^\eta\), nor claim that the sharp or smooth spectral criteria for true binary Goldbach are proved.
