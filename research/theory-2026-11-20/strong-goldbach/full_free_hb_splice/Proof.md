# Full free-branch subtraction in the marked shared-index Goldbach covariance

The [above-root calculation](https://github.com/mxym/math/commit/48786012bff7073486a373df69f35611a803e916) reduces a genuine marked, fixed-target Goldbach covariance to a covariance of actual rough Möbius scores. On that same geometry we now remove a branch of the exact score using three disjoint parts of a single free-factor cutoff. In particular the new remainder has **no squarefree semiprime contributions at all**. It still contains balanced triprimes and higher ranks. This does not bound the whole covariance and does not prove prime-pair existence.

Let \(N=2x\) be a prescribed even integer, \(Y=\sqrt{x}\), \(L=\log x\), \(\ell=\log L\), \(z=\exp(L/\ell^2)\), and \(R_z(y)=1_{P^-(y)>z}\). Use the literal shared-index box
\[
 d,e\in[.65Y,.8Y],\quad k\in[Y,1.1Y],\qquad(dek,N)=1,\qquad y=N-ek.
\]
The mark \(\beta(e)\) counts the genuine ordered pairs \(p_2p_3\mid e\) with prime bands \([x^{.029},x^{.031}]\), \([x^{.075},x^{.078}]\), respectively. The mark prime factors may also divide \(k\). The original rough score is
\[
 K(y)=R_z(y)\sum_{\substack{rs=y\\r>x^{.505}}}\mu(r)\log s .
\]

Set
\[
 T_1(s)=x^{.766}s^{-1/2},\qquad T_2(s)=x^{.918}/s,\qquad
 T_3(s)=x^{.674}s^{-1/4}.
\]
The **base** cutoff is \(T_0(s)=\min(T_1(s),T_2(s))\), with the junction at \(s=x^{.304}\). Define the wider cutoff \(T(s)=T_3(s)\) on \(x^{.13}\le s\le x^{.32}\), and \(T(s)=T_0(s)\) otherwise. Define the actual free score for either cutoff \(U_0(s)=T_0(s)\) or \(T(s)\) by
\[
 F_{U_0}(y)=-R_z(y)\!
     \sum_{\substack{s c a=y,\ ca>x^{.505}\\ a>U_0(s)}}\mu_2(c)\log s ,
 \qquad \mu_2=\mu*\mu .                                      \tag{1}
\]
The \(s=1\) term is identically zero. There is **no artificial upper cutoff on \(s\)**: \(s<y/x^{.505}\) is precisely the original moving bound. All divisors and log weights are literal.

**Uniform signed transfer.** For either score in (1), every \(B>0\) and fixed \(D\), and weights \(|u_{d,k}|\le L^D\tau(d)^D\tau(k)^D\tau(N-dk)^D\), one has
\[
 \sum_d\left|\sum_{e,k}\beta(e)u_{d,k}F_{U_0}(N-ek)\right|
       \ll_{B,D}x^{3/2}L^{-B}.                    \tag{2}
\]
In particular the actual quadratic expression \(\sum\beta(d)\beta(e)K(N-dk)K(N-ek)\) changes by \(O_B(x^{3/2}L^{-B})\) on replacing both \(K\)'s by \(K-F_{U_0}\).

**Exact consequences.** Both new remainders vanish on the original squarefree semiprime component. On every squarefree triprime each surviving divisor term is nonnegative. For every squarefree triprime all of whose genuine prime factors are \(\ge x^{.25}\), the new score is exactly \(2K(y)\), so this is not a sign-improving projection. On squarefree \(y\) with \(P^-(y)>x^{.157}\) for the base cutoff, or \(P^-(y)>x^{.187}\) for the wider cutoff, the new score has the exact nonnegative formula
\[
 K(y)-F_{U_0}(y)
   =2\sum_{\substack{rs=y,\ r>x^{.505}\\\Omega(r)\ {\rm even}}}\log s .
 \tag{3}
\]
This last statement is only pointwise arithmetic on the specified rough families, not a bound on uncut \(y\) or an extra signed cancellation theorem on just those families. Each sign-labelled absolute mass of the whole removal still has size \(\gg x^{3/2}\ell^4\varphi(N)/N\) against the established opposite genuine prime row, as proved in §4 below.

## 1. Exactly which original Möbius terms are being removed?

Use the fifth-power finite identity (3) of the [one-free proof](../long_free_mu2_row/Proof.md), with Möbius factors cut at \(U=x^{.24}\). In every physical branch here a free variable \(a>U_0(s)\) is unique: \(U_0(s)^2>r=y/s\), and \(r\le1.5x\). For \(T_1\) on its range \(s\le x^{.304}\) this follows from \(U_0(s)\ge x^{.614}\), and the complementary \(c\) has \(c<1.5x^{.234}/\sqrt s<U\). For \(T_3\), \(U_0(s)\ge x^{.594}\) and \(c<1.5x^{.326}s^{-3/4}\le1.5x^{.2285}<U\). For \(T_2\), the strict a-cut gives \(a s>x^{.918}\), so \(c<1.5x^{.082}<U\); also \(s<1.5x^{.495}\), and
\[
 T_2(s)^2/r=\frac{x^{1.836}}{sy}\gg x^{.341}.
\]
Thus the other truncations in each chosen free-variable term disappear *exactly*. Their remaining convolution is \(\mu_2(c)\), times \(\sum_{j=2}^5(-1)^{j-1}\binom5j(j-1)=-1\), as in the same proof. This includes nonsquarefree \(r\) and requires no pairwise coprimality of the free factors.

The signed base score splits into two literal disjoint pieces. On \(s\le x^{.304}\) use the first (one-free) proof, with this new additional sharp \(s\)-range inside its already allowed \(.389\) endpoint. Its original \(ca>x^{.505}\) test is automatic there. On \(s>x^{.304}\) use the two-free proof below, with the literal \(ca>x^{.505}\) condition. The wider score adds exactly one more disjoint band:
\[
 x^{.13}\le s\le x^{.32},\qquad T_3(s)<a\le\min(T_1(s),T_2(s)).
\]
The analytic estimate for that precise annulus is the [factored \(q\)-van der Corput appendix](../factored_hb_band/Proof.md). Its lower cutoff is smaller throughout: the differences of the exponents of \(T_1,T_2\) from \(T_3\) are respectively \(.092-v/4\) and \(.244-3v/4\) for \(v=\log_x s\), and both are at least \(.004\) here. The final, larger removed row is not a sum in which any \(a,s,c\)-label is counted twice.

For completeness, the appendix's per-\(k\) absolute-row estimate also suffices for precisely the polynomial-divisor envelope in (2). In each fixed \(k\) the modulus-\(k\) class \(N\bmod k\) is reduced and has interval length \(\asymp x\). Shiu's fixed divisor-moment bound there and the ordinary \(d\)-moment bound give
\(\sum_d|u_{d,k}|\ll YL^{C_D}\tau(k)^D\) by Cauchy. Also the absolute magnitude of the \(e\)-row of the appendix is \(O(YL^C)\) uniformly by Shiu, since \(\beta(e)\) is bounded on the fixed bands and \(B(y)\ll L\tau(y)^{O(1)}\). On \(\tau(k)\le L^{D'}\) the added multiplier is only a log power. On the complementary tail use the uniform \(e\)-row bound and the fixed higher moments of \(\tau(k)\) to obtain arbitrary log savings by increasing \(D'\). Pointwise Shiu is applied only to the actual reduced affine row, not to a modified target average. This proves (2) for the union once its two-free estimate is supplied.

## 2. Incomplete two-free hyperbolas, with the literal reduced-unit constant

For an integer \(A\ge2\), a unit \(b\bmod A\), and intervals \(I,J\) of real lengths \(M_1,M_2\), one has the uniform completed rectangle estimate
\[
 \#\{(m,n)\in(I\times J)\cap\mathbb Z^2: mn\equiv b\bmod A\}
 =\frac{\varphi(A)}{A^2} M_1M_2
   +O_\varepsilon\!\left(A^{1/2+\varepsilon}
                         +(M_1+M_2) A^{-1+\varepsilon}\right).
 \tag{4}
\]
The factor \(\varphi(A)/A^2\) is exact on complete periods and is not \(1/A\). To prove (4), split both integer intervals into full blocks of \(A\) consecutive integers and at most one residual interval of length \(<A\), ignoring an \(O(1)\) difference between real length and count. Each full-full block contributes \(\varphi(A)\), and a full-residual block contributes the number of units in the residual interval, \(\varphi(A)\#J_{\rm res}/A+O(\tau(A))\) by Möbius inclusion–exclusion. These errors and real-to-integer length replacement are covered by the last term of (4).

For residual-residual, complete both intervals on \(\mathbb Z/A\). With Fourier coefficients normalized by \(1/A\), each coefficient at nonzero \(h\), represented by \(0<|h|\le A/2\), is \(O(1/|h|)\). The complete kernel is the ordinary Kloosterman sum \(S(h,jb;A)\); at \(h=j=0\) it is \(\varphi(A)\), and otherwise the classical composite-modulus bound is \(O(\tau(A)A^{1/2}(h,j,A)^{1/2})\). For both frequencies nonzero, group their gcd by \(g\mid A\); the normalized Fourier product costs
\(\ll(\log(2A))^2\sum_{g\mid A}g^{1/2}g^{-2}\).
For only one nonzero frequency the kernel is a Ramanujan sum, of magnitude at most \(\sum_{g\mid(h,A)}g\); its weighted absolute sum is \(O(\tau(A)\log(2A))\). This proves (4) also for composite or squareful \(A\). Polynomial powers of logs are harmless in (4) by partial summation, including the physical \(\log s\) multiplier below.

## 3. Two-free signed transfer on the actual \(s>x^{.304}\) region

Use the exact slope opening (4) of the [one-free proof](../long_free_mu2_row/Proof.md): \(A=k p_2p_3\), \(I_k=[N-.8kY,N-.65kY]\), \(y\equiv N\bmod A\) and \((y,N)=1\). The modulus of (4) is this actual \(A\), whose size is \(x^{.604}\) to \(x^{.6092}\) up to harmless fixed constants. Do not remove the physical \((A,N)=1\) or \((c,A)=1\). Keep \((c,N)=1\). The \((as,N)=1\) restriction may be removed from the actual rough factors **before** any expansion, since every violation puts \(y\) among \(O(xL/z+L)\) integers divisible by a prime \(>z\) dividing \(N\). Divisor moments with \(y,N-y\) and the true opposite row weight pay the loss as in the [one-free proof](../long_free_mu2_row/Proof.md). This keeps the unit-on-\(A\) condition throughout but avoids a false separability requirement involving the full \(N\).

On this branch the original \(r>x^{.505}\) is exactly \(a>x^{.505}/c\). For fixed \(c,k\), the additional \(a s>x^{.918}\) has simply restricted the radial \(y\)-window to \(I_k\cap(c x^{.918},\infty)\). In particular
\[
 1\le c\le1.5x^{.082},\quad s>x^{.304},\quad
 s<1.5x^{.495},\quad a>x^{.423+o(1)} .
 \tag{5}
\]
Leave \(c\) fixed with its true \(\mu_2(c)R_z(c)\)-coefficient. Expand independent actual roughness factors \(R_z(a),R_z(s)\) by their two Bonferroni polynomials at \(J=\lceil C_B\ell\rceil\), with squarefree divisors \(\lambda_a,\lambda_s\le z^J=x^{o(1)}\). If either shares a prime with \(A\), that progression term is zero. The signed product error is justified by the telescoping
\[
 R_z(a)R_z(s)-P(a)P(s)
 =(R_z(a)-P(a))R_z(s)+P(a)(R_z(s)-P(s)).
\]
The bound \(|P(a)|\le\tau(a)\) and the factorial moments of \(\binom{\omega_{\le z}(y)}J\) from the [one-free proof](../long_free_mu2_row/Proof.md) pay this error globally with any fixed divisor envelope, via Hölder and \(N-y\) multiplicities.

After writing \(a=\lambda_a u,\ s=\lambda_s v\), both \(u\) and \(v\) are genuinely **free integers**. The exact congruence is
\[
 uv\equiv N\overline{c\lambda_a\lambda_s}\pmod A,\qquad
  (c\lambda_a\lambda_s,A)=1 ,
\]
in the stated product window. Relative \(L^{-J_0}\)-meshes on \(k,a,s\) give independent rectangles with polylogarithmic multiplicity, treating \(c\) as fixed. Only \(I_k\) boundary strips and \(y=c x^{.918}\) can be affected, plus the independent sharp \(a>x^{.505}/c\) endpoint. The former have \(O(xL^{-J_0}+Y)\) physical \((e,k)\)'s before multiplicities, as in the previous proof. For the product threshold, within fixed dyadic scales \(W,S,C\) with \(W S C\asymp x\), for each \(c,s\) there are \(O(W L^{-J_0}+1)\) admissible \(a\)'s in the relative strip; the same bound applies at the independent \(a\)-endpoint. Thus the unweighted affected \(c,s,a\) count is \(O(xL^{-J_0}+CS)\) per dyadic product box. All these bounds continue to yield any log saving after true divisor weights and multiplicities by Hölder over \(y,N-y\) and the extra free \(d\). For the principal the identical volume estimate with \(1/A\) weights is also log-small; any artificial interval endpoints are measured separately with no accumulated fixed-width loss. The sharp \(\log s\) factor is handled by partial summation in each retained rectangle. No Fourier coefficient carries hidden dependence of the \(s\) range on \(u\).

Applying (4) to the independent \(u,v\) rectangles, its first error summed over all actual moduli and \(c\)'s, then over the two subpower smooth-divisor lists, is
\[
 \ll x^{o(1)}x^{.082}Q^{3/2}
 \le x^{.9958+o(1)},\qquad Q\le x^{.6092}.
 \tag{6}
\]
It is legitimate to extend the sum to all \(A\asymp Q\) only **after** the coprime residue and the absolute error bound have been used. For each actual \(A\), the factorization multiplicity of \(k,p_2,p_3\), coefficient \(|\mu_2(c)|\), and pointwise divisor envelope add at most \(x^{o(1)}\) on this power-saving step; no additional positive power in the number of marks or in \(c\) is lost. The second error in (4), summed over \(A\), is \(x^{o(1)}(W+S)\) per \(c\)-box element. Since \(C(W+S)\ll x/S+x/W\) by the retained product scales, \(S\ge x^{.304-o(1)}\) and \(W\ge x^{.423-o(1)}\) yield a fixed power saving too. The variables \(u,v\) have respective lengths at most \(W,S\); this estimate is valid even when \(W>A\). Sum \(d\) at a further cost \(O(Y)\). Bin boundaries and Bonferroni errors were controlled with log-precision divisor moments, not a pointwise \(x^{o(1)}\) loss.

The true leading rectangle term is \(\varphi(A)/A^2\) times length in \(u,v\). Returning to \(s,a\), its factors \(1/\lambda_a,1/\lambda_s\) complete independently to
\[
 W_z(A)^2=\left(\prod_{\substack{p\le z\\p\nmid A}}(1-1/p)\right)^2 .
\]
This is the product over the \(A\)-unit support, not a replacement by \(\prod_{p\le z}(1-1/p)^2\) without local correction. The factorial tails are uniform. Restoring the exact windows and putting \(a=y/(cs)\), the resulting ordinary zero-frequency model is exactly
\[
 -\frac{\varphi(A)W_z(A)^2}{A^2}\int_{I_k}
     \int_{x^{.304}<s<y/x^{.505}}\frac{\log s}{s}\,
      \sum_{\substack{c<y/x^{.918}\\(c,AN)=1}}
            \frac{\mu_2(c)R_z(c)}{c}\,ds\,dy .
 \tag{7}
\]
The inner \(s\)-measure is now continuous; before the double-free completion it was an integer rough variable. The strict upper cutoff \(s<y/x^{.505}\) comes specifically from \(ca>x^{.505}\) and is retained; no \(s\le x^{.495}\) shortcut has been made. The factor \(dy/(cs)\) and \(c<y/x^{.918}\) are literal consequences of the change of variable and the new \(a s>x^{.918}\) condition. These two facts also explain why no interaction between \(c\) and the sifting level of \(s\) is silently omitted.

The \(c\)-endpoint in (7) is comparable to \(x^{.082}\). The same uniform masked \(\mu_2(c)/c\) sharp-prefix sum as in the [one-free proof, §4](../long_free_mu2_row/Proof.md) is \(O_B(L^{-B})\); it applies here with the exact \(AN\) mask. Indeed it follows from the finite rough harmonic \(\mu\) estimate and Dirichlet hyperbola and requires only polynomial endpoints. Thus (7) contributes \(O_B((x/A)L^{-B})\) before attaching the true opposite-row and mark weights. The harmonic \(A=k p_2p_3\) sum and the ordinary opposite divisor moments prove the announced log saving in (2).

## 4. Physical ranks and independent labelled mass

On any actual squarefree semiprime \(y=pq\) with \(p<q\), the only possible nonzero coefficient in \(K\) has \(s=p\), \(r=q>x^{.505}\). If this \(r\) fails the threshold, **both** \(K\) and (1) are already zero there; the reverse \(s=q,r=p\) is impossible since \(p<\sqrt{1.5x}<x^{.505}\). For the nonzero case \(a=q\) passes the base cutoff, as \(a s=y>x^{.918}\), and also passes the wider \(T\le T_0\). No smaller divisor \(a\) of the true prime \(r=q\) can pass. Thus \(F_{U_0}=K=-\log p\). Small prime factors \(\le z\) have both scores zero by the exact rough factor.

For any squarefree rough triprime, \(s>1\) makes \(r=y/s\) either prime or the product of two actual distinct primes. A prime \(r\) is canceled as above. For \(r=P_1P_2\), the \(a=r\) label always passes; because \(U_0(s)>\sqrt r\), at most the larger proper prime divisor \(a\) can also pass. In the latter case its complement is a prime and \(\mu_2(c)=-2\). Therefore the resulting \(r\)-coefficient of \(K-F_{U_0}\) is exactly \(2\) if there is no such additional \(a\), and \(0\) otherwise. This proves nonnegativity on **all** squarefree triprime rows, not only the central profile. If \(R_z(y)=0\) both expressions are zero.

For squarefree \(y\) with all prime factors \(>x^\delta\), and any nonzero \(s\) label in (1), \(s>x^\delta\). At the first cutoff the largest possible \(c\)-exponent is \(.234-\delta/2+o(1)\), at the two-free cutoff it is \(.082+o(1)\), and at the annulus-improved cutoff it is \(.326-3\delta/4+o(1)\). Consequently for the base \(\delta=.157\), and wider choice \(\delta=.187\), no divisor \(c>1\) can pass. The \(c=1,a=r\) label always passes the base cutoff (\(rs=y>x^{.918}\)) and hence also the wider one. Thus on every original \(r\) label the subtraction replaces \(\mu(r)\) by \(\mu(r)+1\). This proves (3) and the quadratic replacement follows from (2) and the fixed divisor envelopes. For a true triprime with all factor exponents at least .25, no singleton \(r\) can exceed .505, and the only nonzero \(s\)'s are singleton complements of admissible two-prime \(r\)'s. Thus \(\mu(r)=+1\) in every original contribution; (3) gives exactly \(2K\), even when the original moving cutoff excludes one singleton complement. No averaged independence is used.

Lastly both signs can be large against the real opposite prime row in either new score. Use the **two-free piece** at \(x^{.35}<s<x^{.38}\), common \(y\)-window \([1.22x,1.26x]\), and separately \(c=1\) (coefficient \(-1\)) and \(c=p\) genuine prime in \([x^{.01},x^{.02}]\) (coefficient \(+2\)). Each satisfies (5) and \(a s=y/c\gg x^{.98}>x^{.918}\), \(ca=y/s\gg x^{.62}>x^{.505}\). The factor \(\varphi(A)W_z(A)^2/A^2\) in (7) obeys
\[
 \frac{\varphi(A)}{A}W_z(A)^2
 =V_z^2\frac{\varphi(A)}{A}
    \prod_{\substack{p\le z\\p\mid A}}(1-1/p)^{-2}
 \ge (1-o(1))V_z^2,\qquad V_z=\prod_{p\le z}(1-1/p),
\]
since the large prime factors of \(A\) have total harmonic weight \(O(L/z)\). The true \(c\)-harmonic mass is bounded below by \(1\) or a positive fixed constant (reciprocal primes, deleting the finitely many divisors of \(AN\)). The positive \(s\)-integral is \(\asymp L^2\), and the \(y\)-interval length is \(\asymp x\). Applying the same positive transfer to these two subfamilies gives principal \(\gg(x/A)V_z^2 L^2\gg(x/A)\ell^4\) in each. The actual opposite prime row \(\sum_{d,k}\beta(d)\log(N-dk)1_{N-dk\ {\rm prime}}\gg x\varphi(N)/N\) on prescribed units is supplied by the earlier above-root proof (§3), with exact same mark geometry, and each \(k\) has \(\sum_{p_2,p_3}1/(kp_2p_3)\gg Y^{-1}\) on actual allowed tags. This proves the sign-labelled lower masses. It does not assert a pointwise sign on either full free score.

The proof combines a literal independent-factor completion with the one-free and factored-reciprocal estimates. The annulus was capped precisely to avoid double accounting: previously proved unbalanced-semiprime compensation on the **original** \(K\) row and any narrow Jain-type branch estimates cannot be credited to the new \(K-F_{U_0}\) without redoing their intersections. In particular the doubled balanced triprime score exhibits a real surviving obstacle. No new absolute upper or signed closure of that remaining covariance is claimed.
