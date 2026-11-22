# The native coefficient product in the two-high-label near-full score

Companion to [the exact high-cut calibration](Proof.md). Retain precisely its \(N,C_0>1,J_0,J,I,S,U,z,W,T_y,Q_y(m)\), writing \(C_0\) for the exponent previously called \(C\), so \(I=[N/S^{C_0},N/S]\). For a positive integer \(n\) put
\[
 H_U(n)=1_{n>1}\sum_{\substack{d\mid n\\d\le U}}\mu(d).
\]
Thus \(H_U(1)=0\) and \(H_U(n)=0\) for every \(1<n\le U\). The cutoff here really is \(\le U\), not \(<U\); the original \(Q_y(m)\) remains strict. The identities
\[
 \sum_{\substack{ag=A\\a>U}}\mu(a)=-H_U(A),\qquad
 \sum_{\substack{ck=C\\c>U}}\mu(c)=-H_U(C)
\]
are exact, including the \(A=1,C=1\) cases. Apply them **before** any raw-product restriction, directly to (1) of the high-cut proof. With \(x=A f,\ y=m C h=N-x\) this yields the all-even identity
\[
 C_I =
 \sum_{\substack{x\in NJ,\ C h\in I\\ (xy,N)=1,\ P^-(AC)>z\\
                        f,h>W,\ f,h\ {\rm prime}}}
      (\log f)(\log h)H_U(A)H_U(C)Q_y(m)+O_A(NL^{-A}).             \tag{1}
\]
Indeed on the two high-prime supports the raw roughness of \(a,g,c,k\) is equivalent to that of \(A,C\), and \(C h=r=y/m\) is the unchanged literal quotient gate. Nothing requires \(A\) or \(C\) to be squarefree or a product of any particular rank. The old high-cut raw-\(a,c\) deletion is not subtracted in deriving (1).

**Native critical deletion.** Fix \(B_0>0\). At every individual even \(N\) with \(\operatorname{rad}(N)\le L^{B_0}\) there is a fixed \(\delta>0\) for which the **entire native part** of (1) on
\[
                      A(m C)\ge N\exp(-L^\delta)                  \tag{2}
\]
is \(o(N)\). In particular all its actual true rows with \(f h\le N\exp(L^\delta/2)\) lie in this region, uniformly on the fixed central support. The surviving genuine \(f,h\) product is \(\gg_{J_0} N\exp(L^\delta)\). This does not price the surviving part, or imply that the signed smaller-\(f h\) subset alone is negligible with its own sharp gate (although the proof also allows independent dyads). The exact arithmetic deletion uses (2), not a changed \(Q_y\) score or the old raw predicate \(a(mc)\).

## 1. Literal geometry and the signed cofactor's character bound

From \(f,h>W\), each of \(A,mC\) is at most \(\sqrt N S^{C_0+10}\); (2) forces both into \([\sqrt N e^{-2L^\delta},\sqrt N e^{2L^\delta}]\) for large \(N\), for any fixed \(0<\delta<.01\). In particular \(m\le S^{C_0}\), and \(A,C\) each have polynomial length scale. The default divisor envelope uses \(|H_U(t)|\le\tau(t)\). Freeze the actual \(m\)-interval \(T_y\le m\le y S^{C_0}/N\) and \(d<T_y\) on the same relative \(y\)-mesh and smooth the central cutoff as in [the high-cut proof, §3](Proof.md). The same actual multiple counts cover all moved \(m,d\) boundaries. The remaining joint boundary in (2) is paid by a relative \(A\)-mesh of width \(L^{-F}\): on the crossing \(m C\) lies in a relative \(O(L^{-F})\) interval at the frozen threshold. As in that proof treat the two free high prime slots \(f,h\) as integers for this positive boundary, bounding their logs by \(L^2\). The base progression coefficients are \(A,mC\); the reciprocal estimates have the same fixed power margin when their coefficient norms accommodate fixed divisor powers. For the zero term the additional short harmonic is controlled by
\[
 \sum_{C\ {\rm in\ crossing\ strip}}\frac{\tau(C)}C
  \le \left(\sum_{C\ {\rm in\ a\ dyad}}\frac{\tau(C)^2}C\right)^{1/2}
       \left(\sum_{C\ {\rm in\ crossing\ strip}}\frac1C\right)^{1/2}
  \ll L^{O(1)}(L^{-F}+N^{-.49})^{1/2}.
\]
The other harmonics, label and mesh counts are log powers or subpower as in §3; make \(F\) large first. Smooth the \(mC\) cutoff after this freezing, paying true multiples of \(mC\mid y\) in its narrow strips or the same positive lattice comparison. This leaves independent left intervals, fixed \(m\)-gates, and separable smooth tests in \(x/N,mC\). Choose small fixed-ratio source factor packets wholly below \(N\) when they meet the smooth central support.

Here is a replacement for the long-\(\mu\) slot of that proof. On a polynomial-sized \(A\)-dyad at \(X\) in these ranges, the coefficient
\[
 H_U(A)1_{P^-(A)>z,\ (A,N)=1}\,1_{A\text{ avoids a prescribed union of banks}}
                                                                        \tag{3}
\]
has character sums \(O_E(X L^{-E})\) for every fixed \(E>0\). More precisely the bound is uniform in all characters modulo \(M=N d_{\rm arc}\), \(1\le d_{\rm arc}\le L^D\) for fixed \(D\), in such prescribed banks, and in every prefix of the dyad; fixed polylogarithmic archimedean twists follow by partial summation. We only use \(\operatorname{rad}(M)\le L^{B_0+D}\), no assumption on \(\varphi(M)\).

Open the true short divisor \(d\le U\) of \(A\) first: \(d\) is \(z\)-rough and avoids the banks automatically since their primes exceed \(U\). Both these constraints can be kept explicitly. For vertices in a reduced class, all excluded primes dividing \(M\) may be omitted from the remaining sieve alphabet (characters are zero at the nonunits). Open roughness and the prescribed avoidances on \(A/d\) by squarefree \(e\) from the union of primes \(\le z\) and the omitted banks. Thus every \(e\) is coprime to \(d\) and \(M\); the actual free integer is \(G=A/(d e)\). Use successive Bonferroni degrees near \(L^{.1}\); the Euler harmonic per degree is factorially small in the error and \(\max e,\#\{e\}\le\exp(O(L^{.3}))\). Bound the discarded tail in absolute by summing \(O(X/(de)+1)\) with \(\sum_{d\le U}1/d\ll\log U\) and the stated number of labels. This works against every character and every interval and pays all floor counts, since \(U=\exp(\ell^3)\) and \(X\) is polynomial. Any extra rational-arc periodic factor at an auxiliary modulus \(d_0\le L^{O(1)}\) can first be expanded on its unit group in the \(d_0\)-character basis at log-power cost: the actual \(A\) is \(z\)-rough, so every such \(d_0\) is automatically coprime to \(A\). Thus any additional characters have conductors dividing the full \(N d_{\rm arc}\) after increasing the allowed polylogarithmic arc factor. Extra unit masks are retained by omitting the primes of that modulus as described above. No non-smooth conductor is introduced by the sieve products.

For nonprincipal \(\chi\bmod M\), the smooth-modulus character estimate of the small-radical comparison applies on \(G\asymp X/(de)=N^{1/2-o(1)}\), with arbitrary prefixes. Explicitly its inducing conductor \(f_0\mid M\) has \(\operatorname{rad}(f_0)\ll L^{B_0+D}\). Split the imprimitive unit condition using the remaining prime divisors of \(\operatorname{rad}(M)\), of total product at most \(L^{B_0+D}\). After the imprimitive splitting, a primitive conductor below the square root of the actual free length is handled by complete periods. The other primitive terms use Iwaniec Lemma 6 on prefixes in fixed-ratio intervals with lower point exceeding \(\operatorname{rad}(f_0)^{100}\) and \(\log f_0/\log(X/(de))\) in a compact subset of \((0,\infty)\), as in the distinct-character Gram bound of [the small-radical major proof](../small_radical_projection/Proof.md). The defining ratio \(\log f_0/\log(X/(de))\) stays in a fixed compact range for the incomplete nontrivial case. Thus the bound is \(O((X/(de)) N^{-c})\) for some fixed \(c>0\), also after the harmless extra imprimitive sums and partial summation. Sum the \(d,e\) reciprocals, of log-power total, to get arbitrary-log saving. For the principal \(\chi\), unit counts on \(G\) give \(\varphi(M)/M\) density and at most a log-power floor since the radical is polylogarithmic. Its entire model factors the signed
\(\sum_{d\le U,\ P^-(d)>z,\ (d,M)=1}\mu(d)/d=O_E(L^{-E})\)
from the independent \(e\)-reciprocal sum: this is exactly the uniform rough harmonic of the high-cut proof at \(U\). These arguments keep the true reduced mean at every prefix. If clipping (3) at \(\tau(A)\le L^{M_0}\), the removed term in the character estimate costs \(X L^{-E}\) by positive divisor moments with \(M_0\) chosen large enough. Its physical omitted contribution has arbitrary-log saving by \(A\mid x\) and the \(x,y\) divisor envelope.

## 2. True first-success cancellation on the native factors

Use the same fixed separated bank families, with first-success event \(A_j(A)H_j(C)\) (left factor avoids entire family, right factor hits every color). Expand earlier failures into separable left/right masks as in [the high-cut proof, §4](Proof.md). Extract one actual label per color from \(C=u C'\), with the exact reciprocal hit allocation; remove squared bank-label incidences by actual \(q^2\mid y\) and divisor moments. All labels exceed \(U\), so the actual short divisor score on \(C\) equals that on \(C'\) exactly; both \(C,C'\) are much larger than \(U\), because \(C=N^{1/2-o(1)}\) and \(u=N^{o(1)}\). No \((-1)^K\) factor occurs for this short-divisor sum. Earlier bank events and the \(z\)-roughness of \(C'\) are retained, and all labels are target units.

On \(A f+u n=N,\ n=m C'h\), the left \(f\) is a genuine polynomial-sized prime and \(A\) is the exact clipped coefficient (3), avoiding the chosen bank. Both determinant endpoints are primitive by the same genuine prime-slot argument of §4. The uniform character bound just proved applies at every actual full projected major conductor, with the required bounded arc/archimedean factors, so replaces precisely the long signed slot in the exceptional-character step; restricted Bessel still uses the actual prime \(f\)-coefficient. The projected minor comparison needs only the literal prime endpoint, exact avoidance and polylog coefficient. The true residual \(n\ll N/Y\) on tag scales \(u\asymp Y\) has coefficient \(O(L^C\tau(n)^C)\), retaining \(H_U(C')Q_T(m)\), the genuine \(h\)-log-prime weight, its masks and all actual \(m\)-intervals. Thus its norm squared is \(O((N/Y)L^{O(1)})\). Smooth tests in \(m u C'\) separate by Mellin exactly as in §4 with allowed unit-modulus tag multipliers (JLL v2 Lemma 6.11). Cauchy and the projected minor and full major bounds give arbitrary prescribed log saving on this covered sum, after choosing its fixed precision and then the fixed color count. Log-scale packet, Boolean and smooth bounds are uniform for the provisionally restricted \(0<\delta<.01\).

## 3. Positive joint upper on the omitted true \(f,h\) rows

In the missed contribution bound \(|Q_y(m)|\le\tau(m)\), but retain the **already grouped** \(|H_U(A)H_U(C)|\). It is not valid to take the absolute value inside the divisor sums here. For fixed genuine \(m\le S^{C_0}\), use the exact two-prime positive upper flux of [the high-cut proof, §5](Proof.md) with base coefficients now \(A,m C\). In particular the universal upper sieve on \(f h\) is still at fixed tiny polynomial depth, and genuine prime log weights contribute \(L^2\). Splitting \(d\mid f h\) into \(d_f,d_h\) is the same signed gcd inclusion--exclusion; compatible shared labels divide \(N\) and the Poisson calculation uses target \(N/(d_f,d_h)\). The base products keep exact unit/coprime masks, the failure Boolean splits into independent \(A,C\) masks, and fixed divisor powers in the \(\ell^2\) norms cost only log powers. The spectral error stays power-small after summing the polynomial-sieve label counts and the subpower genuinely known \(m\)-count. At fixed outer \(A,mC\), after reassembling the sieve, the exact local model has roots \(1\) at primes dividing \(N A m C\) and \(2\) elsewhere, including \(1\) at 2. The nonnegative main bound for the prime log-lattice sum is \(N(\log L)^{O(1)}/(A m C)\). This follows from the two-log \(L^{-2}\) positive sieve and does not require an unsigned approximation of any actual pair. For the upper only, drop base compatibility after this positive main estimate.

At fixed \(m\), the two independent \(A,C\) harmonic ranges each have log width \(O(L^\delta)\) and lower point \(N^{1/2-o(1)}\). Exact integer Bonferroni and the same disjoint-family probabilities yield
\(\sum_{A,C}(1-\mathrm{cover})/(AC)\ll L^{2\delta-\kappa}+O_E(L^{-E})\)
for a fixed \(\kappa>0\) after selecting the color count. This remains an integer harmonic model, not a prime-independence claim. Separately, on either actual interval \(K\) of lower endpoint \(X_0=N^{1/2-o(1)}\),
\[
 \sum_{n\in K}\frac{|H_U(n)|^2}{n}
 \le \sum_{d,e\le U}\sum_{\substack{n\in K\\ [d,e]\mid n}}\frac1n
 \ll (1+\log(\sup K/\inf K))(\log(2U))^3+\frac{U^2}{X_0}.
\]
Indeed partial summation in each real multiple interval gives its length in the logarithmic measure divided by \([d,e]\) plus \(O(1/X_0)\). Writing \(d=g d_1,e=g e_1\) with \((d_1,e_1)=1\) and ignoring coprimality bounds the sum of \(1/[d,e]\) by \(\sum_{g\le U}g^{-1}(1+\log(U/g))^2\). Both claims are true harmonic bounds on the same separate intervals even though the original lattice rows were coupled.

Now Cauchy on the positive independent harmonic upper, preserving the actual failure indicator, gives
\[
 \sum_{A,C}\frac{|H_U(A)H_U(C)|(1-\mathrm{cover})}{A C}
          \ll (\log L)^C L^{2\delta-\kappa/2}+O_E(L^{-E}).
\]
The remaining genuine quotient weights sum with \(\sum_{m\le S^{C_0}}\tau(m)/m\ll(\log S)^2\). Consequently the whole missed contribution is
\(O(N(\log L)^{O(1)}L^{2\delta-\kappa/2})+o(N)=o(N)\)
after choosing \(\delta<\min(.01,\kappa/10)\), strictly **after** the fixed color count and resulting \(\kappa\). This includes all the grouped cofactor factorizations with \(A(m C)\) in (2); it would not follow from separately bounding each original \(a,g,c,k\) assignment. Covered cancellation and the actual boundary errors now prove (2), without a sign assertion beyond it.
