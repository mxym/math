# Mean Gaussian mass of random module kernels at arbitrary ideal moduli

Let \(K\) be a number field, \(R=\mathcal O_K\), and \(\mathfrak q\ne R\) a nonzero ideal. Put \(d=[K:\mathbb Q]\), \(\Delta=|\operatorname{disc}(K)|\), \(M=N\mathfrak q\), and \(n=dm\). Give \(K_{\mathbb R}\) its Euclidean Minkowski metric, so each complex place has weight two in the squared norm. Fix \(1\le r<m\). For an \(r\)-by-\(m\) matrix \(A\) over \(R/\mathfrak q\) write
\[
 L_A=\{\iota(x):x\in R^m,\ Ax=0\bmod\mathfrak q\},
 \qquad
 T_A(s)=\sum_{0\ne y\in L_A^*}\exp(-\pi s^2\|y\|^2).
\]
All duals below are Euclidean duals. Consider either independent uniform entries or that same law conditioned on surjectivity. Write \(V_A=|\operatorname{im}A|\).

**First-moment theorem.** For both ensembles, all number fields, all ideal moduli and all \(s>0\), the expected dual Gaussian mass has the positive-mixture expression in (3) below, and in particular
\[
 \mathbb E T_A(s)
 \le \Gamma(1+n/2)
       \left(\frac{3\Delta^{1/d}}{\sqrt{\pi d}}\right)^n
       \frac{\mathbb E V_A}{s^n}.                                      \tag{1}
\]
For fixed \(K,m,r\), any fixed \(0<\delta<1\), and \(M\to\infty\) along arbitrary ideal moduli, uniformly over \(0<s\le M^{(1-\delta)/d}\),
\[
 \mathbb E T_A(s)
   =\frac{\Delta^{m/2}\,\mathbb E V_A}{s^n}
      \left(1+O_{K,m,r,\delta}(M^{-r\delta/8})\right).                  \tag{2}
\]
For the surjective ensemble \(V_A=M^r\); for the unconditioned ensemble an exact local recursion for \(\mathbb E V_A\) is given in section 5. For example, at any fixed \(c>0\) and width \(s=c\,\Delta^{1/(2d)}M^{r/(dm)}\), the surjective mean tends to \(c^{-dm}\). This is a mean, not a statement that the random mass concentrates.

**Prior scope.** [Boudgoust–Lapiha, *Leftover Hash Lemma(s) Over Cyclotomic Rings*, §4.2, Lemma 27, Apr. 28, 2026 copy](https://opencryptology.org/2025/1080/versions/20260428T172000Z.pdf) bounds the mean of the same Gaussian invariant for uniform matrices at unramified rational prime moduli and explicitly leaves dropping the prime restriction to later work. Their Lemma 26 restates the earlier systematic-matrix theorem of [Lyubashevsky–Peikert–Regev, *A Toolkit for Ring-LWE Cryptography*, Theorem 7.4](https://web.eecs.umich.edu/~cpeikert/pubs/toolkit.pdf), which already allows composite integer moduli for a different matrix law. For code lifts at large prime-ideal level, comparison with a Siegel mean and higher moments is already established: see [Campello, §III](https://arxiv.org/abs/1702.00608) and [Gargava–Serban–Viazovska–Viglino, *Integral matrices of fixed rank over number fields*, Theorem 4](https://doi.org/10.1007/s40993-026-00792-5). The claims here are the exact finite-level positive mixture and the Gaussian first-moment estimate uniformly over arbitrary ideals, including a single fixed prime ideal raised to increasing powers, without an equidistribution statement. The bound is for a no-leakage theoretical hash and its Gaussian input. It does not assert a hardness reduction, security for a particular scheme, or a tight growing-degree bound.

## 1. Exact positive mixture

Let \(J=\mathfrak D_K^{-1}\) be the codifferent. Let \(j:K_{\mathbb R}\to\mathbb R^d\) be the Minkowski embedding with complex coordinate pairs conjugated; \(\iota(x)\cdot j(y)=\operatorname{Tr}_{K/\mathbb Q}(xy)\) on \(K\), and \(j\) differs from \(\iota\) by an isometry. Factor \(\mathfrak q=\prod_P P^{e_P}\), and put \(Q=N P\) at a given prime-ideal factor. The finite ring \(S=R/P^e\) is a chain ring of length \(e=e_P\) with residue field of size \(Q\). Multiplication identifies the local summand of \(\mathfrak q^{-1}J/J\) with a free \(S\)-module of rank one; this identification is noncanonical and replacing it multiplies by a unit. The trace pairing identifies \(\mathfrak q^{-1}J/J\) with the additive character group of \(R/\mathfrak q\).

Under \(j^{-1}\), the dual of \(L_A\) therefore contains \(J^m\) and is the preimage in \((\mathfrak q^{-1}J)^m\) of the image \(C_A\) of the transpose on the finite dual modules. Indeed a character of \((R/\mathfrak q)^m\) null on \(\ker A\) factors through \(\operatorname{im}A\), and a character of that image extends to the whole target finite group. This gives the asserted transpose image and \(|C_A|=V_A\).

The two ensembles have independent local matrices (including when conditioning on all local surjectivity). The law of each local \(C_A\subseteq S^m\) is invariant under \(\mathrm{GL}_m(S)\). A vector in \(S^m\) has **depth** \(k\) if its annihilator is \((\pi^k)\), \(0\le k\le e\), where \(\pi\) generates the maximal ideal. Depth zero is the zero vector. For \(k\ge1\), such vectors are \(\pi^{e-k}\) times primitive vectors, meaning vectors with at least one unit coordinate. They form one orbit: elementary invertible row operations send any primitive vector to the first coordinate vector. Thus \(w_k=\Pr(z\in C_A)\) only depends on its depth. Set \(w_0=1,w_{e+1}=0\). For \(1\le k<e\), multiplication by \(\pi\) sends a vector at depth \(k+1\) to one at depth \(k\), so \(w_k\ge w_{k+1}\).

Independently at each place choose a random exponent \(H_P\in\{0,\ldots,e_P\}\) with \(\Pr(H_P=h)=w_h-w_{h+1}\), and put \(B=N\mathfrak b\) where \(\mathfrak b=\prod_P P^{H_P}\). A finite vector lies in the image of \((\mathfrak b^{-1}J)^m\) exactly when its depth at each place is at most \(H_P\). Local probability multiplication gives, for any nonnegative test \(f\) on \(K_{\mathbb R}^m\),
\[
 \mathbb E_A \sum_{y\in L_A^*} f(y)
       =\mathbb E_{\mathfrak b}\sum_{y\in j((\mathfrak b^{-1}J)^m)} f(y).
                                                                        \tag{3}
\]
Both sides may be infinite for a general test, with equality by nonnegative summation. The finite group on the right, modulo \(J^m\), has \(B^m\) points, so
\[
 \mathbb E_{\mathfrak b} B^m=\mathbb E_A V_A.                              \tag{4}
\]
This counts distinct frequencies, including at primes where a uniformly sampled \(A\) has a kernel on the transpose side.

For the surjective ensemble \(C_A\) is a uniform free direct summand of rank \(r\). Transitivity and the number \(Q^{mk}-Q^{m(k-1)}\) of ambient depth-\(k\) vectors give
\[
 w_k=\frac{Q^{rk}-Q^{r(k-1)}}{Q^{mk}-Q^{m(k-1)}}
     =\frac{1-Q^{-r}}{1-Q^{-m}}\,Q^{-(m-r)k}\quad(1\le k\le e).            \tag{5}
\]
There is also a local monotone comparison for the unconditioned ensemble. Every image of an \(m\)-by-\(r\) matrix over a chain ring lies in a free rank-\(r\) summand, by diagonal Smith form. Given that image, choose uniformly among all such containing summands. The resulting summand is uniform since the rule and starting law are invariant and the action on the summands is transitive. Thus \(w_k\) for unconditioned matrices is at most (5), and the random \(B\) in (3) is stochastically no larger than its surjective counterpart. This also couples the two dual lattices by containment; no actual preimage is sought.

## 2. Reweighting the denominator

Write \(T_{\mathfrak b}(s)\) for the nonzero Gaussian mass of \(j((\mathfrak b^{-1}J)^m)\). Define the tilted law \(d\widetilde\mu/d\mu=B^m/\mathbb EV_A\), where \(\mu\) is the law of \(\mathfrak b\) in (3). The normalized identity is
\[
 \frac{s^n\,\mathbb E_A T_A(s)}{\mathbb E_A V_A}
     =\mathbb E_{\widetilde\mu}\,F_{\mathfrak b}(s),
 \qquad F_{\mathfrak b}(s)=\frac{s^n T_{\mathfrak b}(s)}{B^m}.            \tag{6}
\]
In the surjective ensemble (4) makes the tilted normalizer \(M^r\), and the tilted exponents remain independent. Put \(D_P=e_P-H_P\), and \(G=M/B=\prod_P Q^{D_P}\). Directly substituting (5) gives the exact tilted local tail
\[
 \Pr_{\widetilde\mu_{\rm sur}}(D_P\ge j)
      =\frac{1-Q^{-(m-r)}}{1-Q^{-m}}Q^{-rj}
      \quad(1\le j\le e_P).                                             \tag{7}
\]
For verification, put \(c=(1-Q^{-r})/(1-Q^{-m})\) and \(a=m-r\). The tilted local masses at \(0\), at \(0<j<e\), and at \(e\), respectively, are \(c\), \(c(1-Q^{-a})Q^{-rj}\), and \((1-cQ^{-a})Q^{-re}\). The identity \(1-cQ^{-a}=(1-Q^{-a})/(1-Q^{-m})\) gives (7).

In particular for \(0<t<r\) one has
\[
 \mathbb E_{\widetilde\mu_{\rm sur}} G^t
 \le\prod_{P\mid\mathfrak q}
       \left(1+\frac{Q^t-1}{Q^r- Q^t}\right).
                                                                        \tag{8}
\]
To see this, use
\(\mathbb E Q^{tD_P}
 = 1+(1-Q^{-t})\sum_{j=1}^e Q^{tj}\Pr(D_P\ge j)\)
and extend the geometric sum. The summand in each product factor is \(O_{r,t}(Q^{-(r-t)})\). For fixed \(K,r,t\) and any \(\xi>0\) the product is at most \(C_{K,r,t,\xi}M^\xi\): primes up to a fixed norm threshold contribute a fixed finite product; beyond it each factor is at most \(Q^\xi\), and \(\prod_{P\mid\mathfrak q} Q\le M\).

For the unconditioned ensemble, full row rank modulo all \(P\) implies surjectivity, and its probability is
\[
 p_{\rm sur}=\prod_{P\mid\mathfrak q}
               \prod_{j=m-r+1}^{m}(1-Q^{-j})
    \ \ge\ \prod_{j=m-r+1}^{m}\zeta_K(j)^{-1}>0.                         \tag{9}
\]
Here the convergence holds because \(m>r\) makes all \(j\ge2\). Multiplying \(B^m\mathbf 1_{B<M^{1-u}}\le M^{(1-u)t}B^{m-t}\) for \(0<u<1\) and using stochastic domination under the *untilted* laws gives
\[
 \Pr_{\widetilde\mu_{\rm iid}}(G>M^u)
 \le p_{\rm sur}^{-1}M^{-ut}\, \mathbb E_{\widetilde\mu_{\rm sur}} G^t.    \tag{10}
\]
Indeed \(m-t>0\), \(\mathbb E_{\mu_{\rm sur}}B^{m-t}
 =M^{r-t}\mathbb E_{\widetilde\mu_{\rm sur}}G^t\), and
\(\mathbb E_{\mu_{\rm iid}}B^m=\mathbb E V_A\ge p_{\rm sur}M^r\). This argument does not assume that stochastic domination survives the tilt. The same bound without \(p_{\rm sur}^{-1}\) for the surjective law follows from Markov's inequality applied to (8).

## 3. Geometry and the uniform error

For any fractional ideal \(I\), every nonzero \(v\in I\) satisfies \(|N_{K/\mathbb Q}v|\ge NI\), since the principal ideal \((v)\) is contained in \(I\). The weighted arithmetic-geometric mean inequality in the canonical norm gives
\(\|\iota(v)\|\ge\sqrt d\,(NI)^{1/d}\).
In a product of \(m\) ideal copies any nonzero vector has at least one nonzero component.

For a lattice of dimension \(n\) and minimum nonzero length \(\ell\), disjoint open balls of radius \(\ell/2\) give at most \((1+2R/\ell)^n\) lattice points in a ball of radius \(R\). For nonzero points this is at most \((3R/\ell)^n\) when \(R\ge\ell\), and there are none for smaller \(R\). Integrating this bound against \(2\pi s^2R\exp(-\pi s^2 R^2)\,dR\) gives
\(\Gamma(1+n/2)(3/(\sqrt\pi s\ell))^n\) for the nonzero Gaussian mass. Apply it with \(\ell\ge\sqrt d(\Delta B)^{-1/d}\) for \((\mathfrak b^{-1}J)^m\). Then \(F_{\mathfrak b}(s)\) in (6) is uniformly bounded by the constant in (1).

For an approximation where \(x=B^{1/d}/s\) is large, Poisson summation on \(j((\mathfrak b^{-1}J)^m)\) instead gives
\[
  F_{\mathfrak b}(s)
   =\Delta^{m/2}
     \left(1+\sum_{0\ne z\in\iota(\mathfrak b)^m} e^{-\pi\|z\|^2/s^2}\right)
       -x^{-n}.                                                         \tag{11}
\]
The determinant of the summed lattice before Poisson is
\(\Delta^{-m/2}B^{-m}\); its Euclidean dual is \(\iota(\mathfrak b)^m\). In particular every nonzero point in this latter lattice has norm at least \(\sqrt d\,B^{1/d}\). When \(x\ge1\), split the exponent in half at that minimum and use the previous ball bound on the remaining Gaussian. The nonzero sum in (11) is at most
\[
 \exp(-\pi d x^2/2)\,
 \Gamma(1+n/2)
       \left(\frac{3\sqrt2}{\sqrt{\pi d}\,x}\right)^n .
\]
This is uniform in the shape and ideal class of \(\mathfrak b\).

For \(s\le M^{(1-\delta)/d}\), use the event \(G\le M^{\delta/2}\). On it \(x\ge M^{\delta/(2d)}\), so (11) differs from \(\Delta^{m/2}\) by \(O_{K,m}(M^{-m\delta/2})\). Off the event use the uniform bound on \(F_{\mathfrak b}\), and (8)–(10) with \(t=r/2,\ \xi=r\delta/8,\ u=\delta/2\). Its probability is \(O_{K,m,r,\delta}(M^{-r\delta/8})\) in both ensembles. This proves (2), including the claimed uniformity over widths and moduli.

## 4. No-leakage hash regularity as a consequence

Let \(L_0=\iota(R)^m\), \(T_0(s)\) its nonzero dual Gaussian mass, and \(X\) sampled proportionally to \(\exp(-\pi\|x-c\|^2/s^2)\) on \(L_0\) for any fixed center \(c\). Fix \(A\). Every reachable output labels a coset of \(L_A\). Poisson summation of the coset mass and of the source normalizer gives, with \(x_y\in L_0\) any member of the output coset,
\[
 \frac{\Pr(AX=y\mid A)}{1/V_A}
  =\frac{\sum_{v\in L_A^*} e^{-\pi s^2\|v\|^2} e^{2\pi i v\cdot(x_y-c)}}
         {\sum_{v\in L_0^*} e^{-\pi s^2\|v\|^2} e^{-2\pi i v\cdot c}} .
\]
The terms in \(L_0^*\) cancel when subtracting 1, since \(x_y\in L_0\). If \(T_0(s)<1\), the joint TV to the same public \(A\) followed by uniform on its image is consequently at most
\[
 \frac{\mathbb ET_A(s)-T_0(s)}{2(1-T_0(s))}.
\]
For full-codomain uniform instead, the information-theoretic support deficit \(\mathbb E[1-V_A/M^r]\) is a lower bound, and adding the displayed estimate to that lower bound is an upper bound. This follows from support and the triangle inequality, including for non-surjective seeds. For surjective \(A\) the support deficit vanishes. The resulting positive regularity estimates are uniform in the Gaussian center and use no leakage model. By Markov, the same first moment also bounds \(\Pr(\eta_\varepsilon(L_A)>s)\le\min(1,\mathbb ET_A(s)/\varepsilon)\) for the usual smoothing threshold and \(\varepsilon>0\). A first moment alone need not give a matching lower tail or a sharp typical smoothing threshold.

## 5. Exact finite image-size factor for unconditioned seeds

For a local length-\(e\) ring of residue cardinality \(Q\), put \(b_{m,r}(e)=Q^{-er}\mathbb E|\operatorname{im}A|\) under the uniform matrix law. If \(p_{m,r,Q}(j)\) is the rank-\(j\) probability of a uniform \(m\)-by-\(r\) matrix over \(\mathbb F_Q\), then
\[
 b_{m,r}(0)=b_{m,0}(e)=1,\qquad
 b_{m,r}(e)=\sum_{j=0}^r p_{m,r,Q}(j)Q^{-(r-j)}
                          b_{m-j,r-j}(e-1).                            \tag{12}
\]
After conditioning on the entire first digit, fixed invertible changes of coordinates put it in block form with an identity and a zero block. The lifted top block is invertible. Block elimination leaves a bottom block divisible by the uniformizer; conditioned on the other blocks, it is uniform there because the original bottom block is uniform and elimination only translates it. The additive identification \(\pi S_e\simeq S_{e-1}\) intertwines scalar multiplication through the quotient. Thus the image size is \(Q^{ej}\) times the image size from the shorter ring of dimensions \(m-j,r-j\), proving (12). The rank probability is explicit:
\[
 p_{m,r,Q}(j)=Q^{-mr}\prod_{i=0}^{j-1}
                      \frac{(Q^m-Q^i)(Q^r-Q^i)}{Q^j-Q^i}.
\]
It counts full-rank factorizations modulo basis changes in the middle rank-\(j\) space. Independence of local factors yields \(\mathbb EV_A/M^r=\prod_{P\mid\mathfrak q} b_{m,r}(e_P)\), using the corresponding \(Q\) at each place.

The same recursion computes every unconditioned mixture weight without summing over matrices. Let \(c_{m,r,e}(k)\) be the expected number of elements of \(C_A\) annihilated by \(\pi^k\), for \(0\le k\le e\). With boundary \(c_{m,r,e}(0)=c_{m,0,e}(k)=1\), the block argument gives
\[
 c_{m,r,e}(k)=\sum_{j=0}^r p_{m,r,Q}(j)Q^{jk}
                    c_{m-j,r-j,e-1}(\min(k,e-1))
 \quad(k\ge1).
\]
Indeed the top free block contributes \(Q^{jk}\) and the rest is the shorter image. Subtract at adjacent \(k\) and divide by \(Q^{mk}-Q^{m(k-1)}\) to obtain \(w_k\) in section 1. At \(k=e\) this gives the same image-size moment as (12).

**Replay.** Run `python3 verify-composite-ideal-kernel-theta.py`. The exact checks enumerate small synthetic matrices, including ramified and mixed ideal levels, check the depth laws, finite image-size recursion, and pointwise mixture equality, and then illustrate the Gaussian first moment at growing integer moduli. The proof does not rely on the numerical illustrations.
