# The optimal homogeneous product–join simplex recursion, with independent arities

**Research note, 7 October 2026.** Attribution: `mxym` (AI-assisted). This is a continuation of entry 005, versions 2 and 5, not a claim of priority or human peer review. All new finite comparisons below have an exact-arithmetic replay.

## Abstract

Let \(T_p\) be a \(p\)-simplex. From \(K_0=T_p\) recursively construct \(K_{j+1}=(K_j^m)^{*k}\), where superscripts denote Cartesian products and joins and \(m,k,p\) are independent positive integers. Write \(R(K)=|\Pi K|/|K|^{d-1}\) in dimension \(d\). We prove that \(\lim_j R(K_j)^{1/\dim K_j}\) has a **unique** maximum over **all** triples \((m,k,p)\) at \((2,2,5)\). Every other triple has logarithmic rate less than \(131/125=1.048\); the known winner has rate greater than \(14267/5000=2.8534>e^{131/125}\). The infinite-dimensional, infinite-arity exclusion uses elementary Stirling bounds, parameter monotonicity and four exact rational interval certificates; the finite rectangle has 6,155 excluded competitors. The lower construction is explicitly inherited from 005 v5.

## 1. Definitions and theorem

For a full-dimensional convex polytope \(K\subset\mathbb R^d\), let \(\Pi K\) be the projection body and let
\[
 R(K)=\frac{|\Pi K|}{|K|^{d-1}},\qquad g(d)=\frac{d^d}{d!}.
\]
The affine-invariant cone parameter \(a(K)\), defined from the lifted facet determinants in [005 v2](../../preprints/005-simplex-product-optimum/v2/paper.md), satisfies
\[
 a(T_p)=\frac1{p+1},\qquad R(T_p)=(p+1)g(p).
\]
Write \(K^m\) for the product of \(m\) copies of \(K\) and \(K^{*k}\) for the join of \(k\) copies. A one-fold product or join is the identity. Define
\[
 K_0=T_p,\quad K_{j+1}=(K_j^m)^{*k},\qquad
 \Lambda_{m,k,p}=\lim_{j\to\infty}R(K_j)^{1/\dim K_j}.
\]
For the constant sequence \(m=k=1\), this means the ordinary fixed-root value of \(T_p\).

**Theorem 1 (complete homogeneous-arity classification).** For every \(m,k,p\ge1\), the displayed limit exists, and
\[
 \boxed{\Lambda_{m,k,p}<e^{131/125}<\frac{14267}{5000}
 \quad\text{if }(m,k,p)\ne(2,2,5).}
\]
Moreover \(\Lambda_{2,2,5}>14267/5000\). Thus \((m,k,p)=(2,2,5)\) is the unique global maximizer among all homogeneous simplex-seeded product–join recursions, including unequal product and join arities.

**Dependencies and limits.** The exact affine product/join calculus and the lower bound for the \((2,2,5)\) orbit are inherited from [005 v2](../../preprints/005-simplex-product-optimum/v2/paper.md) and [005 v5](../../preprints/005-simplex-product-optimum/v5/paper.md); they are not claimed as new. The classification here is stronger than v5 because \(m\) and \(k\) can differ and may equal 1. It does **not** classify heterogeneous/periodically varying trees or the entire product–join closure, much less all convex bodies.

## 2. Exact dynamical identities

We recall, and apply, the following 005 v2 identities. For any \(K\) of dimension \(d\),
\[
 R(K^m)=R(K)^m,\quad a(K^m)=a(K),\quad \dim(K^m)=md.
\]
For the \(k\)-fold join of a body \(P\) of dimension \(s\), the exact join identity gives
\[
 R(P^{*k})=\frac{k}{a(P)}\,g(ks+k-1)
 \left(\frac{a(P)R(P)}{g(s)}\right)^k,
 \qquad a(P^{*k})=\frac{a(P)}k.
\]
Consequently, when \(m,k\ge2\), put
\[
 T=mk,\qquad c=\frac{k-1}{T-1},\qquad c_p=(p+1)g(p).
\]
Writing \(d_j=\dim K_j\) and \(a_j=a(K_j)\), we have
\[
 d_{j+1}=T d_j+k-1,\quad d_j+c=(p+c)T^j,
 \qquad a_j=\frac1{(p+1)k^j}.
 \tag{2.1}
\]
For \(R_j=R(K_j)\), the exact multiplicative recurrence is
\[
 R_{j+1}=R_j^T D_j,\qquad
 D_j= k a_j^{k-1}\frac{g(d_{j+1})}{g(m d_j)^k}.
 \tag{2.2}
\]
Robbins's two-sided factorial bounds imply \(\log D_j=O_{m,k,p}(j+1)\) (indeed the linear terms in \(d_j\) cancel). Thus the next series converges absolutely:
\[
 \boxed{\log\Lambda_{m,k,p}=
 \frac{\log c_p+\sum_{j=0}^\infty T^{-j-1}\log D_j}{p+c}.}
 \tag{2.3}
\]
This proves existence when \(m,k\ge2\).

For later use, Robbins's precise form, for every positive integer \(n\), is
\[
 n-\tfrac12\log(2\pi n)-\frac1{12n}
 < \log g(n)
 < n-\tfrac12\log(2\pi n)-\frac1{12n+1}.
 \tag{2.4}
\]
In particular, the still weaker upper estimate obtained by dropping the last negative term is valid.

## 3. Uniform upper envelope and restart

**Lemma 2.** For \(m,k\ge2\), put
\[
\begin{aligned}
 A_{m,k,p}={}&(k-1)+\tfrac12\log k+\tfrac{k-1}{2}\log m
 +\tfrac{k-1}{2}\log(2\pi(p+c))\\
 &-(k-1)\log(p+1)+\frac{k}{12mp},\\
 b_{m,k}={}&\tfrac{k-1}{2}\log(m/k).
\end{aligned}
\]
Then \(\log D_j<A_{m,k,p}+b_{m,k}j\) for every \(j\ge0\). For any \(J\ge0\),
\[
 \boxed{\log\Lambda_{m,k,p}<U_J:={\log R_J+
 A_{m,k,p}/(T-1)+
 b_{m,k}\bigl(J/(T-1)+(T-1)^{-2}\bigr)
 \over d_J+c}.}
 \tag{3.1}
\]

**Proof.** Insert (2.4) into (2.2). Since \(d_{j+1}>T d_j\),
\[
\begin{aligned}
 \log D_j<&\ (k-1)+\log k+(k-1)\log a_j\\
 &+\frac{k}{2}\log(2\pi m d_j)
  -\frac12\log(2\pi d_{j+1})+\frac{k}{12m d_j}\\
 <&\ (k-1)+\frac12\log k+\frac{k-1}{2}\log m
 +\frac{k-1}{2}\log(2\pi d_j)\\
 &-(k-1)\log(p+1)-j(k-1)\log k+\frac{k}{12mp}.
\end{aligned}
\]
Use \(d_j<(p+c)T^j\); the coefficient of \(j\) becomes \(\frac{k-1}{2}(\log T-2\log k)=b_{m,k}\). Summing \(\sum_{h\ge0} T^{-h-1}=1/(T-1)\) and \(\sum_{h\ge0}hT^{-h-1}=1/(T-1)^2\) in the restart of (2.3) proves (3.1). \(\square\)

The first-envelope numerator has a useful exact simplification. Set
\[
\begin{aligned}
 J_{m,k,p}={}&\log c_p-p+\frac c2
 \log\frac{2\pi m(p+c)}{(p+1)^2}
 +\frac{\log k}{2(T-1)}\\
 &+\frac{c}{2(T-1)}\log(m/k)+\frac{k}{12mp(T-1)}.
\end{aligned}
 \tag{3.2}
\]
Direct substitution yields \(U_0=1+J_{m,k,p}/(p+c)\). The elementary Stirling bound \(\log c_p<p+\log(p+1)-\frac12\log(2\pi p)\) and \(p+c<p+1\) give \(J_{m,k,p}<B_{m,k}(p)\), where
\[
\begin{aligned}
 B_{m,k}(p)={}&\log(p+1)-\tfrac12\log(2\pi p)
 +\tfrac c2\log\frac{2\pi m}{p+1}
 +\frac{\log k}{2(T-1)}\\
 &+\frac{c}{2(T-1)}\log(m/k)+\frac{k}{12mp(T-1)}.
\end{aligned}
 \tag{3.3}
\]
All inequalities in this section are strict; subsequent finite bounds will be compared directly against \((6/125)(p+c)\), avoiding any assumption about the sign of \(J\) or \(B\).

## 4. Four exhaustive parameter regimes

Write \(\delta=6/125\). We now exclude every nonwinning triple with \(m,k\ge2\).

### 4.1. Seed dimension \(p\ge20\), uniformly in both arities

Since \(c\le1/m\), maximize \(\log(am)/m\) over positive real \(m\), using \(a=2\pi/(p+1)\), to obtain
\[
 \frac c2\log\frac{2\pi m}{p+1}
 \le \frac\pi{e(p+1)}<\frac{33}{28(p+1)}.
\]
Here \(\pi<22/7\) and \(e>8/3\). For \(k\ge2\), elementary calculus gives \(\log k\le(2k-1)/4\), hence \(\log k/[2(T-1)]\le1/8\). If \(m>k\), then \(m\ge3\), \(\log(m/k)\le\log m\le m/2\), so \(c\log(m/k)/[2(T-1)]\le1/20\); if \(m\le k\), this term is nonpositive. Finally \(k/[12m(T-1)]\le1/36\).

Thus \(B_{m,k}(p)\le F(p)\), with
\[
 F(p)=\log(p+1)-\tfrac12\log(2\pi p)
 +\frac{33}{28(p+1)}+\frac18+\frac1{20}+\frac1{36p}.
 \tag{4.1}
\]
The second derivative is
\[
 F''(p)=-\frac1{(p+1)^2}+\frac1{2p^2}
 +\frac{33}{14(p+1)^3}+\frac1{18p^3}<0\quad(p\ge20).
\]
Indeed \(p/(p+1)\ge20/21\) gives \(F''(p)\le[-359/882+(33/14+1/18)/20]/p^2<0\), a rational inequality. Therefore \(F(p)-pF'(p)\) increases for \(p\ge20\). The exact certificate verifies both \(F(20)-20F'(20)>0\) and \(F(20)<20\delta\). Consequently \(F(p)/p\) decreases and is less than \(\delta\) for all real \(p\ge20\). Since \(J<B\le F<\delta p<\delta(p+c)\), the desired exclusion follows for every \(m,k\ge2\).

### 4.2. Product arity \(m\ge20\) and \(1\le p\le19\)

For these parameters, \(\log(2\pi m/(p+1))>1\). The function \(x\mapsto\log(2\pi x/(p+1))/x\) is decreasing for \(x\ge20\), so
\[
 \frac c2\log\frac{2\pi m}{p+1}\le
 \frac1{40}\log\frac{40\pi}{p+1}.
\]
Using \(\log k\le k/2\), \(c\le1/m\), \(\log(m/k)\le\log m\le m/2\), and \(k/(mk-1)\le2/(2m-1)\), respectively, bounds the remaining three terms in (3.3) by \(1/78\), \(1/156\), and \(1/(4680p)\). Thus \(B_{m,k}(p)\le G(p)\), where
\[
 G(p)=\log(p+1)-\tfrac12\log(2\pi p)
 +\tfrac1{40}\log\frac{40\pi}{p+1}
 +\frac1{78}+\frac1{156}+\frac1{4680p}.
 \tag{4.2}
\]
The exact certificate checks \(G(p)<\delta p\) for all nineteen integers \(1\le p\le19\). This excludes all \(m\ge20,k\ge2\).

### 4.3. \(3\le m\le19,\ k\ge20,\ 1\le p\le19\)

Write \(c_-=19/(20m-1)\), \(c_+=1/m\). As a function of real \(k\), \(c=(k-1)/(mk-1)\) increases, so \(c_-\le c<c_+\). Set
\[
 L_{m,p}=\log\frac{2\pi m(p+c_+)}{(p+1)^2}.
\]
The logarithm in (3.2) is at most \(L_{m,p}\), and hence its \(c\)-weighted contribution is at most \(\frac12\max(c_-L_{m,p},c_+L_{m,p})\), regardless of the sign of \(L_{m,p}\). Moreover \(m<k\) makes the \(\log(m/k)\) term nonpositive; \(\log k/(mk-1)\) is decreasing for \(k\ge20\), as is \(k/(mk-1)\). We obtain
\[
 J_{m,k,p}\le J^*_{m,p}:=
 \log c_p-p+\tfrac12\max(c_-L_{m,p},c_+L_{m,p})
 +\frac{\log20}{2(20m-1)}+\frac{20}{12mp(20m-1)}.
 \tag{4.3}
\]
The exact certificate checks
\[
 J^*_{m,p}<\delta(p+c_-)
 \quad(3\le m\le19,\ 1\le p\le19).
 \tag{4.4}
\]
These \(17\cdot19=323\) strict comparisons exclude every \(k\ge20\) in this range.

### 4.4. Exceptional product arity \(m=2\), join arity \(k\ge20\)

The crude upper bound (3.3) is insufficient for small simplex seeds. Instead use one exact-level restart. Let \(d_1=k(2p+1)-1\), so by (2.2), \(d_1+c=2k(p+c)\). The upper side of (2.4) yields
\[
 \frac{\log R_1}{2k}< M_p+\frac{E_p(k)}{2k},
 \qquad
 M_p=\log c_p-\frac12\log(p+1)+\frac{2p+1}{2}
 -\frac12\log g(2p),
 \tag{4.5}
\]
where \(E_p(k)=\log k+\log(p+1)-1-\tfrac12\log(2\pi d_1)\). Since \(k\ge20\),
\[
 E_p(k)\le\tfrac12\log k+C_p,\quad
 C_p=\log(p+1)-1-\tfrac12\log\left(2\pi(2p+1-\tfrac1{20})\right).
\]
Set \(\eta_p=1/100\) for \(1\le p\le4\), and \(\eta_p=1/40\) for \(5\le p\le19\). The certificate checks
\[
 C_p<\tfrac12(1+\log(4\eta_p))\qquad(1\le p\le19).
 \tag{4.6}
\]
The universal tangent inequality \(\log x\le tx-1-\log t\), used with \(t=4\eta_p\), then gives \(E_p(k)/(2k)<\eta_p\) for every \(k\ge20\).

Here the slope \(b_{2,k}=\frac{k-1}{2}\log(2/k)\le0\). Put
\[
 f_p=1+\frac12\log(4\pi(p+1/2))-\log(p+1)>0,
\qquad
 V_p=\frac{f_p}{2}+\frac{\log20}{78}+\frac{20}{936p}.
\]
The positivity holds for every \(1\le p\le19\) (e.g. from \(e>2,\pi>3\) and \((p+1)^2<48p\)). The coefficients \((k-1)/(2k-1)\le1/2\), \(k/(2k-1)\le20/39\), the monotonicity of \(\log k/(2k-1)\) for \(k\ge20\), and \(p+c<p+1/2\) show \(A_{2,k,p}/(2k-1)\le V_p\). By (3.1),
\[
 (p+c)\log\Lambda_{2,k,p}<M_p+\eta_p+\frac{V_p}{40}.
 \tag{4.7}
\]
The exact nineteen-case check is
\[
 \boxed{M_p+\eta_p+V_p/40
 <\frac{131}{125}\left(p+\frac{19}{39}\right),\quad1\le p\le19.}
 \tag{4.8}
\]
Since \(c\ge19/39\), (4.7)--(4.8) prove \(\log\Lambda<131/125\) for all \(m=2,k\ge20\).

## 5. Remaining finite cases

The only remaining region is \(1\le p\le19,\ 2\le m,k\le19\), treated by exact rational intervals for \(U_J\) in (3.1):

| Parameter region | Strict finite check |
| --- | --- |
| \(3\le m\le19,2\le k\le19,1\le p\le19\) | \(U_0<131/125\) for all 5,814 triples |
| \(m=2,4\le k\le19,1\le p\le19\) | \(U_1<131/125\) for all 304 triples |
| \(m=2,k=3,1\le p\le19\) | \(U_1<131/125\) except \(p=4\); sharpened Robbins \(U_2<131/125\) at \(p=4\) |
| \(m=k=2,1\le p\le19, p\ne5\) | \(U_0<131/125\) for \(p\ge8\); sharpened Robbins \(U_3<131/125\) for \(p\in\{1,2,3,4,6,7\}\) |

The sharpened finite-level upper bound used in the last two rows retains \(-1/(12d_{j+1}+1)\) in (2.4); all logarithms are bounded rigorously, not evaluated as floats. These rows exhaust \(5,814+341=6,155\) losing triples. The remaining \((m,k,p)=(2,2,5)\) is the already certified orbit of [005 v5, Sections 9–10](../../preprints/005-simplex-product-optimum/v5/paper.md), with \(\Lambda>14267/5000\); the certificate also checks \(131/125<\log(14267/5000)\). This completes the proof for \(m,k\ge2\). \(\square\)

## 6. The boundary arities \(m=1\) or \(k=1\)

If \(m=1\) and \(k\ge2\), a join of simplices is a simplex. Its dimension tends to infinity and \(R(T_d)^{1/d}\to e<e^{131/125}\). If \(k=1\), repeated products preserve the projection ratio multiplicatively and the dimension additively, so \(\Lambda_{m,1,p}=c_p^{1/p}\) (also when \(m=k=1\)). For \(p\ge20\), the Stirling bound gives \(\log c_p-p<\log(p+1)-\frac12\log(2\pi p)<F(p)<\delta p\) from Section 4.1; for the other nineteen values of \(p\), the exact checker verifies \(\log c_p<(131/125)p\). All boundary cases therefore lie strictly below the winner. Together with Section 5, this proves Theorem 1 in full. \(\square\)

## 7. Proof certificate and trust boundary

Run from the repository root:

```sh
python3 notes/unbalanced-homogeneous-projection-recursion/checker.py
python3 -O notes/unbalanced-homogeneous-projection-recursion/checker.py
```

The program performs every finite check in Sections 4--6 and rejects any failed strict comparison via explicit exceptions (not disabled by Python optimization). It uses `int` and `fractions.Fraction` exclusively for arithmetic decisions. For \(y\in[1,2)\), write \(z=(y-1)/(y+1)\in[0,1/3)\); for \(N=16\),
\[
 2\sum_{j=0}^{N-1}\frac{z^{2j+1}}{2j+1}
 \le\log y\le
 2\sum_{j=0}^{N-1}\frac{z^{2j+1}}{2j+1}
 +\frac{2z^{2N+1}}{(2N+1)(1-z^2)}.
\]
Repeated exact powers of two reduce any positive rational logarithm to this interval. The bounds \(333/106<\pi<355/113\) are *themselves* checked with Machin's identity \(\pi=16\arctan(1/5)-4\arctan(1/239)\) and rational alternating Taylor bounds. No numeric optimizer, floating evaluation, hidden solver, or external network service participates in the certificate.

The checker proves all **finite inequalities** used above, conditional only on the displayed standard analytic facts (Robbins--Stirling, the 005 v2 product/join identities, and elementary one-variable inequalities) established on paper. It is not a Lean formalization of the entire theorem. To replay the inherited winner endpoint independently, run the existing `preprints/005-simplex-product-optimum/v5/code/check_balanced.py` in both normal and optimized modes; that certificate contains the exact level-6 integer comparison, while our file rechecks the threshold ordering.

**Novelty status:** no systematic literature priority investigation or external human peer review has been completed. This result does not change any v2/v5 historical file and should be described as an extension in a separate note.
