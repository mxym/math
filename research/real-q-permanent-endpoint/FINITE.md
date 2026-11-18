# An explicit finite rational matrix and rational comparison point

The [October 8 existence proof](../../notes/bapat-real-symmetric-existence-counterexample/proof.md) and its [Lean root theorem](../../formalizations/bapat-real-symmetric-existence-counterexample/formalization/sources/BapatIntegerCounterexample.lean) already give an integer real positive-definite counterexample in existence, including $P'_1<0$; they do not specify its order or matrix. Here the distinction is effectivity: the construction fixes a dimension, row multiplicities and order, a rational diagonal perturbation and a rational comparison parameter. The old Lean proof is not a certificate for these choices. This section specifies the rows by a formula and certifies the sign analytically. No enormous matrix or permanent was evaluated. Equations (1)–(5) and the row-coordinate conventions appear in [PROOF.md](PROOF.md); in particular the sphere is in **complex** dimension four and the Gram rows are **real**.

## 1. A discrete list in a fixed order

Let $M=10^{22}$ and $Q=10^{2M}$. Define componentwise downward rounding
$$
R_Q(x+iy)=\big(\lfloor Qx\rfloor+i\lfloor Qy\rfloor\big)/Q,\qquad \delta=2/Q .
$$
The Euclidean rounding error is less than $\delta$, also for negative inputs. For $p,h=0,\ldots,M-1$ put
$$
s_p=R_Q(e^{\pi i p/M}),\qquad c_h=R_Q(e^{2\pi i h/M}).
$$
These are exact definitions using algebraic roots of unity. With $r_j=j/100$ and $H(r)=r^2/(1+r^2)$, let
$$
b_j=H(r_{j+1})-H(r_j)\ (0\le j<10000),\quad b_{10000}=1-H(100),\quad
w_j=\tfrac{99}{100}b_j+\tfrac1{100}\mathbf1_{j=0}.
$$
The $b_j$ are the weights of a complex Cauchy radius rounded down to a hundredth and capped at 100. Set
$$
D=100\prod_{j=0}^{10000}(10000+j^2),\qquad n=DM^2.
$$
Each $Dw_j$ is an integer: $H(r_j)=j^2/(10000+j^2)$, so $D/100$ clears each separate term. For each triple $(j,h,p)$ include exactly $Dw_j$ copies of
$$
t=r_jc_h,\qquad v=(\Re s_p,\Im s_p,\Re(ts_p),\Im(ts_p)).
$$
Order all copies by nondecreasing $\Re t$, breaking ties lexicographically by $(j,h,p,\text{copy index})$. This defines exactly $n$ rows with $\|v\|\le102$. Denote by $A_0$ their real Gram matrix and by $p(z),F(z)$ the products and wedge polynomial of (1); the subscript $p$ of a phase above is just an index. The distribution of a uniformly selected row label is $w_j$ times independent uniform $h,p$.

## 2. An upper potential bound uniform at this finite order

For complex $U,V$ define $B_* =\max(|U|,|V|)$. The unrounded phases $s_p^0=e^{\pi ip/M}$ obey
$$
\left|\prod_p(s_p^0 U+\overline{s_p^0}V)\right|\le 2 B_*^M.
$$
After removing a unit scalar from each factor the phases $(s_p^0)^2$ run through an entire regular $M$-gon: the magnitude of its two-term product is at most $|U|^M+|V|^M$. In each factor rounding changes the value by at most $2\delta B_*$. Both exact and rounded factors have modulus at most $3B_*$. The telescoping product error is therefore at most $2\delta M3^{M-1}B_*^M\le B_*^M$ since $4M3^{M-1}10^{-2M}<1$. The same argument for the full circle $c_h$ gives
$$
\left|\prod_p(s_p U+\bar s_pV)\right|\le 3B_*^M,
\qquad \left|\prod_h(U+c_h V)\right|\le 3B_*^M .
$$
These product inequalities allow zero factors.

For unit $z$ use the two vectors $u,w$ of [§2 of the qualitative proof](PROOF.md) and write $g_n(z)=n^{-1}\log|p(z)|+\frac12\log2$. Apply the first finite product bound conditionally on $j,h$ to obtain
$$
g_n(z)\le \log(3)/M+\mathbb E_{j,h}\log\max(|u_1+tu_2|,|w_1+\bar t w_2|).
$$
As before introduce an independent, genuinely uniform continuous phase $\alpha$ and $(a,b)=u+e^{i\alpha}\bar w$. The log maximum is the phase mean of $\log|a+tb|$. In the unpinned part of the radial law, averaging over $h$ at radius $r_j$ is bounded by $\log\max(|a|,r_j|b|)+\log(3)/M$ by the second product bound. Flooring/capping the radius can only decrease this log maximum; its original radial mean is $\frac12\log(|a|^2+|b|^2)$ by the circle and radial integral used in (4). If $a=0$, the finite radial law has positive mass at zero and the inequality is valid with left side minus infinity. The separate pinning mass contributes $\log|a|$. Average over $\alpha$, bounding the $99/100$ norm-log term by zero via Jensen and evaluating the first-coordinate log term by the circle identity. This gives at this fixed $n$
$$
g_n(z)\le\frac{2\log3}{M}+\frac1{100}\log\max(|u_1|,|w_1|). \tag{6}
$$
All extended-real exchanges can be justified by Tonelli applied to a constant minus the upper-bounded logs.

## 3. Concentration with explicit slack

Take $\rho_0=10^{-8}$ and $\rho_1=10^{-22}$. Write $N$ for the union of the radius-$\rho_0$ tubes of the two phase circles $z_0,\bar z_0$, using Euclidean chordal distance minimized over a unit scalar. Outside $N$, $\max(|u_1|,|w_1|)\le1-\rho_0^2/2$. By (6) and $\log(1-x)\le-x$,
$$
g_n(z)<-4\cdot10^{-19}\quad (z\notin N).
$$
In the inner tube of radius $\rho_1$ about the phase circle of $z_0$, each row instead satisfies
$$
\sqrt2|v^Tz|\ge 1-\delta-\sqrt2\cdot102\rho_1\ge1-2\cdot10^{-20},
\qquad g_n(z)\ge-4\cdot10^{-20},
$$
by $\log(1-x)\ge-2x$ for $0\le x\le1/2$. For uniform $z$ on the unit sphere in $\mathbb C^4$, $|\langle z_0,z\rangle|^2$ is Beta$(1,3)$ (normalize four independent complex Gaussians). The condition $1-|\langle z_0,z\rangle|^2\le(\rho_1/2)^2$ suffices for membership in that inner tube. Thus its surface probability is at least $(\rho_1/2)^6>10^{-138}$. Comparing the exponential weights $|p(z)|^2$ in the two regions yields
$$
\mu_n(N^c)\le10^{138}\exp\!\left[-2n(4\cdot10^{-19}-4\cdot10^{-20})\right]<1/100, \tag{7}
$$
as $n\ge M^2=10^{44}$. Unlike the qualitative concentration statement this bound has no unspecified convergence threshold.

## 4. Effect of the ordering

Let $X=\Re T$ for the unmodified complex Cauchy variable and $Y=\Re t$ for the discrete row. Couple them by flooring/capping the radius, rounding its angle down to the regular $M$-gon, rounding the root componentwise and independently pinning to zero. Since $|e^{i\alpha}-e^{i\beta}|\le|\alpha-\beta|$,
$$
\mathbb E|X-Y|\le\pi/200+1/100+2/100+100(2\pi/M+\delta)<46/1000.
$$
Here the terms bound pinning, radial flooring, truncation above radius 100 and angular/coordinate rounding, respectively. Therefore $G(Y)\ge\pi/4-\mathbb E|X-Y|>739/1000$. At $z_0,y_0$ the signed real contraction in (3) divided by $n^2$ is exactly $G(Y)$ by the sorted-pair identity; ties are harmless. The rounded scalar $s_p$ cancels in $v^Ty_0/v^Tz_0=t$. At the conjugate point take $\bar y_0$.

After aligning the phase of $z$ with its nearest center, on $N$ the change in each ratio is at most
$$
\frac{102^2\rho_0}{0.69\cdot0.70}<1/1000
$$
since the center denominator has modulus at least $(1-\delta)/\sqrt2>0.70$ and the tube denominator exceeds $0.69$. The sum of the absolute coefficients $|2s-n-1|$ is at most $n^2$. Hence $\|F(z)/p(z)\|\ge(73/100)n^2$ on $N$. Equations (2) and (7) give
$$
\frac{\|F\|_F^2}{\operatorname{per}A_0}\ge
\frac{99}{100}\left(\frac{73}{100}\right)^2\frac{n^4}{(n+3)(n+2)}>\binom{n}{2}.
$$
Indeed even $0.99(0.73)^2>(1+3/1000)(1+2/1000)/2$, and $n\ge1000$. By (1), $P'_1(A_0)<0$.

## 5. Full positive definiteness and an explicit rational q

Put $L=100Q^2$, $B=L^2 A_0$ and $K=20000L^2$. All coordinates of $Lv$ are integers, including the products $Lr_jc_hs_p$. Thus $B$ is PSD with integer entries bounded in magnitude by $K$. The derivative is homogeneous of degree $n$ in $B$ and integer-valued, so $P'_1(B)\le-1$. Set
$$
\zeta=\frac1{2n!\,n^3(K+1)^n},\qquad A=B+\zeta I_n,\qquad
J=n!\,n^4(K+1)^n,\quad h=\frac1{4J},\quad q=1-h .
$$
The real symmetric rational $A$ is positive definite and non-diagonal (a diagonal $B$ would have zero derivative). Telescoping each permutation product yields
$$
|P'_1(A)-P'_1(B)|\le n!\binom{n}{2}\, n\zeta(K+1)^{n-1}\le 1/4 .
$$
Hence $P'_1(A)\le-3/4$. For $0\le t\le1$ the absolute second derivative of $P_t(A)$ is at most $J$: each permutation exponent is at most $\binom{n}{2}$ and each term product has magnitude at most $(K+1)^n$. Taylor's theorem now gives the strict comparison at the specified rational $q\in(0,1)$:
$$
P_q(A)-P_1(A)\ge3h/4-Jh^2/2=5h/8>0.
$$
Multiplying $A$ by the positive denominator of $\zeta$ gives an integer PD counterexample too, by homogeneity. These formulas specify the witness but are not a practical coefficient expansion or a minimal-dimension claim. The constants use only $3.14<\pi<22/7$, $\log3<1.1$ and the elementary log bounds above.
