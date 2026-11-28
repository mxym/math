# Sharp connectivity of the equal-half seven-cluster Kuramoto limit

[O'Keeffe, *Beyond 11/16*](https://arxiv.org/html/2610.21271v1), Theorem 1, constructs strictly stable nonsynchronous Kuramoto templates approaching
\[
\mu_0=\frac{4+2q_*}{7+q_*}=0.6929077063\ldots ,
\qquad q_*=0.6505691669\ldots .
\]
His §IV.3 reports numerical evidence of optimality in the limiting link pattern, but does not prove it. We prove **global optimality within the equal-half first-order \(S_7\) geometry**, allowing an arbitrary outer-to-middle mass ratio. In particular it is not just a local or a fixed-mass bound. We also give the full semidefinite feasibility condition of the limiting symmetric Schur form. This is not an upper bound for arbitrary Kuramoto networks.

## 1. Precise domain and result

Take sheets \(A,B,C,W\) at four successive quarter turns; split \(A,B,C\) into two halves each, leaving \(W\) whole. The leading masses of each half of \(A,C\) are \(a>0\), those of each half of \(B\) are \(b>0\), and \(W\) has mass \((1+q)b\), with \(q\in[0,1]\). The last mass is the leading equilibrium balance; write \(r=a/b>0\), so \(b=1/(4r+3+q)\). The limiting link pattern is O'Keeffe's Table 2: complete within each sheet; both opposite-sheet cuts empty; \(A\!-\!B\) and \(B\!-\!C\) have density 1 between equal signs, \(q\) between opposite signs; the \(C\!-\!W\) and \(W\!-\!A\) cuts are complete. The first-order half-angle deviations about their respective sheet-center offsets are \(\pm h,\ \pm wh,\ \pm h\) with \(w\ge0\). The centers themselves are allowed arbitrary first-order deviations.

Allow arbitrary twice continuously differentiable variations of masses, phases and link densities in \([0,1]\) for \(h\ge0\), with the specified leading data and first-order relative deviations, satisfying phase balance and nonnegative cluster Hessian for all small positive \(h\). Opposite-sheet densities need not stay identically zero. By differentiability the limiting normalized minimum degree is
\[
\mu(q,r)
=\frac{\min\{2r+2(1+q),\ 2+2r(1+q),\ 4r+1+q\}}{4r+3+q}.       \tag{1}
\]
We prove \(\mu(q,r)\le\mu_0\), with equality requiring \(r=1,\ q=q_*,\
w=w_*=\sqrt{1+4q_*/(1+q_*)^2}\). The known equal-mass construction shows this supremum is sharp. In particular unequal masses **between sheets** do not help in this domain. We do not treat unequal masses **inside a split pair**, differing split amplitudes at \(A,C\), a discontinuous or nonsmooth family, or a finite nonzero-splitting global optimum.

## 2. Reduction for arbitrary derivatives

Let \(W_{ij}(h)=x_i(h)x_j(h)P_{ij}(h)\) be the symmetric weighted links, suppressing self-links for the Hessian. For each cluster \(i\), phase balance in mass-weighted form is \(\sum_j W_{ij}\sin(\varphi_j-\varphi_i)=0\). The cluster Hessian is the quadratic form
\[
       \sum_{i<j}W_{ij}\cos(\varphi_j-\varphi_i)(y_i-y_j)^2 .
\]
Use sheet rotations \((\eta_A,\eta_B,\eta_C,\eta_W)\), modulo common rotation. The adjacent rotation differences \(d=(\eta_A-\eta_B,\eta_B-\eta_C,\eta_C-\eta_W,\eta_W-\eta_A)\) satisfy \(\sum d_j=0\), and parametrize all sheet rotations modulo the constant.

First, stability forces all first-order sheet-center offsets to be the same, and all first derivatives of opposite-sheet link masses to vanish. Indeed, the four adjacent cuts have the same total leading link mass \(2ab(1+q)\). Their first-order cosine sums are that constant times the successive center-offset differences, since the signed half-offset averages are zero. The four coefficients therefore sum to zero. On the three-dimensional subspace \(\sum d_j=0\), the quadratic form consisting of these four diagonal terms has trace zero: the projection of each coordinate vector has squared norm \(3/4\). Any opposite-sheet link at first order adds a nonpositive term \(-W'_{ij}(0)(\eta_{s(i)}-\eta_{s(j)})^2\), because it was zero at the leading edge and its cosine is \(-1\) at \(h=0\). Its trace is strictly negative if \(W'_{ij}(0)>0\). But the whole first-order form, being a limit of scaled nonnegative forms, is nonnegative. Thus all opposite first derivatives vanish, and the trace-zero remainder must be identically zero. A diagonal form vanishing on \(\sum d_j=0\) has all coefficients zero (test coordinate pair differences). This forces the center offsets to be equal. Gauge their common value away.

Now use \(s=(-1,1,-w,w,-1,1,0)\) in the order of the six halves and \(W\), and write the phases as their quarter-turn values plus \(hs_i+h^2t_i+o(h^2)\). For the cut oriented from sheet \(j\) to the next in order, its second-order cosine sum is \(b^2 c_j\), with
\[
 b^2 c_j=\sum_{i\to k\ {\rm on\ cut}}
      \big(W'_{ik}(0)(s_i-s_k)+W_{ik}(0)(t_i-t_k)\big).
\]
The \(c_j\) obey the exact budget
\[
                        \sum_{j=0}^3 c_j=8r^2+4w^2=:E.      \tag{2}
\]
To verify this, sum the phase balances at order zero weighted by \(t_i\); the adjacent terms in \(t_i-t_k\) sum to zero. At order one weight the balance equations by \(s_i\). Adjacent edges contribute their \(W'_{ik}(0)(s_i-s_k)\), as the sine of a quarter turn has zero derivative. Same-sheet edges contribute \(-W_{ik}(0)(s_i-s_k)^2\); opposite edges contribute nothing. There are two outer within-sheet pairs of weight \(a^2\) and difference magnitude 2, and one middle pair of weight \(b^2\) and magnitude \(2w\). This gives (2), including varying masses and arbitrary \(t_i\).

Introduce additional half rotations \(-h\zeta_j/2,+h\zeta_j/2\) on each split sheet. Divide the quadratic form by \(h^2\) and take its limit. The block on \((\zeta_A,\zeta_B,\zeta_C)\) is \(\operatorname{diag}(a^2,b^2,a^2)\), entirely from same-sheet pairs. Set
\[
 \rho=1+q,\quad l=1-q,\quad
 \alpha=l w-\rho,\quad \beta=l-\rho w,\quad R=r^2.
\]
The mixed terms are
\[
-2ab\big[(\alpha d_0-\rho d_3)\zeta_A
        +\beta(d_0+d_1)\zeta_B
        +(\alpha d_1-\rho d_2)\zeta_C\big].
\]
For example on \(A\!-\!B\) the two unscaled mixed coefficients, summing over signs \(\sigma,\tau=\pm1\), are \((ab/2)\sum P_{\sigma\tau}(\sigma-w\tau)\sigma=-ab\alpha\), and the corresponding \(-\tau\) sum is \(-ab\beta\). The whole-sheet cuts give \(+ab\rho\) for the adjacent split rotation. This computes every mixed term by reflection. Opposite-sheet edges at order two only subtract a nonnegative rotation square; discard them for a necessary condition.

Completing the squares in \(\zeta\) and dividing by \(b^2\), nonnegative Hessian therefore requires a nonnegative form
\[
 \sum_j c_j d_j^2-(\alpha d_0-\rho d_3)^2
         -R\beta^2(d_0+d_1)^2-(\alpha d_1-\rho d_2)^2 .
\]
Reflection that exchanges \(A,C\) and flips the signs in the split sheets sends \(d\) to \((-d_1,-d_0,-d_3,-d_2)\) and preserves the negative-square sum. Average the reflected form; this preserves nonnegativity and yields the form
\[
 Q= u(d_0^2+d_1^2)+(E/2-u)(d_2^2+d_3^2)
      -(\alpha d_0-\rho d_3)^2-R\beta^2(d_0+d_1)^2
      -(\alpha d_1-\rho d_2)^2.                              \tag{3}
\]
This extends O'Keeffe's equation (13), which uses \(R=1\) and a particular first-order density correction. No restrictions on \(u\) beyond the necessary nonnegative form will be used in the upper bound.

## 3. Exact feasibility of the limiting Schur form

Let \(C=2-l^2=1+2q-q^2>0\). The following two tests completely characterize the existence of a feasible real \(u\):
\[
\begin{split}
 A(R,q,w)&=4R+Cw^2-2R(\rho w-l)^2\ge0,\\
 B(R,q,w)&=4R+Cw^2+4l\rho w-4\rho^2\ge0.                    \tag{4}
\end{split}
\]
Strict inequalities characterize positive definiteness for some \(u\).

For the matrix computation, use \(d_3=-d_0-d_1-d_2\) and the three \(d_0,d_1,d_2\) basis columns \((1,0,-1),(0,1,0),(1,0,1)\). In the top \(2\times2\) block the diagonal entries are both \(f=E/2-\alpha^2-R\beta^2-\rho^2\), and the off-diagonal is \(e=-2\alpha\rho-R\beta^2\). Thus \(f+e=A\), \(f-e=B\). The cross entries with the third column satisfy \(b_{13}+b_{23}=A\) and \(b_{13}=2(u-u_0)\), where
\[
u_0=\tfrac12(E/2+\alpha(\alpha+2\rho)+R\beta^2-\rho^2).
\]
The third diagonal \(b_{33}(u)=5E/2-4u-(\alpha+2\rho)^2-R\beta^2-\rho^2\) obeys
\[
G=b_{33}(u_0)-2e-f=8R+2Cw^2>0 .
\]
Rotate the top block to its plus and minus eigenvectors. The third cross coordinates are \(A/\sqrt2\) and \((4(u-u_0)-A)/\sqrt2\). For \(B>0\) the remaining scalar after the Schur elimination is
\[
                         G-\frac{8(u-u_0-e/2)^2}{B}.        \tag{5}
\]
This also holds at \(A=0\): its cross coordinate vanishes, and its zero eigendirection can simply be deleted. If \(B=0\), positivity requires that its cross coordinate vanish, namely \(u=u_0+e/2\), and the remaining scalar is \(G\). This proves (4), including all semidefinite boundary cases. In particular at \(R=1,q=q_*,w=w_*\) we have \(A=B=0\) and the unique feasible \(u\) gives a rank-one form.

## 4. Excluding all improved mass ratios

Write \(m=\mu_0\). At fixed \(q\), the first term in the minimum of (1), after division by the denominator, strictly decreases with \(r\). The middle term strictly increases with \(r\) for \(q>\sqrt5-2\). For \(q\le\sqrt5-2\) and \(r<1\) that middle term is bounded by its \(r=0\) value, at most \(2/3\). For \(r\ge1\), the first term is bounded above by its \(r=1\) value, increasing in \(q\). Hence \(\mu(q,r)\ge m\) implies \(q\ge q_*\). If \(q=q_*\), the same argument forces \(r=1\).

For \(q\ge q_*\), both of the first two degrees in (1) must be at least \(m\). Solving gives
\[
 r_-(q,m)=\frac{m(3+q)-2}{2\rho-4m}
 \ \le r\le\
 r_+(q,m)=\frac{2\rho-m(3+q)}{4m-2}.                         \tag{6}
\]
The denominators are positive in this range. At \(q_*\), the two endpoints both equal 1.

For \(q\in[13/20,1]\) and \(r\) in (6), one has \(B(R,q,6/5)<0\) and \(A(R,q,w)\) strictly decreasing for \(w\ge6/5\). These are verified below using only the two endpoint radii: the first inequality is strongest to check at \(r_+\), since \(B\) increases with \(R\); for the second it suffices that
\[
 2r_-^2\rho(6\rho/5-l)>6C/5,
\]
which gives negative derivative at \(6/5\) and negative quadratic leading coefficient for every \(r\ge r_-\). Since \(B\) is increasing for \(w\ge0\), a common solution of (4) must have \(A(R,q,w_B)\ge0\), where \(w_B>6/5\) is the positive root of \(B\).

Put \(L(w)=\rho^2-l\rho w-Cw^2/4\); then \(R=L(w_B)\). For fixed \(q\), the quantity
\[
   F(w)=A(L(w),q,w)=Cw^2+2L(w)\big(2-(\rho w-l)^2\big)
\]
expressed as a function of \(R=L(w)\) is strictly convex on the range \(w\ge6/5\). To see this, its second derivative with respect to \(R\) has numerator \(J=F''L'-F'L''\) and denominator \((L')^3<0\). The cubic \(J\) has coefficients, in ascending order,
\[
\begin{aligned}
 2l\rho(3l^2\rho^2+l^2+2\rho^4+2\rho^2-2),\quad&
 -6l^2\rho^2(l^2+2\rho^2-2),\\
 -\tfrac32 l\rho C(6\rho^2-C),\quad& -2\rho^2 C^2 .
\end{aligned}
\]
The linear and cubic terms are nonpositive, with the cubic strictly negative. For the constant plus quadratic terms, factor \(l\rho\). With \(z=\rho^2\in[27/10,4]\), \(l^2\le1/8\), \(C\ge15/8\), \(w^2\ge36/25\), the bracket is bounded above by
\[
     4z^2+\tfrac{19}4z-\tfrac{15}4-\tfrac{81}{20}(6z-15/8)
       =4z^2-\tfrac{391}{20}z+\tfrac{123}{32}<0.
\]
The convex quadratic is negative at both endpoints. Thus \(J<0\), proving strict convexity and reducing the maximum of \(A(R,q,w_B)\) on the interval of squared radii to the two endpoints.

It remains to bound these endpoint values, which coincide and vanish at \(q_*\). For either endpoint \(r(q,m)\) of (6), put \(R=r^2\) and express the root and value without a constraint solve:
\[
\begin{aligned}
 w_B&=\frac{2}{C}\left(\sqrt{l^2\rho^2+C(\rho^2-R)}-l\rho\right),\\
 z_B&=\rho w_B-l,\qquad
 \Phi(q,m)=4\rho^2-4l\rho w_B-2R z_B^2 .
\end{aligned}
\]
The formula for \(\Phi\) uses \(B=0\). Differentiating at fixed \(m\),
\[
 w_B'=\frac{8\rho+8q w_B-2l w_B^2-4R'}{2Cw_B+4l\rho},\qquad
 \Phi'=8\rho+8q w_B-4l\rho w_B'-2R' z_B^2
                      -4R z_B(\rho w_B'+w_B+1).              \tag{7}
\]
The only numerical part of the upper proof is a finite rational interval certificate that \(\Phi'<0\) for both endpoints over \(q\in[13/20,1]\) and \(m\in[6929077/10^7,6929078/10^7]\), together with the two preliminary endpoint inequalities. The [verifier](verify_factor_kuramoto_s7_mass_optimum.py) uses exact fraction arithmetic including dyadic integer square-root enclosures, and partitions the closed \(q\)-interval into 28 leaves of depth at most 5. It also checks the enclosure of \(m\): at \(R=1\) the equations \(A=B=0\) are \(e=0,\ f=0\), with \(w=\sqrt{1+4q/(1+q)^2}\). In this domain the resulting \(f(q,w(q))\) is strictly decreasing: \(f_q\le-2-18q\), \(f_w\le4\), and \(0\le w'\le2\). Its signs at \(65056916/10^8\) and \(65056918/10^8\) are verified by exact intervals. This identifies the bracketed root with O'Keeffe's \(q_*\) and hence supplies the stated interval for \(m\).

Therefore when \(q>q_*\), both endpoints give \(\Phi(q,m)<0\), and strict convexity rules out (4) anywhere in the radius interval. When \(q=q_*\), the unique radius is \(r=1\); \(B\) is increasing in \(w\) and \(A\) strictly decreasing above \(6/5\), so the common boundary root \(w_*\) is the only feasible angle ratio. This completes the upper bound and the equality statement.

The limiting constant is already reached as a supremum of strict nonsynchronous templates by O'Keeffe's construction (Appendix A); we do not count that lower-bound construction as new. The exact checks here certify (7) and the other stated bounds, not stability of arbitrary seven-cluster templates or of arbitrary graphs.
