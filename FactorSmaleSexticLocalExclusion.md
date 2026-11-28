# Explicit local exclusion at the sextic Smale extremizer

For \(f(0)=0\) and \(f'(0)=1\), put \(S(f)=\min_{f'(c)=0}|f(c)/c|\), counting each nonzero critical point in the usual way. This note gives an explicit neighborhood and a quadratic deficit for the candidate sharp sextic value \(5/6\).

**Theorem.** Suppose
\[
 f(z)=z-\frac{z^6}{6}+\sum_{j=1}^4 b_jz^{j+1},\qquad
 A=\sum_{j=1}^4(j+1)|b_j|\le\frac17,\qquad
 v_j=\frac{5-j}{5}b_j,\qquad E=\sum_{j=1}^4|v_j|^2.
\]
Then
\[
 S(f)\le \frac56\exp(-E/8).
\]
In this neighborhood, the value \(5/6\) is attained only when \(b_1=b_2=b_3=b_4=0\). The order of the quadratic deficit cannot be improved uniformly to a smaller power of the coefficient distance. An arbitrary nonzero sextic leading coefficient can be moved to the displayed normalization by replacing \(f(z)\) by \(f(sz)/s\) for a suitable nonzero \(s\), which preserves \(S\).

[Tischler (1989)](https://doi.org/10.1016/0885-064X(89)90019-8), with a stronger local form in [Tischler (1994)](https://www.numdam.org/article/AST_1994__222__407_0.pdf), established qualitative local bounds near these polynomials. The claim here is quantitative and specific to degree six. It makes **no** claim that the global degree-six optimum is \(5/6\); compare the global reported \(K(6)\le17/20\) in [Charalambides (2026)](https://aixiv.online/abs/2611.02831).

## 1. Locate the five roots and control the linear terms

We may assume \(A>0\). For each fifth root of unity \(t\), set \(r=A/4\). On \(|u|=r\),
\[
 |(1+u)^5-1-5u|\le 10r^2(1+r)^3,\qquad
 \left|\sum_{j=1}^4 (j+1)b_jt^j(1+u)^j\right|\le A(1+r)^4.
\]
By monotonicity after division by \(A\), the margin in the comparison with \(5r\) is at least
\[
 \frac54-\frac5{56}(29/28)^3-(29/28)^4
 =\frac{19}{175616}>0.
\]
Rouché applied to \(f'(t(1+u))\) against \(-5u\) gives one critical point \(c_t=t(1+u_t)\) in each disk. The five disks are disjoint, so these are all critical points. Put
\[
 L_t=\sum_{j=1}^4(j+1)b_j t^j,\quad
 V_t=\sum_{j=1}^4 v_j t^j,\quad
 W_t=\sum_{j=1}^4 jv_jt^j,\quad
 T_t=\sum_{j=1}^4 v_jt^j(1+u_t)^j.
\]
The critical equation, the displayed binomial remainder, and
\(|(1+u_t)^j-1|\le j r(1+r)^{j-1}\) imply
\[
 |u_t-L_t/5|\le (13/40)(29/28)^3 A^2<3A^2/8.
\tag{1}
\]
Eliminating \(c_t^5\) from \(f(c_t)/c_t\) with \(f'(c_t)=0\) gives
\(f(c_t)/c_t=(5/6)(1+T_t)\).

For a quantity indexed by \(t\) write \(\|X\|_{\mathrm{rms}}^2=\tfrac15\sum_t|X_t|^2\).
The identities and bounds needed below are
\[
\begin{aligned}
 |T_t-V_t-L_tW_t/5|&\le (13/5)A^2\sqrt E,\\
 \max_t |T_t|&\le (9/4)\sqrt E\le9/70,\\
 \|T-V\|_{\mathrm{rms}}&\le ((4/5)A+(13/5)A^2)\sqrt E,\\
 \|T\|_{\mathrm{rms}}&\le (6/5)\sqrt E .
\end{aligned}
\tag{2}
\]
For the first line, use (1), \(|W_t|\le(\sqrt{30})\sqrt E\), and
\[
 \left|\sum_j v_jt^j((1+u_t)^j-1-ju_t)\right|
 \le \sqrt{46}\,r^2(1+r)^2\sqrt E .
\]
Here \(30=\sum_j j^2\) and \(46=\sum_j\binom j2^2\); using \(\sqrt{30}\le11/2\) and \(\sqrt{46}\le7\) suffices. For the second line use \(|V_t|\le2\sqrt E\) and
\[
 |T_t-V_t|\le (11/2)r(1+r)^3\sqrt E,\qquad \sqrt E\le(2/5)A.
\]
For the third line, in the first line of (2) bound \(\|L W/5\|_{\mathrm{rms}}\le (A/5)\|W\|_{\mathrm{rms}}\le(4/5)A\sqrt E\), by orthogonality of the powers of \(t\). The last line then follows from \(\|V\|_{\mathrm{rms}}=\sqrt E\).

Let \(g_t=\log|1+T_t|\) and \(s_t=\Re V_t\). The standard power-series bound
\[
 |\log(1+z)-z|\le \frac{|z|^2}{2(1-|z|)}\qquad (|z|<1)
\]
and (2) give
\[
 \|g-s\|_{\mathrm{rms}}
 \le \left(\frac45+\frac{13}{5\cdot7}
  +\frac{(9/4)(6/5)(2/5)}{2(1-9/70)}\right) A\sqrt E
 < \frac95 A\sqrt E.
\tag{3}
\]
The logarithm and identity of its real part here are valid because \(|T_t|<1\).

## 2. An exact polynomial bounds the product

Let \(R(v)=\prod_t(1+T_t)\). This is the determinant of multiplication by \(1+\sum_{j=1}^4v_j z^j\) in the five-dimensional quotient by
\[
 z^5-1-\sum_{j=1}^4 w_jv_j z^j,\qquad (w_1,w_2,w_3,w_4)=(5/2,5,10,25).
\]
Indeed its roots are the five distinct \(c_t\), so evaluation at them diagonalizes the multiplication map. For an exact determinant calculation, reduce \(z^k\), \(5\le k\le8\), using the displayed equation, construct the five columns for \(z^k(1+\sum v_j z^j)\), \(0\le k\le4\), and sum the signed products over the \(5!\) permutations. This gives 59 terms in total, with constant term 1, vanishing linear part, and
\[
 R_2=30(v_1v_4+v_2v_3),\qquad
 R_3=-15v_1^2v_3-15v_1v_2^2+960v_2v_4^2+810v_3^2v_4 .
\tag{4}
\]
The attached standard-library script reproduces this determinant and the exact bounds below.

We claim that \(|R_3|\le18 A E\). Write \(x,y,z,u=|v_1|,|v_2|,|v_3|,|v_4|\) and expand \(18AE=18((5/2)x+5y+10z+25u)(x^2+y^2+z^2+u^2)\). The two cubic terms containing \(x\) are individually absorbed. After subtracting \(960yu^2\) and \(810z^2u\) from the other terms, the two only negative coefficients are \(-870yu^2\) and \(-360z^2u\). The former is absorbed by \(450u(y^2+u^2)\) since \(870^2<4\cdot450^2\). The latter together with \(180z^3+180zu^2\) is \(180z(z-u)^2\).

For any term \(c v^\alpha\) of degree \(k\ge4\), reserve two factors with indices \(i,j\). Their product of moduli is at most \(E\) if equal, or \(E/2\) if different. For the remaining multiplicities \(\beta_\ell=\alpha_\ell-1_{\ell=i}-1_{\ell=j}\), weighted AM–GM gives
\[
 \prod_\ell |v_\ell|^{\beta_\ell}
 \ \le\ A^{k-2}\prod_{\beta_\ell>0}
       \left(\frac{\beta_\ell}{(k-2)w_\ell}\right)^{\beta_\ell},
 \qquad A=\sum_\ell w_\ell|v_\ell|.
\]
Minimize this coefficient bound for each monomial over eligible pairs \(i,j\), and sum the bounds for each degree. The coefficients of \(E A^{k-2}\), for \(k=4,5,6,7,8\), are respectively
\[
 \frac{60193}{2000},\quad\frac{8531299}{375000},\quad
 \frac{420163}{2560000},\quad
 \frac{5456361}{1562500000},\quad\frac{516989}{3240000000}.
\]
No higher degrees occur. Substitution of \(A=1/7\) and the cubic bound gives
\[
 |R-1-R_2|\le(33/10)E.
\tag{5}
\]

## 3. Quantitative contradiction

Suppose every \(g_t>-E/8\). Then any negative \(s_t\) has
\(-s_t\le |g_t-s_t|+E/8\). The RMS of these upper bounds is at most
\((37/20)A\sqrt E\) by (3) and \(\sqrt E\le(2/5)A\). Since \(\sum_t s_t=0\), either all \(s_t=0\), or the sum of positive \(s_t\)'s equals the sum of the at most four negative magnitudes. Hence the sum of positive squares is at most four times the sum of negative squares. It follows that
\[
 \frac15\sum_t s_t^2\le 5(37/20)^2 A^2 E .
\tag{6}
\]
The quadratic part satisfies
\[
 \Re R_2=15\left(2\cdot\frac15\sum_t s_t^2-E\right),\qquad |R_2|\le15E ,
\]
since \(\tfrac15\sum_t V_t^2=2(v_1v_4+v_2v_3)\) and
\(\tfrac15\sum_t|V_t|^2=E\). Combining (5), (6), and \(E\le(4/25)A^2\), we obtain
\[
\begin{aligned}
 |R|^2-1
 &\le 2\bigl(15(10(37/20)^2 A^2-1)+33/10\bigr) E
          +(15+33/10)^2 E^2\\
 &\le -(3381/2500)E<-(5/4)E .
\end{aligned}
\]
But \(|R|^2=\exp(2\sum_tg_t)>\exp(-5E/4)\ge1-5E/4\), a contradiction. Thus some \(g_t\le-E/8\), proving the bound. If all \(b_j=0\) every critical ratio is \(5/6\).

For sharpness of the deficit order, take real \(\epsilon\to0\) and \(v=(\epsilon,0,0,-\epsilon)\). All \(V_t=\epsilon(t-t^4)\) are purely imaginary, so (3) gives every \(g_t=O(\epsilon^2)\). The theorem gives a deficit at least a positive constant times \(\epsilon^2\) and this lower estimate on the ratios gives a deficit at most a constant times \(\epsilon^2\).

Replay with `python3 verify_smale_sextic_local.py`. It uses only exact rational arithmetic and the Python standard library. No covering of the remaining sextic parameter space is attached to this local claim.
