# Removing the logarithmic loss in Whitmore's Singmaster bound

Research note, 27 November 2026. Let \(N(t)\) count pairs of integers \((n,m)\) with \(\binom nm=t\), for \(t\ge2\), retaining both sides of Pascal's triangle.

**Theorem.** For \(s=\log\log\log t\),
\[
           N(t)\le(\log t)^{\,1/2+(115/8+o(1))/s}
           \qquad (t\to\infty).
\]
In particular the error above the exponent \(1/2\) is \(O(1/\log\log\log t)\), instead of \(O(\log\log\log\log t/\log\log\log t)\).

This directly answers the technical question in Remark 1.5 of [Ben Whitmore, *An improved upper bound on the number of representations of an integer as a binomial coefficient*, Hexagon 2611.00106v1](https://hexagonmath.org/pdf/2611.00106v1). Whitmore's Theorems 1.2–1.3 already establish the leading \(1/2+o(1)\) exponent. His original Section 5 proof controls a short-circle integral using the low-degree complement of a coefficient tail. We instead estimate the tail itself at a radius comparable to the total dimension. The larger numerator cost is still \(e^{O(kT)}\) once the spacing of the poles is retained in the denominator; the gain in each coefficient exactly absorbs the derivative factorials. The remainder of the binomial argument uses Whitmore's interpolation and determinant estimates and the published [Matomäki–Radziwiłł–Shao–Tao–Teräväinen interior theorem](https://arxiv.org/abs/2106.03335). The leading exponent \(1/2\) and the Singmaster conjecture itself are not settled here.

## 1. Sharper single-mode projection

Use the notation of Whitmore's Lemma 5.1. Let \(k\ge1\), \(T\ge10(k+1)^2\), and let \(\nu_0,\ldots,\nu_k\ge1\) be integer multiplicities. Put \(\nu=\sum_h\nu_h\), and assume \(\nu\le(4k+3)T\) and \(\max_h\nu_h\le5T\). Define
\[
 G_0(z)=\sum_{h=0}^k R_h(z)e^{hTz},\quad
 \deg R_h<\nu_h,\quad
 m_0=\max_{|z|\le1/2}|G_0(z)|.
\]
Then, for all \(|z|\le4\) and \(0\le j\le k\),
\[
                       |R_j(z)e^{jTz}|\le e^{45(k+1)T}m_0.
 \tag{1}
\]
The bound is asserted in the parameter range used by the zero estimate, not for unrestricted \(T\) and multiplicities.

Indeed, set
\[
 \chi(w)=\prod_{h=0}^k(w-hT)^{\nu_h}=\sum_{\ell=0}^\nu a_\ell w^\ell,\qquad
 \chi_i(w)=\sum_{\ell>i}a_\ell w^{\ell-i-1},\qquad y_i=G_0^{(i)}(0).
\]
The Laplace transform, initially in \(\operatorname{Re}w>kT\), is
\[
 Y(w)=\frac{\sum_{i=0}^{\nu-1} y_i\chi_i(w)}{\chi(w)}.
\]
This follows by integrating the constant-coefficient equation \(\chi(d/dz)G_0=0\) along the positive real axis and collecting the initial derivatives. Alternatively the transform of \(z^p e^{hTz}\) is \(p!/(w-hT)^{p+1}\). That last representation also shows that the integral of \(e^{zw}Y(w)/(2\pi i)\) on \(C_j=\{|w-jT|=T/2\}\) is exactly \(R_j(z)e^{jTz}\).

Let \(U=16(k+1)T\). It is at least \(2\nu\) and at least \(\max_{w\in C_j}|w|\). Directly from the high-degree tail and the coefficient majorant \(\prod_h(w+hT)^{\nu_h}\), for \(w\in C_j\),
\[
 |\chi_i(w)|\le U^{-i-1}\prod_{h=0}^k(U+hT)^{\nu_h}.
\]
On the same circle, \(|w-hT|\ge (T/2)\max(1,|h-j|)\). Since \(U+hT\le17(k+1)T\), the ratio of the two products is bounded by
\[
 \frac{\prod_h(U+hT)^{\nu_h}}{|\chi(w)|}
 \le \left(\frac{[34(k+1)]^{k+1}}{j!(k-j)!}\right)^{\max_h\nu_h}
 \le e^{40(k+1)T}.
 \tag{2}
\]
Every factor used in raising to \(\max_h\nu_h\) is at least 1. For the final bound, \(j!(k-j)!\ge k!/2^k\ge (k/(2e))^k\), so the parenthesized ratio is at most \(34(k+1)(136e)^k\le e^{8(k+1)}\), and \(\max_h\nu_h\le5T\).

Cauchy's estimate gives \(|y_i|\le i!2^i m_0\). Combining it with (2) yields
\[
 |Y(w)|\le e^{40(k+1)T}\frac{m_0}{U}\sum_{i<\nu} i!\,(2/U)^i
 \le e^{40(k+1)T}\frac{\nu m_0}{U},
\]
because \(U\ge2\nu\). For \(|z|\le4\) the remaining factor \(|e^{zw}|\) is at most \(e^{4(k+1)T}\) on \(C_j\). Its length divided by \(2\pi\) is \(T/2\); \((T/(2U))\nu\le\nu\le e^T\) in the stated range. This proves (1). The loss \(\max(1,(4\nu/T)^\nu)\) from the original estimate is absent: the numerator is evaluated at \(U\), although the contour and its exponential cost remain small.

## 2. The replacement parameter in the zero estimate

In Whitmore's Proposition 6.1 put
\[
                             a(k)=10e^{23(k+1)}
\]
in place of \(a_0(k)\), including the definitions of \(T=L/(a(k)x_0)\) and of the scaled windows. The following check records why the bounds in Sections 6–7 still apply, without assuming Theorem 1.3 for an unproved new parameter.

In his proof of Proposition 6.1 the exponential polynomial has \(\nu_0=d+k+1\) and \(\nu_h=d+k+J+1\) for \(h\ge1\), with \(J=\lceil2T\rceil\), \(d\le2T\) and \(T\ge10(k+1)^2\). These give \(\nu\le(4k+3)T\) and \(\max_h\nu_h\le5T\) as required in §1. Replace his component constant \(C_b\) by
\[
                  C_b'=\min\{C_b,e^{45(k+1)T}\}.
\]
Both bounds apply to the same components. With his Taylor error \(\delta'=(1/5)(10/a(k))^{J+1}\), we have
\[
                 2kC_b'\delta'\le (2k/5)e^{-(k+1)T}\le e^{-T}.
\]
This is precisely the needed substitute for the old (6.5)–(6.6) implication. Every remaining upper estimate in the zero argument, including the near-zero bound (6.8) and the Lagrange error bound (6.9), may continue to use the **old** upper bound on \(C_b'\). The total-function growth bound \(C_a\) in Lemma 5.1(a) is untouched. The other lower bounds on the window parameter used in that proof, including \(a(k)\ge40(4k+3)\), all hold. Thus the conclusion \(|Z|\le17(4k+3)T\) with the original \(\delta_5=\exp(-1000(k+1)^2(T+1)\log(6x_0+6))\) holds with the new \(a(k)\).

For clarity, the transfer in Section 7 uses \(L=\log t\),
\[
 \theta=\frac{k+1}{2k+1},\quad \alpha=\frac{k}{k+1},\quad
 M_0=L^\theta,\quad M_1=\frac{L}{(\log L)^{7/5}},
 \qquad
 r_M=(M/2)^\alpha e^{-2a(k)-1}.
\]
Assume \(\log L\) is sufficiently large and
\[
                         40(k+1)^2a(k)\le(\log L)^{2/5}.
 \tag{3}
\]
The interpolation and determinant steps (Propositions 3.1 and 4.1) are unchanged. In Lemma 7.2, for \(M\in[M_0,M_1]\), integer \(x_0\in[M,2M]\), and \(d=\lfloor L/(a(k)M)\rfloor\), their application uses \(d\le2T\), \(d+1>L/(a(k)M)\), and \(T\ge10(k+1)^2\), all as in the original proof by (3). The determinant radius comparison uses \(\ell=L/x_0\le L/M<a(k)(d+1)\); the tolerance comparison (7.2) uses only \(k+1\le(\log L)^{1/5}\), also from (3). The numerical lower bounds \(a(k)\ge2(k+1)\), \(a(k)\ge17(4k+3)\) ensure both cases of the argument give at most \(L/M\) half-triangle solutions per window. Finally (3) bounds \(a(k)\) from above, ensuring \(r_M\ge2\) for all sufficiently large \(\log L\). These are the appearances of the replaced parameter in the window and summation argument.

As in that section, the range \(m\le M_0\) has at most \(M_0\) half-triangle solutions, because each \(m\) determines at most one \(n\). On each dyadic interval \([M,2M]\) in the middle range, \(O(M/r_M)\) windows and the bound \(L/M\) give at most \(6e^{2a(k)+1}LM^{-\alpha}\) solutions. The sum is bounded by \(21e^{2a(k)+1}L^\theta\), using \(1-\theta\alpha=\theta\). The interior theorem gives at most two further solutions with \(m\ge M_1\), by Whitmore's Lemma 7.1, which does not use \(a_0\). Doubling to restore the whole triangle gives the replacement of his fixed-\(k\) bound:
\[
                       N(t)\le50e^{2a(k)+1}L^{(k+1)/(2k+1)}
 \quad\text{under (3) for sufficiently large }\log L .
 \tag{4}
\]

Now choose \(k+1=\lfloor((2/5)s-3\log s-\log400)/23\rfloor\) for sufficiently large \(s=\log\log L\). Then \(k+1\le s\), and \(\log(40(k+1)^2a(k))=\log400+2\log(k+1)+23(k+1)\le(2/5)s\), so (3) holds. Moreover
\[
 \frac{k+1}{2k+1}=\frac12+\frac1{4k+2}
            =\frac12+\frac{115/8+o(1)}{s}.
\]
By (3), \(\log(50e^{2a(k)+1})=O((\log L)^{2/5})=o(\log L/s)\); the prefactor in (4) does not change the claimed exponent. This proves the theorem. The numerical coefficient \(115/8\) is not optimized.

## Verification scope

[verify_factor_singmaster_projection.js](verify_factor_singmaster_projection.js) checks exact small instances of the Laplace numerator identity, the coefficient-tail majorant at points on the pole circles, and the factorial-product estimate. These finite checks do not replace the complex-analytic argument. This is a written proof using the cited published interior theorem and Whitmore's interpolation and determinant work; it is not a new Lean kernel verification.
