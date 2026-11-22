# The two exact dimension-two sifting functions on the same zero-tag self-pair

Use the original fixed even \(N\), genuine unit pairing \(x+y=N\),
central interval \(J\), logarithm \(L=\log N\), \(M=|J|N\mathfrak S(N)\),
sharp score \(S=G_b+W,\ b=.003\), and the exact unchanged chamber
\(\mathcal Z_{.080}=\{P^-(x),P^-(y)>N^{.080}\}\) of
[the full zero-tag comparison](FullZeroTagAffineSelf.md).
No tag-count or angular support is moved.

**Proposition.** The actual signed sum on this same whole chamber satisfies
\[
                    \sum_{\mathcal Z_{.080}} S(x)S(y)
                                     >(4.251+o(1))M .
\]
This replaces the \(2.091M\) bound of the
[exact linear refinement](ExactLinearZeroTag.md), not adds to it.
The improvement \(2.160M\) changes no remaining exterior.
There is still no sign bound on that exterior and no binary lower.

## 1. The exact DHR upper and lower on the same physical fibre

Write \(a=.080\), \(V_0,\Pi,Q\) as in the full zero-tag proof.
Retain its hard divisor cap .4999 on each coordinate of the
raw \(V_0,V_0\) expansion, its \(4199\) actual angle cells of
width \(10^{-4}\) and the even unit atom, and the same real
squarefree restoration, own-log replacement and true ambient
cap error \(<.00000729M+o(M)\). The original opposite prime
bound \(<3.729964M+o(M)\) per orientation and the original
\(Q,H_0\) debit \(<.016840M+o(M)\) are unchanged.

On each real primitive fibre \(d r+e v=N\) the two genuine
roughness conditions, true target units, and multiplicative root
counts are exactly those in
[§2 of the full zero-tag proof](FullZeroTagAffineSelf.md#2-the-genuine-dimension-two-lower-and-upper-on-the-same-fibre).
For upper cell-sum \(\sigma\le .9998\) put
\[
                   D=N^{.999(1-\sigma)},\qquad
                   u=.999(1-\sigma)/a .
\]
On this same fibre use both **unweighted** DHR bounds from
[Diamond–Halberstam, Theorem 9.1](https://www.cambridge.org/core/books/abs/higherdimensional-sieve-method/sieve-method-for-1/5A00D3EA4C00B3B10D3CB8521D68D10C),
as explicitly stated in
[Franze–Kao, §4, (19)–(22)](https://arxiv.org/pdf/1812.11280).
The uniform dimension-two Euler product and
\(O(\sum_{\ell\le D}8^{\omega(\ell)})\) actual remainder
bound with a fixed strict power reserve are as in that proof.
Use the lower only with \(u>\beta_2\) (else zero) and
the DHR upper only with \(u>\alpha_2\), so \(D\ge N^a\)
wherever either new bound is used. For all other upper
pieces, and whenever better, keep the original genuine
Selberg upper with support exponent \(.499(1-\sigma)\).
This retains its validity down to the hard cap with no
invocation of the DHR upper at an inadmissibly small ratio.

The normalized lower and upper coefficients from DHR are
\(e^{-2\gamma} f_2(u)/a^2\), \(e^{-2\gamma}F_2(u)/a^2\),
in the scale \(X\mathfrak S(N)/L^2\) on the actual fibre of
length \(X=|J|N/(de)\). The upper is applied on the negative
Möbius pairs and the lower on the positive pairs. Thus this
only strengthens the original coefficient calculation (6)
on real counts *before* summation over the exact label signs.
The step does not rely on independent prime-factor patterns
of the actual pair.

## 2. Outward integration through the actual changes of branch

Use
\[
 A(u)=u^2 e^{-2\gamma}F_2(u),\qquad
 B(u)=u^2 e^{-2\gamma}f_2(u),\qquad
 \mathcal G(w)=\int_0^w\rho_2(t)\,dt .
\]
By the exact normalization of \(\sigma_2\) in
[Booker–Browning, Theorem 3.1](https://arxiv.org/pdf/1511.00601)
and the prior proof,
\[
 \begin{array}{ll}
 A(u)=u^2/\mathcal G(u/2) & (0<u\le\alpha_2),\\
 A'(u)=2uB(u-1)/(u-1)^2 & (u>\alpha_2),\\
 B(u)=0 & (0<u\le\beta_2),\\
 B'(u)=2uA(u-1)/(u-1)^2 & (u>\beta_2).
 \end{array}
\]
Both \(A\) and \(B\) are nonnegative and nondecreasing:
for the initial \(A\) this follows directly from
\((u^{-2}\sigma_2(u))'\le0\), and for their subsequent
parts it follows from the delay equations. In addition
\(f_2\) is nondecreasing and \(F_2\) is nonincreasing.
The [Booker–Browning certified interval table](https://arxiv.org/src/1511.00601v2/anc/dhr.html)
puts \(\alpha_2\) in \((5.3577,5.3578)\) and \(\beta_2\)
in \((4.2664,4.2665)\).

Use the mesh \(u=j/10^4\). Up to the lower endpoint
\(\alpha_-\) of its switch cell, enclose \(A\) by the
original certified upper and lower \(\mathcal G\) table,
rounding the argument \(u/2\) respectively up and down
as needed. At the other endpoint \(\alpha_+\), use
\[
      A(\alpha_-)\le A(\alpha_+)
         \le (\alpha_+/\alpha_-)^2 A(\alpha_-).
\]
The left inequality uses monotonicity of \(A\), the right
monotonicity of \(F_2\). Thus no extrapolation through
the unknown branch inside that cell occurs. In the
\(\beta_2\) switch cell take the lower increment of \(B\)
to be zero, and the upper from the positive derivative
bound on the entire cell, valid on the portion where
the derivative is nonzero. The delayed argument there
is below \(\alpha_-\), so the initial \(A\) formula
applies. In every other delay cell, use the interval
of the monotone delayed numerator between its two
endpoint enclosures, and the positive squared delayed
denominator over the full cell. When the delayed
argument is wholly on the initial \(A\) branch one
may use its simpler \(A(w)/w^2=1/\mathcal G(w/2)\)
form. All referenced delayed entries are already
available.

For a physical \(u\), use the downward-rounded mesh
argument for **both** \(f_2\) in a lower and \(F_2\)
in an upper, by their opposite monotonicities.
Use the lower on \(f_2\) only when the rounded argument
is at least the upper endpoint of the \(\beta_2\) cell;
use the DHR upper on \(F_2\) only from the upper endpoint
of the \(\alpha_2\) cell. The remainder of each upper is
still the old positive Selberg bound. The outer interval
evaluation, even/odd label densities, literal cell
geometry, and true rank bound have not changed.
Use the original ambient coefficient for the cap error.

Run:

    python3 -OB check_exact_dhr_zero_tag.py

The [checker](check_exact_dhr_zero_tag.py) locks the
original affine checker by hash and reuses its genuine
ordinary label density and \(\mathcal G\) enclosures.
Only the two fibre functions change in the outer
double sum. The resulting actual raw lower is
\(>11.745M+o(M)\) after the same hard cap error.
Keeping the actual nonnegative \(R_J,Q\times Q\) terms
discarded as before, the final lower is
\[
 \big(11.745-2(3.729964)-2(.016840)+o(1)\big)M
                                     >(4.251+o(1))M .
\]
The old tagged masks remain disjoint exactly as before;
no other numerical credit is changed.
