# Proof and exact counterexample

Let \(G=(\mathbb Z/q\mathbb Z)^\times\). Character orthogonality gives
\[
\mathbf 1_{x=\ell y\text{ in }G}
=
\frac1{|G|}\sum_{\chi\in\widehat G}
\chi(x)\overline{\chi(\ell y)}
=
\frac1{|G|}\sum_{\chi}
\overline{\chi(\ell)}\chi(x)\overline{\chi(y)}.
\]
After stratifying by the common gcd \(\delta\), this is exactly the corrected
term
\[
\frac1{\varphi(q)}
\sum_\chi
\overline{\chi(\ell)}
\mathcal V_{1,\delta}(\chi)
\mathcal V_{2,\delta}(\overline\chi).
\]

By contrast, the printed term
\[
\frac1{\varphi(q)}
\sum_\chi
\overline{\chi(\ell)}\chi(x)\chi(y)
\]
equals \(\mathbf 1_{xy=\ell\text{ in }G}\).

## Minimal exact witness

Take \(q=10\), \(G=\{1,3,7,9\}\), \(\ell=3\), \(x=1\), and \(y=7\).
Then
\[
x\equiv \ell y\pmod {10}
\quad\text{because}\quad
3\cdot7\equiv1\pmod {10},
\]
but
\[
xy\equiv7\not\equiv3\pmod {10}.
\]
Therefore the target left side is \(1\), the printed character sum is \(0\),
and the corrected character sum is \(1\).

For real \(v_2\),
\[
\mathcal V_{2,\delta}(\overline\chi)
=\overline{\mathcal V_{2,\delta}(\chi)},
\]
so the magnitude and character-energy estimates used by the local
Cauchy–Schwarz step are unchanged.
