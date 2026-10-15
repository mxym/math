# Exact pure envelope for every linear-order parameter c at least one

Yongxian Zhang (张永贤), School of Computer Science and Engineering, South China University of Technology. 15 October2026. No external funding. OpenAI AI assistants assisted analysis and writing. Original material all rights reserved; credited results retain their attribution.

AUTHOR VERSION: complete ordinary scalar proof awaiting an independent full read. No Lean coverage, external human peer review, priority certificate or new-major-conjecture count is claimed. The full intermediate-c phase diagram is still open here.

## Credited profile and exact statement

Use the continuous scalar profile proved for original complex all-global-unitary APPT densities in `research/appt-growing-renyi/LINEAR_ORDER_VARIATIONAL.md`, especially L1 and the exact mixing-parameter elimination L20:

\[
G(L)=\frac{2L^2}{3(2-L)},\quad
B(c,L,h)=e^{-cLh}[1+h(e^{cL}-1)],\quad
P(c,L,h)=e^{-c[Lh+G(L)]},\quad
F(c,r;L,h)=B+rP,
\]

for `c>0,r>=0,0<=L<=2,0<=h<=1`, with `P(c,2,h)=0`. At `L=0`, `B=P=1` and `F=1+r`. Let `F_*` be the maximum on this compact parameter rectangle. Retain

\[
b(t)=\frac{e^t-1}{t}\exp\!\left[-1+\frac{t}{e^t-1}\right],\qquad
h_b(c)=\frac1{2c}-\frac1{e^{2c}-1}.
\]

The already credited pure-bulk optimization says `max B=b(2c)>1`, uniquely at `(L,h)=(2,h_b(c))`.

**Theorem D1.** For every real `c>=1` and every real `r>=0`,

\[
F_*(c,r)=\max\{b(2c),1+r\}.
\]

Writing `r_0=b(2c)-1>0`, its complete scalar argmax set is

\[
\begin{cases}
\{(2,h_b(c))\},&0\le r<r_0,\\
\{(2,h_b(c))\}\ \cup\ (\{0\}\times[0,1]),&r=r_0,\\
\{0\}\times[0,1],&r>r_0.
\end{cases}
\]

In particular, there are no hidden interior-width ties when `c>=1`. The constant1 is a proved sufficient bound, not a claim about the sharp final mixed-phase boundary or its uniqueness. The argument below uses L20 directly and does not depend on the author's separate, not-yet-reviewed small-c or c>=10 draft.

## Elementary one-variable facts

For `t>0` put

\[
q(t)=\frac{t}{e^t-1},\quad
s(t)=\frac{e^t}{e^t-1}-\frac1t,\quad
g(t)=\log b(t)=-\log q(t)-1+q(t).
\]

Then `0<q(t)<1`, `q'=-s q`, and

\[
g'(t)=s(t)(1-q(t))>0.\tag{D2}
\]

Here `s(t)>1/2`. To see this without an asymptotic approximation, multiply `s-1/2` by the positive number `2t(e^t-1)`. The result is

`H(t)=(t-2)e^t+t+2`.

It has `H(0)=H'(0)=0` and `H''(t)=t e^t>0` for `t>0`; hence `H(t)>0`.

The function `g` is convex. Indeed it is the pointwise maximum, over `h in[0,1]`, of

\[
\log\mathbb E e^{t(X-h)},\qquad X\text{ Bernoulli}(h).
\]

Each is a log moment-generating function and is convex. This maximum equals `log b(t)` by the credited bulk calculation. The explicit formula makes it differentiable for `t>0`. Consequently, for `0<k<K`,

\[
g(K)-g(k)\ge(K-k)g'(k).\tag{D3}
\]

This uses the tangent inequality for a differentiable convex function, rather than an unsupported assertion about a derivative of an arbitrary increasing function.

## No interior maximum at the bulk height when c is at least one

Fix `c>0`, let `K=2c` and set `r=r_0=b(K)-1`. Both width endpoints have maximum value `b(K)`: width0 gives it for every `h`, and width2 gives it only at `h_b(c)`.

Suppose a global maximizer has `0<L<2`. Its value is at least `b(K)`. At either mixing endpoint `h=0` or `h=1`, one has `B=1` and `P<1`, so

`F=1+r_0 P<1+r_0=b(K)`.

Thus its mixing parameter lies strictly in `(0,1)`. Put

\[
k=cL\in(0,K),\qquad u=K-k>0,\qquad
a(k)=\frac{2k^2}{3(K-k)}.
\]

The equality `a(k)=cG(L)` is exact. By L20, the unique interior mixing maximizer and its value are

\[
h_*(k)=\frac1k-\frac{1+r_0 e^{-a(k)}}{e^k-1},\qquad
\log F(c,r_0;L,h_*(k))=g(k)+T(k),
\]

where

\[
T(k)=r_0q(k)e^{-a(k)}>0.
\]

Since `h_*(k)` is interior at the putative maximum, it stays interior on a neighborhood. The displayed smooth optimized formula is therefore valid there, and the global maximum at an interior width satisfies

\[
0=g'(k)+T'(k)
=g'(k)-T(k)[s(k)+a'(k)],\qquad
a'(k)=\frac{2k(2K-k)}{3u^2}.\tag{D4}
\]

The maximum reaches at least the bulk height, so `g(k)+T(k)>=g(K)`. Combining this with D3 and D4 yields

\[
T(k)\ge g(K)-g(k)\ge u g'(k)
=u T(k)[s(k)+a'(k)].
\]

Cancel the strictly positive `T(k)` to obtain

\[
1\ge u[s(k)+a'(k)].\tag{D5}
\]

But `0<u<K` and `s(k)>1/2` imply

\[
\begin{aligned}
u[s(k)+a'(k)]
&>\frac u2+\frac{2(K^2-u^2)}{3u}\\
&=\frac{2K^2}{3u}-\frac u6\\
&=\frac K2+\frac{(K-u)(4K+u)}{6u}
>\frac K2.
\end{aligned}\tag{D6}
\]

Therefore every such interior global maximizer necessarily has `K<2`, equivalently `c<1`. For `c>=1` it is impossible. Compactness guarantees a global maximum; since no interior-width maximum exists, and the width endpoints have maximum exactly `b(K)`, this proves the value and all ties at `r=r_0`. It excludes interior points with value strictly greater than bulk and interior points tied with bulk: either would be, or would force, an interior global maximum.

## Extension to every r, retaining equality cases

For `0<=r<r_0`, put `t=r/r_0<1`. Affinity in `r` gives, for every scalar competitor,

\[
F(c,r;L,h)=(1-t)B(c,L,h)+tF(c,r_0;L,h)\le b(K).
\]

The bulk point attains the bound. Equality requires `B=b(K)` since `1-t>0`, and therefore forces its unique maximizer `(2,h_b(c))`.

For `r>r_0`,

\[
F(c,r;L,h)-(1+r)
=[F(c,r_0;L,h)-b(K)]+(r-r_0)(P-1)\le0.
\]

At positive width, `P<1`, so equality is impossible. At width0 equality always holds. This proves the remaining branches and completes D1. No finite grid, root search or local ansatz is used.

## Original quantum scope and remaining question

The scalar profile remains the already proved leading profile of actual complex PSD trace-one densities that are PPT after **every** global unitary. For sequences of integers `2<=m<=n`, `m->infinity`, and real orders `alpha>1` with `alpha/m->c>=1` and `3^alpha/(mn)->r<infinity`, L1 and D1 give the corresponding optimized moment limit `max{b(2c),1+r}`. The complete actual near-optimizer criterion is obtained from the existing theorem S by replacing its full scalar argmax set with the explicit set in D1 and retaining both the middle spread loss `J` and the actual peak loss. Those physical losses cannot be removed by a scalar calculation.

This does not assert an exact finite-dimensional optimizer, uniqueness of an eigenbasis, absolute separability, full all-order spectral rigidity, a sharp c threshold, absence of mixed-phase islands in `0<c<1`, or Lean formalization. Those remaining intermediate-parameter questions continue as the active depth target.
