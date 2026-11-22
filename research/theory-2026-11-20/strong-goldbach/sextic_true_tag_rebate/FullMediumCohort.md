# Full removal of a true two-tag negative cohort on the .003 sextic residual

Keep the same fixed even target, target units, central interval,
normalization \(M\), and genuine sextic weights \(H,Q,G=H+Q\)
of [the original proof](Proof.md). Use the sharp \(b=.003\)
partition in [the explicit tiny-stop tradeoff](ExplicitTinyStopTradeoff.md):
\(J_b(n)=1_{P^-(n)>N^b}\), \(G_b=J_bG\). All pairings retain actual
coordinates \(x+y=N\). Let \(W\) be exactly \([-H]_+\) on the
following physical squarefree cohort and zero elsewhere:

- The two least primes are in distinct cells \((i/1000,(i+1)/1000]\)
  and \((j/1000,(j+1)/1000]\) of target-log angles, \(5\le i<j\),
  with upper endpoints \(u,v\) satisfying \(u+v\le .065\).
- With their actual product \(h\), the quotient \(n/h\) has exact rank
  \(1,2,\) or \(3\), and all its factors exceed \(N^z\) where
  \(D=.555-u-v,\ z=D/3\).

In particular \(W\) is supported on the actual \(b\)-rough arm,
is disjoint from \(Q\) on a single arm, and does not count the same
pair of least labels twice.

**Theorem.** The actual genuine prime opponent gives
\(\langle W,\Pi\rangle,\langle\Pi,W\rangle>.05846M+o(M)\).
The actual \(G_b+W\) is identically zero, not merely diminished,
on every selected negative row. At every sufficiently large even
target,
\[
 R_J\ge .257M+\langle G_b+W,G_b+W\rangle+o(M).                    \tag{1}
\]
There is no sign bound on the last covariance, nor any addition of
an earlier narrow-mark debit. Rows outside the specified cells, rows
where the quotient is insufficiently rough, and all unselected
ranks remain subject to the actual sharp score.

## 1. True .555 prime-opponent source and every higher quotient rank

Write \(u_-=u-.001,\ v_-=v-.001,\ T=1-u-v,\ T_+=1-u_--v_-\).
All selected cells have \(z\in(.1325,.187)\), \(z>v\), \(D/z=3\).
Let \(J_r(t)\) denote the ordinary prime-product simplex harmonic
from [the two-least-tag proof, §2](../halfzero_detector/TwoLeastPrimeRebate.md):
\(J_1(t)=1\) for \(t\ge1\), and
\(J_r'(t)=J_{r-1}(t-1)/(t-1)\) with \(J_r(t)=0\) for \(t<r\).
The underlying convolution is on the physical quotient labels;
there is no model of their correlation with the prime.

Apply the exact two-tag .555 Rosser lower with the same cells
and \(z=D/3\), as proved in
[that proof, §§1–2](../halfzero_detector/TwoLeastPrimeRebate.md).
The true prime source is the actual \(N-n\) in the corresponding
central interval (or its reflected orientation).
Its congruence is \(N\bmod h\ell\), with the two genuinely forced
primes inserted into the actual decreasing sieve list. The square
prefix tests, small-bank vector lower and .55525 packing are
unchanged; these 729 cells are a subset of the cells there.
At the normalized tag weights \(t_1t_2\) and two log weights,
the lower before the rank restriction is
\(10^{-6}(2/D)\log2+o(1)\). Subtract **every** actual quotient
rank \(r\ge4\) by the genuine 3.446 prime-opponent upper using
the true compact products. The resulting coefficient lower is
\[
 \frac1{10^6}\left[\frac2D\log2-
               \frac{3.446}{T}\sum_{r\ge4}J_r(T_+/z)\right].     \tag{2}
\]
In particular the actual residue remains \(N\); ordinary
below-root product BV has not been used for this lower.
The source, unit, square loss and proper prime-power details are
unchanged from the cited proof. The rank sum is finite since
\(T_+/z<8\); no actual higher quotient is dropped from the debit.

On the surviving true rows put \(a_1,a_2\) for the actual
**own-log** tag angles, and \(q=\sum_{p\mid n}(\log p/\log n)^2\).
Normalize \(-H\) by \((\log n)a_1a_2\). At rank 3 the quotient
is one giant, and this normalized weight is the positive
polynomial
\[
 w_3(a_1,a_2)=-\int_0^1\!\int_0^1 F''(a_1s+a_2t)\,ds\,dt .
\]
Since \(F''\) increases and is negative on the entire tag-sum
range \([0,.065]\), it is at least \(w_3(u,v)-o(1)>0\).
At rank 4 put \(q_4=u_-^2+v_-^2+T^2/2\);
the exact even formula gives lower
\((1680q_4-528)z(T-z)-o(1)>0\).
At rank 5 use the exact centered slice expression in
[the sextic proof, §2](Proof.md), the bounds
\(b_5(0)\le\sqrt{2/q}\) and \(\mathbb E|Y_5|\ge\sqrt{q/24}\),
and \(q\ge q_5-o(1)\), where \(q_5=u_-^2+v_-^2+T^2/3\).
This gives lower
\[
   \left(40320\sqrt{q_5/24}-1056\sqrt{2/q_5}\right)
                         z^2(T-2z)-o(1)>0.
\]
For the last two bounds the minimum product of two or
three angles with the given total and floor \(z\) occurs
at the extreme with all but one equal to \(z\).
All actual angles are perturbed by \(O_J(L^{-1})\) in the
own-log replacement. The three displayed minima are strictly
positive on every retained cell. Thus multiplying (2) by their
minimum proves the claimed lower on the **full** actual weight;
this uses a deweight only for that lower, not to define \(W\).
All error comparisons hold for true even targets in either
orientation.

## 2. Ordinary mass and genuine positive receiver for the full weight

Write \(C_5(q)=10080\sqrt q-1056/\sqrt q\), a positive increasing
concave function on the relevant \(q\). By the existing sextic
slice bound, the rank-five normalized full weight is at most
\(C_5(q)\) times the product of the three quotient angles.
The rank-three upper is \(w_3(u_-,v_-)\), which we denote \(w_3^+\).
Let
\[
 B_4=1680(u^2+v^2+T_+^2)-528,\quad V_-=z(T-z),\quad
 V_+=T_+^2/4.
\]
The rank-four normalized full weight is bounded by
\(\max_{V_-\le V\le V_+}V(B_4-3360V)\), denoted \(w_4^+\).
Retaining the sum and floor in the rank-five quotient gives upper
\[
 w_5^+=C_5(u^2+v^2+(T_+-2z)^2+2z^2)\,T_+^3/27
\]
by convexity for its sum of squares and AM--GM for its product.
These are pointwise bounds at the actual weights, up to the
harmless \(o(1)\) angle changes on compact cells.

For the positive receiver against any real nonnegative
compact angular product source \(Z\), open the actual two
factors \(p_1,p_2\), and upper-sift the genuine quotient
with level \(N^{D_0}\), \(D_0=.499-u-v\), and cut \(N^z\).
Because \(2<D_0/z<3\) here, the true coefficient on the cell
is \(2\,10^{-6}/D_0\) on the \(a_1a_2\log n\) weight.
There is no need to upper-sift to large actual factors.
The true modulus \(h\ell\le N^{.499}\) permits ordinary
below-root product BV with the exact reduced source and
target units, just as in the [true five-bank receiver]
(../halfzero_detector/CompensatedDebit.md). Both real tag primes
are omitted from the quotient sieve (their possible squares
are already physically excluded), so their outside density
is \(1/\varphi(h)\) and no repeated-prime local factor is
inserted. The nonunit alternatives for \(NhZ_{\rm int}\)
are absent; the source-label omissions of polynomial factors
affect only \(o(1)\) in the same true underlying model.
Use the maximum of \(w_3^+,w_4^+,w_5^+\) for this cell.
The reduced models on the two actual orientations yield
\[
 \langle Z,W\rangle/M\le U_W m(Z)+o(1),\qquad U_W<.52844 .        \tag{3}
\]

For the ordinary \(m(W)\) the tag factors \(a_1a_2\) cancel
both reciprocal harmonic denominators. The rank-three
bound per unit tag-cell area is \(w_3^+/T\).
At rank 4 the remaining product \(V\) cancels the two
quotient denominators; its remaining integral is on the
ordered smaller angle \(t\in[z,(1-a_1-a_2)/2]\).
A positive upper is the elementary integral
\[
 \int_z^{T_+/2}\bigl(B_4-3360t(T-t)\bigr)\,dt.
\]
In fact the integrand is positive throughout the enlargement
on these cells. At rank 5 the three-factor product cancels
their quotient denominators. With \(S_5=T_+-3z\) its
ordinary symmetric simplex volume is \(S_5^2/12\).
The simplex mean of the sum of squares of the three
quotient angles is at most \(3z^2+2zS_5+S_5^2/2\).
The concavity of \(C_5\) at these means gives upper
\[
  \frac{S_5^2}{12}\,
       C_5(u^2+v^2+3z^2+2zS_5+S_5^2/2).
\]
These are ordinary true-prime-product density bounds only;
all joint uses of \(W\) go through (2) or (3).
The [rational check](check_medium_full.py) verifies the sums
\(m(W)<.16921,\ U_W<.52844\) and prime lower \(>.05846\),
with integer outward evaluation of \(J_r\), square roots,
and log 2. The exact source rank floors ensure the same
compact \(W\) can be an opponent in the earlier short
transfers.

## 3. The exact same-score .003 signed accounting

Use \(T_0=I_bH\) and the true stopped decomposition of
[the .003 tradeoff](ExplicitTinyStopTradeoff.md),
\(T_0=A+V+E-D_*\). Here the latter \(D_*\) is the
earlier no-hit taper defect, not the cell level \(D\).
The exact transfer against this **same** compact \(W\) is
\[
 \langle A,W\rangle/M=c_A m(W)+o(1),\quad
       \langle E,W\rangle=o(M),\quad |c_A|<.228 .
\]
The two errors are genuine: \(|\langle V,W\rangle|\le
U_W(.009042)M+o(M)\) by (3) and the .003 ordinary remainder
bound, and \(|\langle D_*,W\rangle|\le .007445\,m(W)M+o(M)\)
by the true no-hit taper receiver. The \(V\) estimate uses
fixed physical floors and then the already certified limit,
not an independent synthetic distribution of its rows.
Similarly \(Q\) pairs with \(W\) at most by the minimum of
the two genuine upper bounds
\(\min(.852\,m(W),.01701\,U_W)M+o(M)\).
The \(W,W\) upper is \(U_W m(W)M+o(M)\).
All hold in both orientations.

Since \(G_b=H+Q-T_0\), use the ordinary signed \(H\)
transfer for this actual \(W\); it gives
\(\langle H,W\rangle/M=m(W)-\langle \Pi,W\rangle/M+o(1)\).
Thus the full debit for adding \(W\) to \(G_b\) is at most
\[
 2\Big[(1+.228+.007445)m(W)-.05846+
             \min(.852m(W),.01701U_W)+.009042U_W\Big]
                  +U_Wm(W)<.419 .
\]
The last strict bound uses the exact outward values in the
checker, which retains the slightly sharper prime minimum.
In the exact identity
\(\langle G_b,G_b\rangle=\langle G_b+W,G_b+W\rangle-
   \langle G_b,W\rangle-\langle W,G_b\rangle-\langle W,W\rangle\),
the last overlap is counted only once. Subtract this debit
from the same \(.676\) coefficient, proving (1). Because
the selected negative rows all have both tags above
\(N^{.005}\) and least factor below \(N^{.1251}\), the
original \(Q\) never occurs there, and the newly compensated
score replaces their complete old \(H\) by zero.
