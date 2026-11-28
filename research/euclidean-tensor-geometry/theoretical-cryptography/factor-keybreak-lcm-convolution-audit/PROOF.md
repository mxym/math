# Exact audit of KeyBreak (C.59)

## 1. Printed statement

In Lemma C.12 the paper sets

\[
 r'=\frac r{\gcd(r,\ell)},\qquad
 s'=\frac s{\gcd(s,2)},\qquad
 L=\operatorname{lcm}(H_1r',H_2s')
\]

and prints

\[
\frac{rs}{2L}
\le
\frac{\sqrt{rs\sqrt{\gcd(r,\ell)\gcd(s,2)}}}
     {2\sqrt{H_1H_2}}.
\tag{printed C.59}
\]

## 2. Exact counterexample

Take a prime \(\ell>9\), and set

\[
H_1=H_2=1,\qquad r=\ell,\qquad s=3,\qquad t=3.
\]

Then \(r'=1\), \(s'=3\), and \(L=\operatorname{lcm}(1,3)=3\).
The divisibility conditions used immediately before (C.59) hold:
\(H_1r'\mid t\) and \(H_2s'\mid t\).

The printed inequality becomes

\[
\frac{\ell}{2}\le \frac{\sqrt3}{2}\ell^{3/4},
\]

equivalently \(\ell\le9\), contradicting \(\ell>9\).  The smallest
prime example is \(\ell=11\).  These conductors are compatible with
the surrounding setup: \(r=11\) divides the rational modulus \(33\),
and \(s=3\) divides the even algebraic modulus \(6\).

## 3. Correct inequality

Let

\[
a=\gcd(r,\ell),\qquad b=\gcd(s,2).
\]

Since an lcm is at least the geometric mean of its arguments,

\[
L
\ge \sqrt{(H_1r')(H_2s')}
=\sqrt{\frac{H_1H_2rs}{ab}}.
\]

Therefore

\[
\frac{rs}{2L}
\le
\frac{\sqrt{rsab}}{2\sqrt{H_1H_2}}
=
\frac{\sqrt{rs\,\gcd(r,\ell)\gcd(s,2)}}
     {2\sqrt{H_1H_2}}.
\]

Because \(b\le2\),

\[
\frac{\sqrt{rsab}}{2\sqrt{H_1H_2}}
\le
\frac{\sqrt{rsa}}{\sqrt{H_1H_2}}.
\]

This proves the repaired two-step inequality.

## 4. Mapping to (C.58)

If \(\ell\nmid r\), then \(a=1\).  After the convergent \(H_1,H_2\)
sums this contributes the ordinary product \(M_aM_b\).

If \(\ell\mid r\), then \(a=\ell\), since \(\ell\) is prime.  The
repaired inequality contributes one factor \(\sqrt\ell\).  Averaging
over the prime band gives precisely the second term printed in (C.58),

\[
\frac{\sqrt{2U_0}}{|J|}M_b
\sum_{r\ge U_0}\sqrt r\,a(r)\omega_J(r).
\]

Thus the prose after (C.59) has its divisibility sign reversed:
the exceptional \(\sqrt\ell\) occurs for \(\ell\mid r\).
The paper's own overview before the lemma also describes the exceptional
contribution as coming from \(\ell\mid r\).

## 5. Scope

This audit establishes an exact counterexample to the printed intermediate
inequality and a local repair whose output is already the displayed bound
(C.58).  It does not independently certify all of Lemma C.12, Theorem 3.1,
or either global factoring complexity theorem.
