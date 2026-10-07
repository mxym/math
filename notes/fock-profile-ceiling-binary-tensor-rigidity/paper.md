# Fock-profile completion and a certified ceiling for binary tensor rigidity

Research note, 7 October 2026.

This is an additive continuation of
notes/boundary-profile-binary-tensor-rigidity.  The earlier note turns every
fixed finite reflected edge profile into an asymptotic lower bound for the
sharp binary tensor-rigidity constants.  Here we analyze the resulting
Gaussian/Fock variational problem itself.  We prove compactness and
attainment in its natural infinite-dimensional completion, improve the
certified lower constant, and give an exact dual certificate placing the
entire profile mechanism in a narrow interval.

No claim is made that this variational problem describes every asymptotically
extremal binary tensor.

## 1. Profile functional

Let \(\ell^2=\ell^2(\mathbb N_0;\mathbb R)\).  For
\(a=(a_0,a_1,\ldots)\in\ell^2\), put

\[
 S(a)=\sum_{k\ge0}a_k^2,\qquad
 H(a)=\sum_{k\ge0}k\,a_k^2.
\]

The form domain of the number operator is

\[
 \mathcal H_1=\{a\in\ell^2: H(a)<\infty\}.
\]

For \(a\in\ell^2\), define the Fock function

\[
 A_a(x)=\sum_{k\ge0}\frac{a_k}{\sqrt{k!}}x^k .
\]

Cauchy--Schwarz gives

\[
 |A_a(x)|\le \sqrt{S(a)}\,e^{x^2/2},
\]

so the series converges for every real \(x\).  Set

\[
 \Phi_a(x)=e^{-x^2}\bigl(A_a(x)^2+A_a(-x)^2\bigr),
 \qquad
 M(a)=\sup_{x\in\mathbb R}\Phi_a(x).
\]

For \(S(a)>0\) and \(0<H(a)<\infty\), define

\[
 Q(a)=\frac{2S(a)-M(a)}{4\sqrt{S(a)H(a)}}.
 \tag{1}
\]

The functional is invariant under nonzero real scaling of \(a\).

The finite-profile theorem from the preceding note states that if \(a\) has
finite support then the reflected boundary tensors associated with \(a\)
satisfy

\[
 \liminf_{p\to\infty}\frac{C_p^2}{\sqrt p}\ge Q(a).
 \tag{2}
\]

We therefore define

\[
 \Lambda_{\rm prof}
 =\sup\{Q(a):a\ne0,\ a\text{ finitely supported},\ H(a)>0\},
 \qquad
 \kappa_{\rm prof}=\sqrt{\Lambda_{\rm prof}}.
 \tag{3}
\]

Our main quantitative result is

\[
 \boxed{
 \left(\frac{6238973}{10^7}\right)^2
 <\Lambda_{\rm prof}\le\frac{779}{2000}}
 \tag{4}
\]

and hence

\[
 \boxed{
 0.6238973<\kappa_{\rm prof}
 \le\sqrt{\frac{779}{2000}}
 =0.624099351065\ldots .}
 \tag{5}
\]

The upper endpoint in (5) applies only to this profile mechanism.  It is not
an upper bound for the true constants \(C_p/p^{1/4}\).

## 2. Coherent-state form and continuity

For \(x\in\mathbb R\), let

\[
 v_x=\left(e^{-x^2/2}\frac{x^k}{\sqrt{k!}}\right)_{k\ge0}.
\]

The exponential series gives \(\|v_x\|_2=1\).  Let

\[
 K_x=v_x\otimes v_x+v_{-x}\otimes v_{-x}.
\]

Then

\[
 \Phi_a(x)=\langle a,K_xa\rangle.
 \tag{6}
\]

This immediately yields \(0\le M(a)\le2S(a)\).

### Lemma 2.1. Uniform continuity in the profile

For all \(a,b\in\ell^2\),

\[
 |M(a)-M(b)|
 \le 2(\|a\|_2+\|b\|_2)\|a-b\|_2.
 \tag{7}
\]

#### Proof

For either sign of \(x\),

\[
 \left|
 \langle a,v_{\pm x}\rangle^2-
 \langle b,v_{\pm x}\rangle^2
 \right|
 \le(\|a\|_2+\|b\|_2)\|a-b\|_2.
\]

Add the two estimates and take the supremum over \(x\).  ∎

### Lemma 2.2. The supremum defining \(M(a)\) is attained

If \(a\ne0\), then \(\Phi_a(x)\to0\) as \(|x|\to\infty\), and consequently
\(M(a)>0\) is attained.

#### Proof

For a finitely supported profile, the assertion is immediate because
\(e^{-x^2/2}A_a(x)\) is a Gaussian times a polynomial.  For general
\(a\in\ell^2\), truncate after \(m\) coordinates.  The coherent-state
bound gives

\[
 \left|e^{-x^2/2}
 \bigl(A_a(x)-A_{a^{[m]}}(x)\bigr)\right|
 \le\|a-a^{[m]}\|_2
\]

uniformly in \(x\).  Let \(m\to\infty\) after taking \(|x|\to\infty\).
Continuity follows from norm continuity of \(v_x\).  A nonzero entire
function \(A_a\) is not identically zero, so \(\Phi_a\) is positive
somewhere.  ∎

## 3. Completion, compactness and attainment

### Theorem 3.1. Finite profiles have the same supremum as the form domain

\[
 \Lambda_{\rm prof}
 =
 \sup\{Q(a):a\in\mathcal H_1,\ S(a)>0,\ H(a)>0\}.
 \tag{8}
\]

#### Proof

Only one inequality needs proof.  Let \(a\in\mathcal H_1\) with
\(S(a),H(a)>0\), and truncate it at order \(m\).  Then

\[
 S(a^{[m]})\to S(a),\qquad
 H(a^{[m]})\to H(a).
\]

Lemma 2.1 gives \(M(a^{[m]})\to M(a)\).  Hence
\(Q(a^{[m]})\to Q(a)\).  ∎

The next elementary estimates are useful twice.  Normalize \(S(a)=1\).
Since \(x=0\) gives \(\Phi_a(0)=2a_0^2\),

\[
 2-M(a)
 \le2(1-a_0^2)
 =2\sum_{k\ge1}a_k^2
 \le2H(a).
 \tag{9}
\]

Also \(2-M(a)\le2\).  Therefore

\[
 Q(a)\le
 \min\left\{\frac{\sqrt{H(a)}}2,\frac1{2\sqrt{H(a)}}\right\}
 \le\frac12.
 \tag{10}
\]

### Theorem 3.2. The completed profile problem has a maximizer

There exists \(a_*\in\mathcal H_1\) with \(S(a_*)=1\),
\(0<H(a_*)<\infty\), and

\[
 Q(a_*)=\Lambda_{\rm prof}.
 \tag{11}
\]

In particular, the supremum in (8) is an actual maximum.

#### Proof

The explicit profile in Section 4 shows \(\Lambda_{\rm prof}>0\).
Choose \(a^{(j)}\) with \(S(a^{(j)})=1\) and
\(Q(a^{(j)})\to\Lambda_{\rm prof}\).  For all sufficiently large \(j\),
(10) gives upper and lower bounds

\[
 c\le H(a^{(j)})\le C
 \tag{12}
\]

with positive finite constants independent of \(j\).  Indeed,
\(Q\le\sqrt H/2\) and \(Q\le1/(2\sqrt H)\).

The upper moment bound gives uniform \(\ell^2\) tails:

\[
 \sum_{k>K}|a_k^{(j)}|^2
 \le\frac{H(a^{(j)})}{K+1}
 \le\frac C{K+1}.
 \tag{13}
\]

Thus the sequence is precompact in \(\ell^2\).  Pass to a subsequence such
that

\[
 a^{(j)}\to a_*\quad\text{in }\ell^2,
 \qquad
 H(a^{(j)})\to\bar H.
\]

Then \(S(a_*)=1\), \(H(a_*)\le\bar H\) by lower semicontinuity, and
\(M(a^{(j)})\to M(a_*)\) by Lemma 2.1.  Write
\(N_*=2-M(a_*)\).  Since

\[
 \Lambda_{\rm prof}
 =\lim_j\frac{2-M(a^{(j)})}{4\sqrt{H(a^{(j)})}}
 =\frac{N_*}{4\sqrt{\bar H}}>0,
\]

we have \(N_*>0\).  Hence \(H(a_*)\ne0\): otherwise \(a_*=\pm e_0\),
which would give \(M(a_*)=2\).  Consequently

\[
 Q(a_*)=\frac{N_*}{4\sqrt{H(a_*)}}
 \ge\frac{N_*}{4\sqrt{\bar H}}
 =\Lambda_{\rm prof}.
\]

The reverse inequality follows from Theorem 3.1, so equality holds.  ∎

A useful consequence is that the nonquantitative strict inequality
\(\Lambda_{\rm prof}<1/2\) follows already from attainment and (10).
Indeed equality in both estimates in (10) would force \(H=1\) and
\(2-M=2\), hence \(M=0\), impossible for a nonzero profile.  Section 5
gives the much stronger quantitative ceiling \(779/2000\).

## 4. An exact five-term lower certificate

We now improve the preceding three-term lower profile.  It is convenient to
specify the polynomial coefficients

\[
 c_0=1,\quad
 c_1=\frac{750737}{500000},\quad
 c_2=-\frac{232953}{500000},\quad
 c_3=-\frac{25879}{1000000},
\]
\[
 c_4=-\frac{2229}{1000000},\qquad
 c_5=-\frac{163}{1000000}.
 \tag{14}
\]

Use the actual Fock profile

\[
 a_k=c_k\sqrt{k!}\quad(0\le k\le5),
 \qquad a_k=0\quad(k>5).
 \tag{15}
\]

Then

\[
 A_a(x)=
 1+\frac{750737}{500000}x
 -\frac{232953}{500000}x^2
 -\frac{25879}{1000000}x^3
 -\frac{2229}{1000000}x^4
 -\frac{163}{1000000}x^5.
 \tag{16}
\]

Exact arithmetic gives

\[
 S=\frac{1846350870529}{500000000000},
 \qquad
 H=\frac{1567622847647}{500000000000}.
 \tag{17}
\]

Put \(y=x^2\), and write \(A_a(x)=E(y)+xO(y)\).  Then

\[
 A_a(x)^2+A_a(-x)^2=2P(y),
 \qquad
 P(y)=E(y)^2+yO(y)^2.
\]

For (16),

\[
\begin{aligned}
P(y)={}&1
+\frac{330653043169}{250000000000}y
+\frac{16862138693}{125000000000}y^2\\
&+\frac{451450213}{200000000000}y^3
+\frac{2680999}{200000000000}y^4
+\frac{26569}{1000000000000}y^5.
\end{aligned}
 \tag{18}
\]

All coefficients are positive.  The derivative of \(e^{-y}P(y)\) has
the sign of \(q(y)=P'(y)-P(y)\), namely

\[
\begin{aligned}
q(y)={}&
\frac{80653043169}{250000000000}
-\frac{263204488397}{250000000000}y\\
&-\frac{128125356349}{1000000000000}y^2
-\frac{440726217}{200000000000}y^3\\
&-\frac{265443}{20000000000}y^4
-\frac{26569}{1000000000000}y^5.
\end{aligned}
 \tag{19}
\]

Thus \(q\) is strictly decreasing on \([0,\infty)\), starts positive and
tends to \(-\infty\).  It has a unique positive zero \(y_*\), and exact
substitution gives

\[
 L:=\frac{2957298}{10^7}<y_*<
 U:=\frac{2957299}{10^7}.
 \tag{20}
\]

Therefore

\[
 M(a)=2e^{-y_*}P(y_*).
 \tag{21}
\]

Since \(P\) is increasing and \(y_*>L\), \(y_*<U\),

\[
 M(a)<2e^{-L}P(U).
\]

For \(0<L<1\), the degree-ten alternating Taylor sum

\[
 T_{10}(L)=\sum_{j=0}^{10}\frac{(-L)^j}{j!}
\]

is an upper bound for \(e^{-L}\).  Hence the completely rational number

\[
 \overline M=2T_{10}(L)P(U)
 \tag{22}
\]

satisfies \(M(a)<\overline M\).  With

\[
 r=\frac{6238973}{10^7},
\]

the exact checker verifies the rational inequalities

\[
 2S-\overline M>0,
 \qquad
 (2S-\overline M)^2>16r^4SH.
 \tag{23}
\]

No square root or floating-point comparison is used in (23).  Equations
(1), (22), and (23) give

\[
 Q(a)>r^2,
 \qquad
 \kappa_{\rm prof}>r=0.6238973.
 \tag{24}
\]

The exact checker reconstructs (18)--(23) from the six rational
coefficients in (14); the displayed decimals in its output are diagnostic
only.

## 5. A dual operator criterion

Let \(N\) denote the number operator, \(Ne_k=ke_k\), interpreted through its
quadratic form on \(\mathcal H_1\).

### Lemma 5.1. Dual criterion

Let \(Q_0>0\).  Suppose that for every \(t>0\) there is \(x=x(t)\in\mathbb R\)
such that, as quadratic forms on \(\mathcal H_1\),

\[
 K_x+2Q_0tN
 \succeq
 \left(2-\frac{2Q_0}{t}\right)I.
 \tag{25}
\]

Then \(Q(a)\le Q_0\) for every admissible profile \(a\), and hence

\[
 \Lambda_{\rm prof}\le Q_0.
 \tag{26}
\]

#### Proof

Normalize \(S(a)=1\), put \(\mu=H(a)>0\), and use (6).  For every \(t>0\),

\[
 M(a)+2Q_0t\mu
 \ge 2-\frac{2Q_0}{t}.
\]

Thus

\[
 2-M(a)\le2Q_0\left(t\mu+\frac1t\right).
\]

Choose \(t=\mu^{-1/2}\).  The right side becomes
\(4Q_0\sqrt\mu\), and (1) gives \(Q(a)\le Q_0\).  ∎

We certify (25) with

\[
 Q_0=\frac{779}{2000}=0.3895.
 \tag{27}
\]

## 6. Rank-one Schur reduction

Fix \(t>0\) and put \(y=x^2\).  Define

\[
 d_k(t)=2Q_0tk-2+\frac{2Q_0}{t},
 \qquad
 r_k(y)=e^{-y}\frac{y^k}{k!}.
 \tag{28}
\]

The vectors \(v_x\pm v_{-x}\) have opposite parity.  Consequently the
operator in (25), after moving the scalar right side to the left, splits
into even and odd blocks

\[
 D_{\rm even}+2w_{\rm even}\otimes w_{\rm even},
 \qquad
 D_{\rm odd}+2w_{\rm odd}\otimes w_{\rm odd},
 \tag{29}
\]

where \(D\) is diagonal with entries \(d_k(t)\) and
\(w_k^2=r_k(y)\).

For \(Q_0=779/2000\),

\[
 8Q_0^2-1=\frac{106841}{500000}>0.
\]

By AM--GM,

\[
 d_2(t)=4Q_0t+\frac{2Q_0}{t}-2>0
 \qquad(t>0),
 \tag{30}
\]

and \(d_k(t)\ge d_2(t)>0\) for every \(k\ge2\).

On the interval used below, \(t\ge0.47>Q_0\), so \(d_0<0\).
There is therefore only one potentially negative diagonal direction in
the even block.  If \(d_1<0\), there is likewise only one in the odd
block; if \(d_1\ge0\), the odd block is already positive.

For a diagonal operator with exactly one negative entry \(d_j\) and all
other entries positive, the Schur complement of a rank-one update gives
the exact condition

\[
 d_j+
 \frac{2w_j^2}
 {1+2\sum_{k\ne j}w_k^2/d_k}
 \ge0.
 \tag{31}
\]

For the even and odd tails,

\[
 T_e(y):=\sum_{\substack{k\ge2\\k\ {\rm even}}}r_k(y)
 =\frac{1+e^{-2y}}2-e^{-y},
 \tag{32}
\]

\[
 T_o(y):=\sum_{\substack{k\ge3\\k\ {\rm odd}}}r_k(y)
 =\frac{1-e^{-2y}}2-ye^{-y}.
 \tag{33}
\]

Because \(d_k\) increases with \(k\),

\[
 \sum_{\substack{k\ge2\\k\ {\rm even}}}\frac{r_k}{d_k}
 \le\frac{T_e}{d_2},
 \qquad
 \sum_{\substack{k\ge3\\k\ {\rm odd}}}\frac{r_k}{d_k}
 \le\frac{T_o}{d_3}.
 \tag{34}
\]

These estimates reduce the infinite-dimensional problem to two scalar
inequalities.

## 7. Exact rational interval certificate

For \(0\le z<1\), define the rational alternating sums

\[
 L(z)=\sum_{j=0}^{13}\frac{(-z)^j}{j!},
 \qquad
 U(z)=\sum_{j=0}^{12}\frac{(-z)^j}{j!}.
 \tag{35}
\]

The alternating-series theorem gives

\[
 L(z)\le e^{-z}\le U(z).
 \tag{36}
\]

For a rational \(y\) in the table below put

\[
 \ell=L(y),
\]

\[
 T_e^+=\frac{1+U(2y)}2-\ell,
 \qquad
 T_o^+=\frac{1-L(2y)}2-y\ell.
 \tag{37}
\]

Then \(\ell\le e^{-y}\), \(T_e\le T_e^+\), and \(T_o\le T_o^+\).
It is therefore sufficient, by (31)--(34), to prove

\[
 F_e(t):=
 d_0(t)\bigl(d_2(t)+2T_e^+\bigr)
 +2\ell\,d_2(t)>0,
 \tag{38}
\]

\[
 F_o(t):=
 d_1(t)\bigl(d_3(t)+2T_o^+\bigr)
 +2y\ell\,d_3(t)>0.
 \tag{39}
\]

When \(d_1\ge0\), the odd block needs no Schur estimate; (39) is simply
an additional sufficient certificate.

After multiplication by \(t^2>0\), both expressions in (38)--(39) are
degree-at-most-four polynomials in \(t\) with rational coefficients.
The following table covers \(0.47\le t\le2.10\).  In each row the indicated
rational \(y=x^2\) is used.

| \(t\)-interval | \(y\) |
|---|---:|
| [0.47, 0.8] | 0.304 |
| [0.8, 1.015] | 0.304 |
| [1.015, 1.045] | 0.300 |
| [1.045, 1.055] | 0.299 |
| [1.055, 1.065] | 0.298 |
| [1.065, 1.074] | 0.297 |
| [1.074, 1.0832] | 0.296 |
| [1.0832, 1.0917] | 0.295 |
| [1.0917, 1.100] | 0.294 |
| [1.100, 1.108] | 0.293 |
| [1.108, 1.117] | 0.292 |
| [1.117, 1.125] | 0.291 |
| [1.125, 1.134] | 0.290 |
| [1.134, 1.151] | 0.288 |
| [1.151, 1.168] | 0.286 |
| [1.168, 1.184] | 0.284 |
| [1.184, 1.201] | 0.282 |
| [1.201, 1.218] | 0.280 |
| [1.218, 1.250] | 0.276 |
| [1.250, 1.300] | 0.270 |
| [1.300, 1.365] | 0.262 |
| [1.365, 1.465] | 0.250 |
| [1.465, 1.550] | 0.240 |
| [1.550, 1.640] | 0.230 |
| [1.640, 1.740] | 0.220 |
| [1.740, 1.950] | 0.200 |
| [1.950, 2.065] | 0.190 |
| [2.065, 2.100] | 0.180 |

For every row \(2y<1\), so (35)--(36) apply.  The checker converts each
of the two rational polynomials \(t^2F_e(t)\), \(t^2F_o(t)\) to the
Bernstein basis on the stated interval.  **Every Bernstein coefficient is
strictly positive.**  Since the Bernstein basis is nonnegative on a closed
interval, (38)--(39) hold everywhere on every row.  The smallest positive
Bernstein coefficient in the replay is approximately
\(5.67\times10^{-6}\); this decimal is not used in the decision.

It remains to cover the two tails in \(t\).  Take \(x=0\).  Then
\(K_0=2e_0\otimes e_0\), so (25) is diagonal.  Its \(k=0\) entry is
\(2Q_0/t>0\), and all \(k\ge1\) entries are nonnegative whenever

\[
 Q_0\left(t+\frac1t\right)\ge1.
 \tag{40}
\]

The function \(t+1/t\) decreases on \((0,1]\) and increases on
\([1,\infty)\).  At the two rational endpoints,

\[
 Q_0\left(\frac{47}{100}+\frac{100}{47}\right)-1
 =\frac{110811}{9400000}>0,
\]

\[
 Q_0\left(\frac{21}{10}+\frac{10}{21}\right)-1
 =\frac{1439}{420000}>0.
\]

Thus \(x=0\) proves (25) for \(t\le0.47\) and \(t\ge2.10\), while the
table proves it in between.  Lemma 5.1 now yields

\[
 \Lambda_{\rm prof}\le\frac{779}{2000}.
 \tag{41}
\]

Together with (24), this proves (4)--(5).

## 8. Euler equation at a nondegenerate maximizer

The existence theorem permits a structural first-order analysis.  This
section is not used in the certified window.

Let \(a_*\) maximize \(Q\), and do not fix its normalization in the
calculation.  Put

\[
 S=S(a_*),\qquad H=H(a_*),\qquad M=M(a_*),\qquad
 n=2S-M.
\]

Then \(n>0\).

Assume that the maximizing set of \(\Phi_{a_*}(x)\) consists of one
absolute scale, \(\{x_0,-x_0\}\).  Since \(K_{x_0}=K_{-x_0}\), the
maximum functional is differentiable at \(a_*\) in every finitely
supported direction \(h\), with

\[
 dM(a_*)[h]=2\langle K_{x_0}a_*,h\rangle.
 \tag{42}
\]

Differentiating the scale-invariant functional (1) and using global
maximality gives

\[
 \left\langle
 K_{x_0}a_*+\eta Na_*-\theta a_*,
 h\right\rangle=0
 \tag{43}
\]

for every finitely supported \(h\), where

\[
 \eta=\frac{n}{2H}>0,
 \qquad
 \theta=2-\frac{n}{2S}
 =1+\frac{M}{2S}.
 \tag{44}
\]

Thus, coordinatewise,

\[
 K_{x_0}a_*+\eta Na_*=\theta a_*.
 \tag{45}
\]

Because \(K_{x_0}\) is bounded and \(a_*\in\ell^2\), (45) in fact implies
\(Na_*\in\ell^2\).

Suppose \(x_0>0\), put \(y=x_0^2\), and set

\[
 w_k=e^{-y/2}\frac{x_0^k}{\sqrt{k!}}.
\]

Let

\[
 L_e=\sum_{k\ {\rm even}}w_ka_k,\qquad
 L_o=\sum_{k\ {\rm odd}}w_ka_k.
\]

Parity gives

\[
 (K_{x_0}a)_k=
 \begin{cases}
 2w_kL_e,&k\text{ even},\\
 2w_kL_o,&k\text{ odd}.
 \end{cases}
 \tag{46}
\]

If both \(L_e\) and \(L_o\) are nonzero, then no denominator below can
vanish, and (45) gives the explicit resolvent form

\[
 a_k=
 \begin{cases}
 \displaystyle
 \frac{2L_e\,w_k}{\theta-\eta k},&k\text{ even},\\[8pt]
 \displaystyle
 \frac{2L_o\,w_k}{\theta-\eta k},&k\text{ odd}.
 \end{cases}
 \tag{47}
\]

Substituting (47) back into the definitions of \(L_e,L_o\) yields the two
scalar equations

\[
 2e^{-y}
 \sum_{k\ {\rm even}}
 \frac{y^k}{k!(\theta-\eta k)}=1,
 \tag{48}
\]

\[
 2e^{-y}
 \sum_{k\ {\rm odd}}
 \frac{y^k}{k!(\theta-\eta k)}=1.
 \tag{49}
\]

Finally, because \(x_0\) is an interior active scale, differentiation in
\(x\) gives

\[
 A(x_0)A'(x_0)
 -A(-x_0)A'(-x_0)
 -x_0\bigl(A(x_0)^2+A(-x_0)^2\bigr)=0.
 \tag{50}
\]

Equations (44), (48)--(50) reduce a nondegenerate infinite-profile
extremizer to a small coherent-state resolvent system.  They explain the
rapidly decaying alternating corrections seen in finite numerical
discovery, but no uniqueness claim for the global optimizer is made here.

For completeness, the differentiability assertion used in (42) follows
from the standard maximum argument directly.  Lemma 2.2 localizes all
maximizers of profiles near \(a_*\) to a fixed compact \(x\)-interval.
Uniqueness of the active operator \(K_{x_0}\) then gives the directional
derivative of the maximum as the derivative of
\(\langle a,K_{x_0}a\rangle\).  Only finitely supported directions are
needed to derive (45).

## 9. Consequence for the tensor constants

The preceding finite-profile theorem gives (2) for every finitely supported
profile.  By Theorem 3.1,

\[
 \sup_{\text{finite }a}\sqrt{Q(a)}
 =\sqrt{\Lambda_{\rm prof}}
 =\kappa_{\rm prof}.
\]

Taking the supremum in (2) therefore yields

\[
 \liminf_{p\to\infty}\frac{C_p}{p^{1/4}}
 \ge\kappa_{\rm prof}
 >0.6238973.
 \tag{51}
\]

This improves the previous certified profile value \(0.623586\).

The full tensor upper bound from the parent rigidity note remains

\[
 \limsup_{p\to\infty}\frac{C_p}{p^{1/4}}
 \le2^{-1/2}=0.707106\ldots.
\]

Equation (5) has a different meaning: **no reflected boundary-profile
argument covered by the finite-profile theorem can produce a leading lower
constant above \(0.624099351\ldots\)**.  Therefore further substantial
progress on the tensor leading constant must either improve the global tensor
upper theorem toward this window or construct asymptotic lower examples not
captured by the reflected boundary-scale ansatz.

## 10. Verification scope

The checker in checks/check_exact.py uses only exact rational arithmetic for
all decisions.

For the lower witness it:

1. reconstructs \(P\) and \(P'-P\) from (14);
2. checks the strict coefficient signs and the rational root bracket (20);
3. forms the alternating Taylor upper bound (22);
4. verifies the squared rational inequality (23).

For the upper certificate it:

1. reconstructs the Schur sufficient polynomials (38)--(39);
2. uses alternating Taylor lower/upper bounds for \(e^{-y}\) and
   \(e^{-2y}\);
3. converts every degree-at-most-four polynomial to the Bernstein basis on
   each rational interval in the table;
4. checks every Bernstein coefficient is strictly positive;
5. checks the exact two tail inequalities and \(8Q_0^2>1\).

The script contains no floating-point proof branch.  Its printed decimals
are summaries after all exact decisions have passed.  Running Python with
optimization does not remove any proof check because the script uses an
explicit failure routine rather than removable assertions.

The compactness, density, coherent-state reduction, dual lemma, Schur
complement proof, and Euler equation are analytic arguments in this file;
they are not delegated to the checker.

No complete Lean formalization or external human peer review is claimed.
