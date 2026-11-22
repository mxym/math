# The leading cancellation of the true many-small composite score

We use the literal fixed-target notation and score of the
[direct composite-gap identity](../direct_goldbach_composite_gap/Proof.md),
and the genuine two-bank upper sieve from the
[exactly-two gate](../direct_many_small_gate/Proof.md).
In particular, \(N=2x\) is even, \(L=\log x\),
\(z=\exp(L/(\log L)^2)\), \(P=N-y\), and \(J=xJ_0\) with
\(J_0\subset[1,3/2]\) a fixed nondegenerate interval.
The score \(\mathcal R_{\rm gap}\) includes the full actual calibrated
odd \(m\)-factor payer. A small prime is a prime \(<C_y=y/x^{1-\epsilon}\)
and \(k(y)\) counts the genuinely small prime factors of a squarefree
\(z\)-rough \(y\). Set \(c_0=e^{-\gamma}\), and define
\[
 H_k=\sum_{\substack{y\in J,\ N-y=P\ {\rm prime}\\
                     y\ {\rm squarefree},\,P^-(y)>z,\ k(y)=k}}
               \log P\,\mathcal R_{\rm gap}(y)
\]
(with \(H_{\ge3}=\sum_{k\ge3}H_k\)).

**Theorem.** Fix the odd \(m\ge3\). For sufficiently small fixed
\(0<\epsilon<.04/m\), and then \(x\to\infty\), uniformly in the even
target, we have
\[
\begin{split}
 H_0&={\cal G}_J(N)
       +\frac{c_0^2}{8\epsilon^2}|J|\mathfrak S(N)
       +O\left(\frac{\log(1/\epsilon)}{\epsilon}x\mathfrak S(N)\right)
       +o_{\epsilon,m,J_0}(x\mathfrak S(N)),\\
 |H_1|+|H_2|&\ll\epsilon^{-1}x\mathfrak S(N)
                      +o_{\epsilon,m,J_0}(x\mathfrak S(N)),\\
 H_{\ge3}&=-\frac{c_0^2}{8\epsilon^2}|J|\mathfrak S(N)
       +O\left(\frac{\log(1/\epsilon)}{\epsilon}x\mathfrak S(N)\right)
       +o_{\epsilon,m,J_0}(x\mathfrak S(N)).                 \tag{1}
\end{split}
\]
The \(O\)-constants in the displayed powers of \(\epsilon\) are
absolute. Both signs, including the negative many-small main,
are statements about the actual same-target true-prime pairing;
there is no average over \(N\).
The third formula concerns only rank \(\ge5\), as the smaller
ranks with \(k\ge3\) have score identically zero here.
It does not evaluate \({\cal G}_J(N)\): that term cancels between
the \(k=0\) evaluation and the original gap identity.

There is an optional explicit recentering. Complete *all* small
subproducts in the free term, with their coefficients
\(\mu_2(c)=(\mu*\mu)(c)\), instead of the old short hyperbola,
missing-pair and payer. Denote this new score by
\(\mathcal R^{\rm all}_{\rm gap}\). Its true prime mean, less
\({\cal G}_J(N)\), is
\[
  |J|\mathfrak S(N)\,[Q_\epsilon(1/2)-1]
               +o_{\epsilon,m,J_0}(x\mathfrak S(N)),           \tag{2}
\]
where \(Q_\epsilon\) is the explicit positive convolution mass
defined in Section 4. The entire shift is on \(k\ge3\) after
squareful errors; in particular it is not an unchanged
Goldbach identity. This recentering removes the leading
negative term of (1), but its remaining signed mass is not
priced at the Goldbach scale.

## 1. Evaluating the actual no-small channel

For this section one can use the fixed physical roughness
\(C=x^\epsilon\), instead of \(C_y\).
The difference lies in rows with one factor \(r\in[C,1.5C]\),
the other part being \(C/2\)-rough.
The number of factors on such a row is \(O(1/\epsilon)\), so
both the gap and own-root scores are \(O_\epsilon(L)\).
The two-bank upper on \(a\) and \(N-ra\) in an interval
of length \(\asymp x/r\) gives
\[
  \ll \frac{x\mathfrak S(N)}{\epsilon L^2 r}
\]
such rows for each \(r\). This is the bound (6) of the
exactly-two gate: the fixed coefficient is \(r\), and a bank
with cutoff \(C/2\) can be used. The endpoint convention for
a single boundary prime has the same upper.
Summing \(\sum_{C\le r\le1.5C,\ r\ {\rm prime}}1/r=O_\epsilon(L^{-1})\)
pays \(o_\epsilon(x\mathfrak S(N))\) for the full logarithmically
weighted score. Opposite primes dividing \(N\) cost \(x^{o(1)}\)
and are omitted in these arguments.

On the no-small class there is no \(c\) other than 1 and no
completion or payer. Temporarily use the two fixed wider
cutoffs
\[
 R'_\pm=x^{1/2\pm\eta},\qquad
 \eta=K\epsilon\log(1/\epsilon)<.01,
\]
where \(K>0\) is a sufficiently large absolute constant and
\(\epsilon\) is sufficiently small thereafter. The original gap
parameter tends to zero, and eventually is \(<\eta\).
For any changed divisor, its shorter-variable complement or
the divisor itself lies in \([x^{1/2-\eta},1.5x^{1/2+\eta}]\).
Sum over this fixed \(C\)-rough variable \(b\), relax to
\(x\le ab\le1.5x\), and use the same two-bank bound on the other
\(C\)-rough variable \(a\) and the actual prime \(N-ba\).
It is uniform in this use: the interval for \(a\) has length
\(\gg x^{.49}\), all primes of \(b\) exceed \(z\), and the sieve
CRT remainder remains \(O(x^{.23}L^{O(1)})\).
Both score logarithms cost \(O(L^2)\).
The harmonic mass of those \(b\)'s is
\[
  \ll \frac{\eta L+1}{\epsilon L};
\]
indeed divide into dyads and apply the one-dimensional upper
rough sieve in each, as in the exactly-two gate.
Thus the actual change of the gap score paired with primes
is \(O(\eta x\mathfrak S(N)/\epsilon^2)+o_\epsilon(x\mathfrak S(N))\).

For each wider cutoff the genuine paired calculation is
particularly simple:
\[
 \sum_{\substack{y\in J,\ P=N-y\ {\rm prime}\\P^-(y)>C}}\log P\,\mathcal R'_{\rm gap}(y)
    ={\cal G}_J(N)-T_{\rm raw}+T_{\rm free}
                   +o_\epsilon(x\mathfrak S(N)),              \tag{3}
\]
where
\[
 \begin{split}
 T_{\rm raw}
 &=\sum_{y\in J,\ P\ {\rm prime}}\log P\, R_C(y)
       \sum_{\substack{b\mid y\\b\le R'_-}}\mu(b)\log(y/b),\\
 T_{\rm free}
 &=\sum_{y\in J,\ P\ {\rm prime}}\log P\, R_C(y)
       \sum_{\substack{b\mid y\\b<y/R'_+}}\log b .
 \end{split}
\]
Here \(R_C\) indicates \(C\)-roughness.
The \(\Lambda\) identity is exact, all actual Goldbach prime
partners are \(C\)-rough at this scale, and proper powers
cost \(O(x^{1/2}L^{O(1)})\).
Squareful \(C\)-rough terms in the composite scores have
negligible absolute size by their \(O(x/C)\) unweighted
count and an ordinary fixed divisor moment.

Keep \(b\) itself \(C\)-rough and a unit at \(N\), and open the
rough condition on \(a=y/b\) using the upper and lower linear
fundamental lemma with level \(D=x^{\eta/2}\).
The two masks have disjoint prime supports.
Both true progression moduli \(bd\) lie below
\(1.5x^{.5-\eta/2}\), and the reconstruction of \(b,d\) from
such a modulus is unique. Prefix estimates and partial
summation cover the varying \(y>bR'_+\) and
\(\log(y/b)\); BV thus gives arbitrary-log errors for
fixed \(\epsilon,\eta\).
The sieve parameter is \(s=\eta/(2\epsilon)\).
Separate the signs of \(\mu(b)\): using the upper and lower
weights according to each sign, the main error is bounded
by the positive discrepancy of the fundamental lemma times
its absolute model. This is at most
\[
  \ll x\mathfrak S(N)\epsilon^{-2}\exp(-c\,s\log s)
\]
for a fixed \(c>0\): the absolute model is bounded by
\(xV_N(C)L\sum_{b\le1.5R'_-}R_C(b)/b\), where
\(V_N(C)\ll\mathfrak S(N)/(\epsilon L)\) and
\(\sum R_C(b)/b\ll1/\epsilon\).
For the latter include \(b=1\), take an absolute fixed
large \(A_0\), and use dyads starting above \(x^{2A_0\epsilon}\)
with rough-sieve level \(x^{A_0\epsilon}\). Below this use the
bounded reciprocal-prime convolution, including the atom at
1, whose mass is \(O_{A_0}(1)\).
This avoids imposing a dimension-one estimate at a short
level with parameter below 1.
For the bounded coefficients and the stated factorial form, use
[Koukoulopoulos, *The Distribution of Prime Numbers*, Theorem 19.1(a)--(c)](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf).
Its uniform dimension condition holds here as \(g(t)=1/(t-1)\) for
\(t\nmid N\), zero otherwise, and \(g(2)=0\).
For a fixed \(K>0\) and sufficiently small \(\epsilon\),
\(c s\log s\ge 3\log(1/\epsilon)\) (since \(s=(K/2)\log(1/\epsilon)\)),
so this error is even \(O(\epsilon x\mathfrak S(N))\).

Replacing \(1/\varphi(b)\) with \(1/b\) and removing the
omitted \(N\)-factors in \(b\) costs \(o_\epsilon(x\mathfrak S(N))\).
Indeed every prime in \(b\) is \(>C\), the ratio of totients
is \(1+O(L/C)\), and the removed harmonic mass is
\(O_\epsilon(L/C)\) by dividing by a prime of \(N\) above
\(C\). Also
\[
  V_N(C)=\mathfrak S(N)\frac{c_0+o_\epsilon(1)}{\epsilon L}
\]
by the same local product identity as at \(z\).
The principal expressions for \(T_{\rm raw},T_{\rm free}\)
are thereby the integrals over \(y\in J\) of \(V_N(C)\)
times, respectively,
\[
 \sum_{\substack{b\le R'_-\\P^-(b)>C}}
            \frac{\mu(b)}b\log(y/b),\qquad
 \sum_{\substack{b<y/R'_+\\P^-(b)>C}}\frac{\log b}{b}.
                                                                    \tag{4}
\]

We recall the precise analytic normalization. For \(U\) fixed,
as \(C\to\infty\), the signed harmonic cumulative function
\(\sum_{b\le C^U,\ P^-(b)>C}\mu(b)/b\) tends to \(\rho(U)\),
the ordinary Dickman function. The positive harmonic measure
\(\sum_{P^-(b)>C} b^{-1}\delta_{\log b/\log C}\) tends locally
to \(dM=\delta_0+\omega_{\rm ext}(u)\,du\), where \(\omega_{\rm ext}\)
is Buchstab's function, extended by zero on \([0,1)\).
For completeness, the two local limit measures are the signed
and positive convolution exponentials of
\(1_{u\ge1}\,du/u\): expand by number of true primes,
ignore repeats at \(O_U(C^{-1})\) harmonic cost, and use Mertens
uniformly on finite intervals. The first cumulative exponential
solves \(u\rho'(u)=-\rho(u-1)\) with \(\rho=1\) on \([0,1]\);
the positive exponential has density solving Buchstab's
equation and initial value \(\omega(u)=1/u\) for \(1<u<2\).
This can also be seen by differentiating the two Laplace
transforms \(\exp(\mp\int_1^\infty e^{-su}\,du/u)\).
Use \(\int\rho=e^\gamma\), and the exponential convergence
of \(\omega(u)\) to \(c_0\); see primary
[Hildebrand--Tenenbaum, *On a class of differential-difference equations*](https://tenenb.perso.math.cnrs.fr/PPP/Diff-diff_eqns.pdf).
The Dickman bound \(\rho(u)\le1/\lfloor u\rfloor!\) follows
from monotonicity and \(u\rho(u)=\int_{u-1}^u\rho(v)\,dv\).

Write \(U=(1/2-\eta)/\epsilon\). For the first expression in
(4), after normalization by \(V_N(C)/\mathfrak S(N)\),
Mertens and integration by parts yield
\[
       c_0\left[\frac{\log y}{\epsilon L}\rho(U)
               +\int_0^U \rho(t-1)1_{t\ge1}\,dt\right]+o_\epsilon(1)
                     =1+O(\epsilon)+o_\epsilon(1).
\]
This follows from the factorial Dickman bound just stated.
For the free expression the model is
\[
           c_0\int_0^{U} t\,\omega_{\rm ext}(t)\,dt+o_\epsilon(1)
           =\frac{c_0^2}{2\epsilon^2}(1/2-\eta)^2
                    +O(1)+o_\epsilon(1);
\]
the mass at \(t=0\) contributes zero, and the error is
\(O(1)\) by exponential convergence of \(\omega\).
The cutoff \(y/R'_+\) moves the exponent \(U\) by
\(O(1/(\epsilon L))\), which only incurs \(o_\epsilon(1)\).
Equation (3) and the genuine wider-gap shoulder now prove
the first line of (1), with coefficient \(c_0^2/8\).

## 2. Both signs for exactly one or two small primes

Use the own root \(R=\sqrt y\); all \(k\le2\) ranks are
bounded for each fixed \(\epsilon\), so the original scored
true prime expectation changes by \(o_{\epsilon,m,J_0}(x\mathfrak S(N))\).
For \(y=pM\) with unique small prime \(p\), put \(b=M/d\).
The exact grouped large-divisor formula is
\[
 \sum_{\substack{u\mid p\\du>R}}\mu(p/u)
       \{(1-\mu(d))\log b-(1+\mu(d))\log(p/u)\}.
\]
When \(d>R\) it is \((1+\mu(d))\log p\); when \(R/p<d\le R\)
it is \((1-\mu(d))\log b\); otherwise it vanishes.
For the first portion keep \(p,b\) fixed and count the rough
long \(d\) and true prime \(N-pbd\) by the two-bank upper.
Here \(pb=y/d\le\sqrt{1.5x}\) on the actual rows,
so the \(d\)-interval is long, also allowing \(b=1\).
The cost is bounded by
\[
  \ll \frac{x\mathfrak S(N)}{\epsilon L}
            \sum_{p\le1.5C}\frac{\log p}{p}
            \sum_{\substack{b\le\sqrt{1.5x}\\P^-(b)>C/2}}\frac1b
       \ll\frac{x\mathfrak S(N)}{\epsilon}.
\]
For the root strip portion keep \(p,d\) fixed, and count
the rough \(b\) and the opposite prime. The sum over \(d\)
has \(1/d\) mass
\(\ll(\log p+1)/(\epsilon L)\), and both logarithms then
cost \(O(L^2)\). Its upper is of the same order.

For \(y=pqM\), \(p<q\) the true small primes, the exact
formula (4) of the exactly-two gate shows that \(d>R\)
and \(d\le R/(pq)\) give zero. In the lower and upper
strips \(R/(pq)<d\le R/q\), \(R/p<d\le R\), the absolute
score per \(d\) is \(O(L)\), and each log-width is \(\log p\).
These are bounded exactly like its earlier negative upper.
In the middle strip \(R/q<d\le R/p\), the absolute score
is \(\le2\log p\); its width is \(\le\log q\).
Fix \(p,q,d\), apply the same two-bank bound to rough
\(b=M/d\), and sum the harmonic \(d\) weight by dyads.
This middle contribution is
\[
 \ll \frac{x\mathfrak S(N)}{\epsilon^2 L^2}
       \sum_{p<q\le1.5C}\frac{\log p\,(\log q+1)}{pq}
 \ll x\mathfrak S(N).
\]
The actually admissible long intervals are at least
\(\gg x^{.49}\) for sufficiently small \(\epsilon\);
the root thresholds with \(R=\sqrt y\) change these
dyadic harmonic widths by only an additive \(O(1)\).
This proves the second line of (1), in fact for the
fully absolute score in each of these two classes.

## 3. Actual many-small main

The direct gap identity gives
\({\cal G}_J(N)=H_0+H_1+H_2+H_{\ge3}+O_A(xL^{-A})\).
Its squareful \(z\)-rough omission has that error by
Cauchy--Schwarz and a fixed divisor moment.
Subtract the first two lines of (1); the unknown
binary count cancels exactly. This gives the third line.
For rank at most four with \(k\ge3\), the only possible
case here is three small primes and one giant prime;
the product of the small ones is \(<x^{3\epsilon+o(1)}\),
and the giant exceeds \(x^{1-3\epsilon-o(1)}\).
Both original gap cutoffs therefore admit only the
divisors containing the giant in the large terms.
The raw alternating sum is zero. In the free term all
small subsets of size \(\le2\) are present, and omitting
a size-three subset has no effect because its free
complement is only the giant, with \(S_+(\text{giant})=0\).
If \(m>3\) the payer is absent; if \(m=3\) and these three
small primes are an eligible payer, its free complement is the
single giant and \(S_+(\mathrm{giant})=0\).
The resulting complete small-subset finite difference is zero.
There is thus no low-rank mass hidden in the third line of (1).

## 4. Optional explicit completion of all small subproducts

Here use the actual moving \(C_y\) again. The new score replaces its
free cofactor coefficient by
\[
 w_y^{\rm all}(c)=\mu_2(c)\,1_{\{P^+(c)<C_y\}},
 \qquad P^+(1)=1.
\]
It is the same true row observable on squarefree \(k\le2\)
because the old pair-completion restores the sole possible
missing cofactor there and the odd payer is absent.
Each new summand has \(b=sc\le1.5R_-\) exactly as before,
regardless of the possible number of small factors of \(c\).
Its coefficient as a function of the physical \(y\) has
one small-factor-admission jump and one interval endpoint
\(y>bR_+\); the sum over \(c\mid b\) costs only fixed divisor
powers. Thus the original true-prime BV transfer applies
unchanged, with the same \(z\)-smooth sieve supports,
actual modulus \(bd\) and prefix/error estimates.
It yields the model
\[
 V_N(z)\int_J
 \sum_{\substack{sc\le y/R_+\\P^-(sc)>z}}
   \frac{w_y^{\rm all}(c)\log s}{sc}\,dy+O_A(xL^{-A}).
                                                                    \tag{5}
\]
Endpoint equality has no effect on the integral.
As in the direct proof the local \(1/\varphi(sc)\)
may be changed to \(1/(sc)\), and removing the \(N\)-parts
from these harmonic coefficients costs arbitrary-log error
by fixed ordinary divisor moments and \(z\to\infty\).

The exact analytic simplification is useful: if
\(\zeta_{>v}(s)=\prod_{p>v}(1-p^{-s})^{-1}\), let
\(\zeta_{\ge C_y}\) denote the product with \(p\ge C_y\).
Then the Dirichlet series of the coefficient in (5), before
the \(1/(sc)\) harmonic normalization, is exactly
\[
    -\zeta_{>z}'(s)\prod_{z<p<C_y}(1-p^{-s})^2
        =\zeta_{\ge C_y}^2(s)\,(\zeta_{>z}^{-1})'(s).
\]
This retains all prime powers in the analytic computation.
If \(A=y/R_+\), the integrand with \(V_N(z)\) removed is
therefore exactly
\[
 \sum_{\substack{h\le A\\P^-(h)\ge C_y}}\frac{\tau(h)}h
             \sum_{\substack{d\le A/h\\P^-(d)>z}}
                     \frac{-\mu(d)\log d}{d}.                 \tag{6}
\]
The inner signed sum multiplied by \(V_z\) has a uniformly
bounded cumulative model
\[
      c_0\int_0^{\log(A/h)/\log z}
                \rho(t-1)1_{t\ge1}\,dt+o(1),
\]
uniform for \(1\le A/h\le2x\). To verify moving-range uniformity,
put \(T=\log(2x)/\log z=O((\log L)^2)\).
At normalized exponents \([1,T]\), the reciprocal-prime
measure has prefix discrepancy \(O(\exp(-c\sqrt{\log z}))\)
from \(dt/t\), by ordinary quantitative PNT and partial
summation. Its total mass and the continuous mass are
\(O(1+\log T)\). In each \(j\)-fold convolution on
\([0,U]\), telescope by replacing one factor at a time;
the other variables give a prefix at every fixed choice,
so the difference is bounded by \(j\) times this discrepancy
times \(O(1+\log T)^{j-1}\), with a fixed constant.
The lost repeat primes are bounded in the unsigned factorial
sum by \(O(T^{O(1)}/z)\), using
\(\sum_{p>z}p^{-2}\ll1/z\).
Summing the \(j!\) denominators costs only \(T^{O(1)}\).
The weight \(\log d\) comes by prefix partial summation in
\(U\), with additional factor at most \(T\log z\), and
\(V_z\log z\to c_0\).
Thus the convergence above is uniform and the model tends
to 1 whenever \(\log(A/h)/L\) is bounded below by a positive
constant.

The outer harmonic measure in (6) converges on \([0,1]\)
to the positive mass with cumulative
\[
 Q_\epsilon(v)=\sum_{j\ge0}\frac{2^j}{j!}
 \int_{\substack{t_i\ge\epsilon\\\sum_i t_i\le v}}
                    \prod_{i=1}^j\frac{dt_i}{t_i}.
\]
There is one atom at zero (the \(j=0\) term) and no atom
in a neighborhood of \(1/2\). To check this convergence
replace the primes by their reciprocal-prime measures,
note that \(\tau(h)=2^j\) on the squarefree terms and
remove powers at \(O_\epsilon(x^{-\epsilon})\) harmonic
cost; use the finite rank bound at fixed \(\epsilon\).
The shift \(C_y=x^{\epsilon+O(1/L)}\) is uniform in \(y\),
with \(o_\epsilon(1)\) local error. The changed outer
boundary \(A=x^{.5-o(1)}\) lies at a continuity point;
cut first just below \(1/2\), use the preceding uniform
bound and convergence of the inner model, and then let
that last width go to zero. This proves (5) equals
\(|J|\mathfrak S(N)Q_\epsilon(1/2)+o_\epsilon(x\mathfrak S(N))\).
The raw subtraction is still \(|J|\mathfrak S(N)\) with
the old sign. Equation (2) follows.

In particular \(Q_\epsilon(v)=(M*M)([0,v/\epsilon])\).
Since \(M=\delta_0+\omega_{\rm ext}(t)\,dt\) and
\(\omega_{\rm ext}(t)=c_0+O(e^{-ct})\) for large \(t\),
\[
                   Q_\epsilon(1/2)
                      =\frac{c_0^2}{8\epsilon^2}
                                    +O(\epsilon^{-1}).
\]
This agrees with the real no-small amplification in (1).
The new aggregate \(k\ge3\) is now
\(O(\epsilon^{-1}\log(1/\epsilon)x\mathfrak S(N))
+o_{\epsilon,m,J_0}(x\mathfrak S(N))\), not a bound of
size \(o(x\mathfrak S(N))\).
For squarefree \(y=SM\) with \(S\) the full small prime
product, the new own-root reference sums for \(d\mid M\)
only over \(u\mid S,\ du>\sqrt y\), with exact term
\[
  \mu(S/u)\{(1+\mu(d)\mu(S))\log(M/d)
                    +(\mu(d)\mu(S)-1)\log(S/u)\}.
\]
If \(S\) has two or more prime factors, the groups with
all or none of the \(u\)'s admitted give zero, so the
own-root residual is physically supported on genuine
macro divisors \(\sqrt y/S<d\le\sqrt y\).
This last pointwise statement does not transfer all
unbounded ranks from the actual gap to the own-root score.
The proof of (2) uses the actual gap throughout.

A [same-score least-factor deletion](../direct_completed_rough_deletion/Proof.md) raises the actual roughness threshold in this all-completed variant, with the sharp gap, physical small-factor boundary and recentered main unchanged to natural-scale precision. It does not estimate the surviving many-small signed sum.
