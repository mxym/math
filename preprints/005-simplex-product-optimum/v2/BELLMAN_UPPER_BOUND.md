# A Bellman upper bound for the product/join closure

**Supplement to 005 v2 — 7 October 2026.**

This note proves a global upper bound for the asymptotic projection-volume
growth rate of the point-generated product/join class \(\mathcal C\) defined
in 005 v2. It uses the exact \((R,a)\) calculus of paper.md and the spectral
reduction in ASYMPTOTIC_SPECTRAL_REDUCTION.md.

The finite part of one scalar inequality is certified by
code/check_bellman_upper.py, using only integer and Fraction arithmetic for
every proof decision. The script also certifies the numerical constants
appearing in the analytic tails. The computer check is not a substitute for
the invariant-calculus proof; the mathematical reduction to the checked
scalar inequalities is written below.

## 1. Statement

For a positive-dimensional body \(K\), write

\[
 d=\dim K,\qquad D=d+1,\qquad H(K)=\frac1{a(K)},\qquad
 Q(K)=\frac{a(K)R(K)}{g(d)},\qquad g(d)=\frac{d^d}{d!}.
\]

For the formal point use \(D=H=Q=1\). Define

\[
 \boxed{\alpha_*=\frac{11}{85}\log\frac{189}{128}.}
\]

### Theorem 1.1. Global Bellman inequality

Every \(K\in\mathcal C\) satisfies

\[
 \boxed{
 \log Q(K)\le
 \alpha_*\left(D-\frac{H(K)^2}{D}\right).}
 \tag{1.1}
\]

The inequality is sharp: equality holds for every simplex, for
\(T_5\times T_5\), and for the join of any number of identical copies of
\(T_5\times T_5\).

### Corollary 1.2. A narrow rigorous interval for the recursive asymptotic rate

Let

\[
 \Gamma_{\mathcal C}
 =\lim_{n\to\infty}\sup_{K\in\mathcal C_n}R(K)^{1/n}.
\]

Then

\[
 \boxed{
 2.8534<\Gamma_{\mathcal C}
 \le e\left(\frac{189}{128}\right)^{11/85}
 <2.8589.}
 \tag{1.2}
\]

The lower bound is Theorem 9.2 and Corollary 9.3 of paper.md.
The upper bound follows from (1.1) and the spectral reduction.

Indeed, (1.1) gives
\(\lambda(K)=Q(K)^{1/D}\le e^{\alpha_*}\), hence
\(\lambda_*\le e^{\alpha_*}\). The spectral identity
\(\Gamma_{\mathcal C}=e\lambda_*\) then gives the middle inequality in
(1.2). The final decimal comparison is checked by rational logarithm
intervals in the supplied verifier; no floating-point comparison is a proof
dependency.

## 2. Join closure is automatic

For joins, 005 v2 proves

\[
 D(A*B)=D(A)+D(B),\qquad
 H(A*B)=H(A)+H(B),\qquad
 Q(A*B)=Q(A)Q(B).
\]

Suppose (1.1) holds for \(A,B\). Then

\[
\begin{aligned}
 \log Q(A*B)
 &\le \alpha_*
 \left(D_1+D_2-\frac{H_1^2}{D_1}-\frac{H_2^2}{D_2}\right)\\
 &\le \alpha_*
 \left(D_1+D_2-\frac{(H_1+H_2)^2}{D_1+D_2}\right),
\end{aligned}
\]

where the second line is Cauchy's inequality. Thus the Bellman region is
closed under joins.

The formal point has equality in (1.1), so all simplices, which are repeated
joins of points, also have equality.

## 3. Reduction of a product to one scalar inequality

Let \(A,B\) have dimensions \(r,s\ge1\), and put \(n=r+s\). Write

\[
 H_1=H(A),\qquad H_2=H(B),\qquad
 A_{r,s}=\frac{g(r)g(s)}{g(n)}.
\]

The product formulas from 005 v2 give

\[
 H(A\times B)=
 \frac{n}{r/H_1+s/H_2}
\]

and

\[
 Q(A\times B)
 =Q(A)Q(B)A_{r,s}\,
 \frac{rH_2+sH_1}{n}.
\]

Set

\[
 B_0=\frac{rH_2+sH_1}{n}
\]

and

\[
 G=
 \frac{H_1^2}{r+1}
 +\frac{H_2^2}{s+1}
 -\frac{H(A\times B)^2}{n+1}.
\]

If (1.1) holds for both factors, it will hold for their product provided

\[
 \boxed{
 \log(A_{r,s}B_0)\le\alpha_*(G-1).}
 \tag{3.1}
\]

The general invariant bound \(1/(d+1)\le a(K)\le1\) gives the only box
constraints needed below:

\[
 1\le H_1\le r+1,\qquad 1\le H_2\le s+1.
 \tag{3.2}
\]

Thus the entire induction has been reduced to (3.1) for integers \(r,s\ge1\)
and the rectangle (3.2).

## 4. A sharp box-constrained quadratic lower bound

Assume without loss of generality \(r\ge s\). Let

\[
 C_0=\frac{rH_1+sH_2}{n}.
\]

Weighted harmonic mean is at most weighted arithmetic mean, hence

\[
 H(A\times B)\le C_0.
\]

Therefore

\[
 G\ge
 \widetilde G:=
 \frac{H_1^2}{r+1}
 +\frac{H_2^2}{s+1}
 -\frac{C_0^2}{n+1}.
 \tag{4.1}
\]

Fix \(B_0\). The constraint
\(sH_1+rH_2=nB_0\) leaves one degree of freedom, and
\(\widetilde G\) is a strictly convex quadratic on the resulting interval.

Put

\[
 \Delta=4rs+3r+3s+2,
\]

\[
 B_-=\frac{\Delta}{(s+1)(3r+s+2)},\qquad
 B_+=\frac{\Delta}{3r+s+2},\qquad
 B_{\max}=1+\frac{2rs}{r+s}.
\]

For \(r\ge s\),

\[
 1\le B_-\le B_+\le B_{\max}.
\]

The unconstrained quadratic minimizer is

\[
 \frac{H_1}{B_0}
 =\frac{(r+1)(r+3s+2)}{\Delta},\qquad
 \frac{H_2}{B_0}
 =\frac{(s+1)(3r+s+2)}{\Delta}.
 \tag{4.2}
\]

Consequently the exact box-constrained minimum
\(q_{r,s}(B_0)\) of the right side of (4.1) is

\[
 q_{r,s}(B)=
 \begin{cases}
 q_1(B),&1\le B\le B_-,\\[2mm]
 \displaystyle
 \frac{3(r+s)+2}{\Delta}\,B^2,
 &B_-\le B\le B_+,\\[3mm]
 q_{s+1}(B),&B_+\le B\le B_{\max},
 \end{cases}
 \tag{4.3}
\]

where, for \(b\in\{1,s+1\}\),

\[
 h_b(B)=\frac{(r+s)B-rb}{s},
\]

\[
 q_b(B)=
 \frac{h_b(B)^2}{r+1}
 +\frac{b^2}{s+1}
 -\frac{(r\,h_b(B)+s b)^2}{(r+s)^2(r+s+1)}.
 \tag{4.4}
\]

Indeed, below \(B_-\) the unconstrained value of \(H_2\) is below one, and
above \(B_+\) it is above \(s+1\); the nearest box boundary is therefore
\(H_2=1\) or \(H_2=s+1\), respectively. Formula (4.2) also shows that
\(H_1\) remains inside its box throughout the middle interval. This proves
(4.3) directly from one-variable convex quadratic minimization.

It is therefore sufficient to prove

\[
 \boxed{
 \log(A_{r,s}B)
 \le\alpha_*\bigl(q_{r,s}(B)-1\bigr)
 \quad(1\le B\le B_{\max}).}
 \tag{4.5}
\]

Each branch of \(q_{r,s}\) is a quadratic
\(uB^2+vB+w\) with \(u>0\). Hence

\[
 \log B-\alpha_*(uB^2+vB+w-1)
\]

is strictly concave. There is at most one interior maximizer on each branch.
This is the scalar fact certified in the finite part of the checker.

## 5. The unique equality in the product step

For \(r=s=5\), the middle branch is valid on \(1\le B\le6\), with

\[
 A_{5,5}=\frac{63}{256},\qquad
 q_{5,5}(B)=\frac8{33}B^2.
\]

The maximum occurs at the endpoint \(B=6\), and

\[
 A_{5,5}B=\frac{189}{128},\qquad
 q_{5,5}(6)-1=\frac{85}{11}.
\]

Thus the definition of \(\alpha_*\) gives exact equality:

\[
 \log\frac{189}{128}
 =\alpha_*\frac{85}{11}.
\]

This is the product \(T_5\times T_5\). Equal joins preserve equality in
the Cauchy step, explaining the first self-similar equality state in 005 v2.

## 6. Infinite tails

Only a finite strip needs computer checking. The rest follows from elementary
uniform estimates.

### 6.1. Both dimensions at least ten

The standard Robbins Stirling bounds imply

\[
 A_{r,s}\le
 \sqrt{\frac{r+s}{2\pi rs}}.
 \tag{6.1}
\]

The unconstrained quadratic minimum underlying (4.3) gives, for every \(B\),

\[
 q_{r,s}(B)\ge
 k_{r,s}B^2,\qquad
 k_{r,s}=\frac{3(r+s)+2}{4rs+3(r+s)+2}.
 \tag{6.2}
\]

Maximizing \(\log B-\alpha_*k_{r,s}B^2\) over all \(B>0\), and using
\(r\ge s\ge10\), yields

\[
\begin{aligned}
 \log(A_{r,s}B)-\alpha_*(q_{r,s}(B)-1)
 &\le
 \frac12\log\!\left(
 \frac{23/60}{\pi\alpha_*}\right)
 -\frac12+\alpha_*\\
 &<0.
\end{aligned}
 \tag{6.3}
\]

For the elementary constant \(23/60\), note that

\[
 \frac{r+s}{4rs\,k_{r,s}}
 =
 \frac{r+s}{3(r+s)+2}
 +\frac{r+s}{4rs}
 <
 \frac13+\frac1{20}
 =\frac{23}{60}.
\]

The final strict inequality in (6.3) is certified by rational intervals for
\(\pi\), \(\log\), and \(\alpha_*\).

### 6.2. Fixed small side and large other side

For fixed \(s\) we use the elementary estimate

\[
 A_{r,s}
 \le g(s)\left(1+\frac sr\right)^{-r},
\]

and

\[
 \log A_{r,s}
 \le \log g(s)-s+\frac{s^2}{2r},
 \tag{6.4}
\]

which follows from
\(\log(1+x)\ge x-x^2/2\).

For

\[
 s\in\{1,4,5,6,7,8,9\},\qquad r\ge1000,
\]

combine (6.4) with

\[
 k_{r,s}\ge\frac3{4s+3},\qquad
 B_{\max}<1+2s.
\]

The resulting one-variable maxima are all strictly negative. The largest
certified upper margin among these seven tails is less than \(-0.0045\).

For \(s=2,3\), the low and middle portions are handled by the same quadratic
bound. On the high branch, (4.4) is bounded below by a limiting quadratic.
For \(s=2\),

\[
 q_{r,2}(B)\ge
 q_{\infty,2}(B):=
 \frac32(B^2-6B+11)
 \qquad(3\le B\le5),
 \tag{6.5}
\]

because

\[
 q_{r,2}(B)-q_{\infty,2}(B)
 =
 -\frac{
 r(4B^2-48B+108)+(3B^2-54B+99)}
 {2(r+1)(r+3)}
 \ge0
\]

throughout \(3\le B\le5\). Likewise,

\[
 q_{r,3}(B)\ge
 q_{\infty,3}(B):=
 B^2-8B+20
 \qquad(4\le B\le7),
 \tag{6.6}
\]

because

\[
 q_{r,3}(B)-q_{\infty,3}(B)
 =
 -\frac{4\{r(B^2-20B+64)-24B+60\}}
 {3(r+1)(r+4)}
 \ge0.
\]

Together with (6.4), these give strict negative margins for
\(s=2,3,\ r\ge1000\). The checker records margins below \(-0.07\) and
\(-0.047\), respectively, on the high branches.

## 7. Finite exact interval certificate

It remains to check

\[
 1\le s\le9,\qquad s\le r<1000.
\]

There are 26,847 nonempty quadratic branches in (4.3).
code/check_bellman_upper.py checks every one.

The checker uses no floating-point number in a proof decision.

* Rational logarithms use
  \[
   \log x=2\sum_{j\ge0}\frac{z^{2j+1}}{2j+1},
   \qquad z=\frac{x-1}{x+1},
  \]
  after power-of-two range reduction, with an explicit geometric tail bound.
* \(\pi\) is enclosed by the Machin identity
  \[
   \pi=16\arctan(1/5)-4\arctan(1/239)
  \]
  and alternating rational series.
* Integer logarithms through 1008 are cached; finite
  \(A_{r,s}\) values are evaluated through a short binomial-log identity,
  avoiding giant floating-point factorials.
* Every branch is strictly concave. The derivative is enclosed by rational
  intervals and its unique zero is bracketed by rational bisection. The
  whole bracket is then evaluated by interval arithmetic.
* The \((5,5,B=6)\) equality is checked algebraically rather than accepted
  through a rounded zero.

All strict finite branches pass. The closest non-equality branch is
\((r,s)=(5,4)\), with certified upper margin below \(-4.55\times10^{-4}\).

This completes the proof of (4.5), hence the product induction, and therefore
Theorem 1.1.

## 8. Scope

This theorem is an upper bound for the point-generated class closed under
Cartesian products and joins. It is **not** an upper bound for all convex
bodies and does not determine the unrestricted Schneider projection
constant.

It also does not prove that the current self-similar lower construction is
optimal inside \(\mathcal C\). The remaining certified gap is

\[
 2.8534
 <\Gamma_{\mathcal C}
 <2.8589.
\]

The next target is a sharper convex Bellman function than the quadratic
potential in (1.1). A mixed quadratic/quartic potential already gives
discovery-level evidence for an upper value near \(2.8542\), but that stronger
claim is not included here until its global product inequality receives the
same exact certification.
