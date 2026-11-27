# Sharper effective bounds for equal binomial shifts

Consider integers \(d\ge2,\ n\ge 2d,\ 0\le k\le n-2d\) satisfying
\[
                 \binom n k=\binom{n-d}{k+d}.
\]
We allow both halves of Pascal's triangle and also the boundary \(k=0\).
Put \(z=n-k-d+\tfrac12\).

**Theorem.** For \(d\ge8\), every solution has
\[
     z<\max(8d,r_d d^2),\qquad
     r_d=\begin{cases}7/10,&d\equiv 2,4\pmod6,\\[1mm]1/2,&\text{otherwise}.\end{cases}
\]
For \(2\le d<8\) one has \(z<16d^2\). Also \(n\le 2z+d-1\).
The companion exact enumeration finds only \(n=2d,\ k=0\) for every \(2\le d\le256\).
In particular the small shifts in the analytic statement have no nontrivial exceptions.

The repository's [previous equal-shift note](FactorSingmasterBalancedShifts.md)
already proved effective finiteness for the equal-offset direction of
[Hugo Jenkins, *Repeated Binomial Coefficients and High-Degree Curves*, §4](https://math.colgate.edu/~integers/q69/q69.pdf).
It bounds \(z\) by \(128d^2\) for \(d\) coprime to 6 and \(11d^2\) otherwise,
and checks \(d\le128\). The present argument sharpens both cutoffs using an
explicit **signed** second-order error and extends the exact range.
The [Lind–Singmaster case \(d=1\)](https://www.fq.math.ca/Scanned/13-4/singmaster.pdf)
is excluded throughout. This is not a new bound on global multiplicity,
and makes no claim about unequal shifts or all \(d>256\).

## 1. Centering and a coarse uniform enclosure

Write \(x=n-(d-1)/2\), \(y=k+(d+1)/2\), \(s=z^2\), and \(E=s-xy\).
The identity \(x-y=z-\tfrac12\) is exact. For a positive integer \(m\)
let \(C_m(t)=\prod_{j=-(m-1)/2}^{(m-1)/2}(t+j)\), with step 1.
Write \(J_m\) for the strictly positive \(j\) in this product, and set
\[
 S_m=\sum_{j\in J_m}j^2=\frac{m(m^2-1)}{24},
 \qquad T_m=\sum_{j\in J_m}j^4=\frac{m(m^2-1)(3m^2-7)}{480}.
\]
These formulas follow by summing the second and fourth powers of the centered
arithmetic progression and taking half. Cancellation of factorials gives
\(C_{2d}(z)=C_d(x)C_d(y)\). All factors are positive on the stated domain.
Bounding the factors on each side by the extremal or centered terms gives
\[
          xy\ge(z-d)^2,\qquad (x-d/2)(y-d/2)\le z^2 .
\]
The second inequality and \(x>y\) give \(k\le z-\tfrac12\) and
\(n=z+k+d-\tfrac12\le2z+d-1\).
When \(z\ge8d\), the first inequality gives \(y>z/2\):
if \(y\le z/2\), then \(x=y+z-\tfrac12<3z/2\), so
\(xy\le3z^2/4<(z-d)^2\).
Consequently \(x>z\) on this range.

Set \(u=E/s,\ \alpha=\log(s/(xy))=-\log(1-u)\), and
\[
 L_m(t)=-\sum_{j\in J_m}\log(1-j^2/t^2).
\]
The positive factorizations \(C_m(t)=t^m\prod_{j\in J_m}(1-j^2/t^2)\)
give \(d\alpha=L_{2d}(z)-L_d(x)-L_d(y)\). In these three sums,
\(0\le j^2/t^2\le d^2/s\le1/64\). Using
\(-\log(1-v)\le(4/3)v\) for these \(v\), and
\(x^{-2}+y^{-2}<5/s\), yields
\[
    |\alpha|\le (13/18)d^2/s<1/64 .
\]
Thus \(|E|\le s\,e^{|\alpha|}|\alpha|<d^2\), since
\(e^{|\alpha|}\le64/63\).
For \(|v|\le 1/2\), the first-order log remainder is bounded in absolute
value by \(v^2\) by the power series. Define
\[
 A=s(x^{-2}+y^{-2}),\quad B=s^2(x^{-4}+y^{-4}),\quad q=1/z,\quad
 C=s(A-3+q),\quad E_*=(5d^2+1)/24.
\]
As \(x^2+y^2=3s-z+\tfrac14-2E\), we have the exact identities
\[
 C=\frac{(4-2q)E+\tfrac14-(3-q)E^2/s}{(1-u)^2},
 \quad B=A^2-\frac2{(1-u)^2},
 \quad E_*=\frac{S_{2d}-3S_d}{d}.
\]
Equivalently \(A=(3-q+(\tfrac14-2E)/s)/(1-u)^2\).
From \(|u|\le1/64\) and
\(|(1-u)^{-2}-1|<3|u|\) for nonzero \(u\)
(with equality \(0\) at \(u=0\)), this gives \(|C|<12d^2\):
the contribution of \(3-q\) is at most \(9d^2\), and the other
contribution is bounded by \((\tfrac14+2d^2)(64/63)^2<3d^2\).

The sum of the log remainders at \(z,x,y\) is at most
\((T_{2d}+17T_d)/s^2\), since \(B<17\) follows from \(x>z,\ y>z/2\).
For the moment use \(T_{2d}\le d^2S_{2d}\le d^5/3\) and
\(T_d\le(d^2/4)S_d\le d^5/96\).
The remainder from \(\alpha-u\) contributes at most \(E^2/s\) in the
equation for \(E\), and the \(C/s\) term contributes at most
\((S_d/d)|C|/s\).
It follows from the first-order log equation that
\[
        \left|E-E_*-\frac{d^2-1}{24z}\right|<\frac{3d^4}{s},
                       \qquad z\ge8d. \tag{1}
\]
Here the three dimensionless error coefficients are bounded by
\(49/96,\ 1,\ 12/24\), respectively.

To establish the fallback cutoff for \(d<8\), suppose \(z\ge16d^2\).
Equation (1) gives \(|E|<d^2/4\), since after division by \(d^2\)
the sum \(7/32+1/(24\cdot64)+3/(256\cdot4)\) is less than \(1/4\).
The same estimate for \(C\) now gives \(|C|<3d^2\).
Using the exact fourth-moment formulas gives
\((T_{2d}+17T_d)/d< (49/160)d^4\).
The three error coefficients improve to \(49/160,\ 1/16,\ 1/8\),
whose sum is less than \(1/2\). Thus
\[
        \left|E-E_*-\frac{d^2-1}{24z}\right|<\frac{d^4}{2s}
                       \qquad(z\ge16d^2).
\]
This puts \(E-E_*\) strictly between 0 and \(1/24\), using
\(d^2-1\ge3d^2/4\). But \(E\in\frac14\mathbb Z\) and
\(E_*\in\frac1{24}\mathbb Z\), a contradiction. The fallback therefore
in fact holds for every \(d\ge2\).

## 2. Signed refinement

Now assume \(d\ge8,\ z\ge8d\). Equation (1) first gives
\[
 |E|/d^2 < 21/100+1/(24\cdot64)+3/64<13/50.
\]
The formula for \(A\) then yields \(|C|<3d^2\): use
\(9(13/50)+(1/256+2(13/50))(64/63)^2<3\).
Applying exact fourth moments as above, the new total coefficient in (1) is
less than \(49/160+(13/50)^2+1/8<1/2\).
In particular
\[
         1/5<E/d^2<11/50,\qquad 0<u<1/256 .
\]
The lower bound uses \(5/24-1/128>1/5\), and the upper bound uses
\(21/100+1/(24\cdot64)+1/128<11/50\).
Using \(q\le1/64\) in the identities for \(C,B\) now gives
\[
          (79/100)d^2<C<(9/10)d^2,\qquad
                         34/5<B<36/5.       \tag{2}
\]
For \(C\), bound its numerator below by \((4-2q-3u)E\) and above by
\(4E+1/4\). For \(B\), \(3-q<A<3+(9/10)/64\), so
\((3-1/64)^2-2(256/255)^2<B<(3+(9/10)/64)^2-2\).

For \(v\in[0,1)\), set \(R(v)=-\log(1-v)-v-v^2/2\),
so \(0\le R(v)\le v^3/[3(1-v)]\). Let \(R_z,R_x,R_y\)
be its sums on the respective lists of log arguments.
The exact second-order log equation is
\[
 \begin{aligned}
 s\left(E-E_*-\frac{d^2-1}{24z}\right)
 &=\frac{T_{2d}-T_d B}{2d}
   +\frac{s^2}{d}(R_z-R_x-R_y)
   -s^2(\alpha-u)-\frac{S_d C}{d}.              \tag{3}
 \end{aligned}
\]
The nonnegative terms admit the following bounds (all entries after
multiplication by \(d^4\)):
\[
\begin{array}{c|c|c}
\text{term}&\text{lower coefficient}&\text{upper coefficient}\\ \hline
 T_{2d}/(2d) & 19/200 & 1/10\\
 T_d B/(2d)  & 1/50 & (36/5)/320\\
 s^2 R_z/d   & 0 & 1/500\\
 s^2(R_x+R_y)/d &0 & 1/1000\\
 s^2(\alpha-u)&1/50&1/40\\
 S_d C/d &4/125&3/80
\end{array}
\]
The moment rows follow from the exact formulas and (2); for example
\(T_d/d>(59/10000)d^4\).
The \(\alpha-u\) row follows by the log series, between \(E^2/2\)
and \(E^2/[2(1-u)]\) after multiplying by \(s^2\).
For the cubic remainders, use
\(\sum_{j\in J_{2d}}j^6\le d^2T_{2d}< d^7/5\) and
\(\sum_{j\in J_d}j^6\le(d^2/4)T_d<d^7/640\).
Here \(s^3(x^{-6}+y^{-6})<65\) and \(d^2/s\le1/64\), giving the
two upper coefficients at most \(1/(15\cdot63)\) and
\(65/(1920\cdot63)\), respectively.
Combining the table in (3), the lower coefficient is positive, and
the upper one is at most \(1/10+1/500-2/50-4/125=3/100\).
Thus, with strict inequalities,
\[
  0<E-E_*-\frac{d^2-1}{24z}<\frac{3d^4}{100z^2}
                   \qquad (d\ge8,\ z\ge8d).       \tag{4}
\]

For odd \(d\), \(x,y\) are integers and \(E\in 1/4+\mathbb Z\).
For even \(d\) it is enough to use \(E\in\frac14\mathbb Z\).
If \(d\equiv2,4\pmod6\), the next quarter-lattice point strictly
above \(E_*\) has distance \(1/8\).
The upward gap is at least \(5/24\) in all other classes:
for \(d\equiv0,\pm1\pmod6\) the quarter-lattice gaps are \(5/24,1/4,1/4\);
for \(d\equiv3\pmod6\) use \(d^2\equiv9\pmod{24}\) and the
odd lattice, giving \(1/3\). From (4), if \(z\ge r d^2\),
\[
                   0<E-E_* <\frac1{24r}+\frac{3}{100r^2}.
\]
For \(r=7/10\) the upper bound is less than \(1/8\), and for \(r=1/2\)
it is less than \(5/24\). This excludes all solutions at or above
the claimed thresholds.

## 3. Exact small-shift replay

Run [verify_factor_singmaster_balanced_shift_drift.py](verify_factor_singmaster_balanced_shift_drift.py)
with Python 3 (optionally `--max-shift 256`). For each
\(v=n-k\) below the analytic cutoff, set \(Z=2v-2d+1\) and
\(Y=2k+d+1\). The integer \(F=4E=Z^2-Y(Y+Z-1)\) is strictly
decreasing with \(k\). Equations (1) and (4), after clearing
denominators, bound \(F\) in an integer interval. Exact integer square
roots then recover the full interval of possible \(k\)'s. For \(z<8d\)
there is no analytic enclosure beyond the domain bound. In both cases the
strictly increasing right product in \(k\) is checked by exact integer binary
search. Every accepted answer
is checked against both integer binomial coefficients. The script also
compares its enumeration with direct enumeration for \(d=2,3,4\), and
checks the displayed rational inequality constants, moment identities, and
27 independent exact real-branch brackets by substituting the two endpoints
of (4) into the centered products.
