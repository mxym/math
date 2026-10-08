# Sharp mass-constrained Gaussian propeller fans

**Research note, 7 October 2026.** The new results below concern
**planar conical fan partitions**, not arbitrary Gaussian partitions.
The latter, unrestricted problem is covered by OpenAI's Gaussian
propeller theorem [OAI-096]. We do not claim historical priority.

## 1. Definitions and Gaussian reduction

Fix integers \(n\ge2,k\ge3\) and \(0\le\varepsilon\le 2\pi/k\).
A fan partition \((A_1,\dots,A_k)\) of \(\mathbb R^n\) is the
product with \(\mathbb R^{n-2}\) of consecutive planar sectors of
angles \(\theta_i\ge\varepsilon\), with \(\sum_i\theta_i=2\pi\).
Zero-angle sectors are permitted at \(\varepsilon=0\).
Write \(\gamma_n\) for standard Gaussian probability measure and
\[
 P(\theta)=\sum_{i=1}^k
   \left\|\int_{A_i}x\,d\gamma_n(x)\right\|_2^2,\qquad
 f(t)=\sin^2(t/2)=\frac{1-\cos t}{2}.
\]
Here \(\gamma_n(A_i)=\theta_i/(2\pi)\); thus the angle floor means
each cell has Gaussian mass at least \(\varepsilon/(2\pi)\).

**Lemma 1 (polar identity).** For every admissible fan,
\[
             P(\theta)=\frac1{2\pi}\sum_{i=1}^k f(\theta_i).
 \tag{1}
\]

*Proof.* A planar sector of angle \(\theta\) centered on unit
direction \(u\) has Gaussian moment
\[
 \frac1{2\pi}\left(\int_0^\infty r^2e^{-r^2/2}\,dr\right)
 2\sin(\theta/2)u
 =\frac{\sin(\theta/2)}{\sqrt{2\pi}}u.
\]
Orthogonal components vanish by Gaussian independence and centering.
The radial integral equals \(\sqrt{\pi/2}\). Squaring completes the
proof. \(\square\)

For \(r=1,2,3\), set
\[
 a_r(k,\varepsilon)=\frac{2\pi-(k-r)\varepsilon}{r},
 \quad
 V_r(k,\varepsilon)=r f(a_r)+(k-r)f(\varepsilon).
 \tag{2}
\]

## 2. Exact finite-candidate theorem for every k

**Theorem 2 (three-candidate principle).** For every \(k\ge3\) and
\(0\le\varepsilon\le2\pi/k\),
\[
 \boxed{\max_{\theta_i\ge\varepsilon,\,\sum\theta_i=2\pi}
 P(\theta)=\frac1{2\pi}\max\{V_1,V_2,V_3\}.}
 \tag{3}
\]
A maximizing angle multiset can always be chosen with \(r\) angles
\(a_r\) and \(k-r\) angles \(\varepsilon\) for one winning \(r\in
\{1,2,3\}\).

*Proof.* The constraint simplex is compact. If
\(\varepsilon=2\pi/k\), every angle is forced to \(2\pi/k\), and
all three candidates equal that vector. Otherwise take a maximizer.
Let \(r\) count the *free* coordinates strictly above \(\varepsilon\).
The case \(r=1\) is already the \(V_1\) configuration.

For \(r\ge2\), perturbing any two free angles by \((+t,-t)\) gives
the stationarity equations
\(\sin\theta_i=\sin\theta_j\).
No free angle can exceed \(\pi\), since another free angle would
lie in \((0,\pi)\), producing opposite signs. If a free angle
equals \(\pi\), stationarity forces all other free angles equal
\(\pi\), hence exactly two angles \(\pi,\pi\) with
\(\varepsilon=0\), which is \(V_2\).

Otherwise, the free angles are in \((0,\pi)\), and for some
\(s\in(0,\pi/2]\) each equals either \(s\) or \(\pi-s\).
If two free angles are strictly below \(\pi/2\), the
\((+t,-t)\) perturbation at two such angles has second derivative
\(2f''(s)=\cos s>0\), impossible at a maximum.
If exactly one free angle is \(s<\pi/2\) and the other \(r-1\)
are \(\pi-s\), the perturbation
\[
 (\underbrace{(r-1)t}_{\text{small angle}},
   \underbrace{-t,\dots,-t}_{r-1\text{ large angles}})
\]
has vanishing first derivative and second derivative
\[
 (r-1)^2 f''(s)+(r-1)f''(\pi-s)
 =\frac{(r-1)(r-2)}2\cos s.
\]
It is strictly positive for \(r\ge3\). For \(r=2\) instead,
\(f(s)+f(\pi-s)=1\). The smaller free angle can be decreased
to the floor \(\varepsilon\) and the other increased by the
same amount, preserving both the sum and score; the resulting
configuration is \(V_1\).

Every remaining maximizing free-angle set is uniform, with
common angle \(\alpha\). It cannot have \(\alpha<\pi/2\) when
\(r\ge2\), by the positive second derivative
\(2f''(\alpha)>0\). Hence \(\alpha\ge\pi/2\), and \(r\le4\).
For \(r\le3\), the sum constraint gives \(\alpha=a_r\),
yielding \(V_r\).

If \(r=4\), all free angles must equal \(\pi/2\), and any
remaining cells have zero angles. But replacing four quarter-turn
angles by
\[
 (\pi/2+t,\pi/2+t,\pi/2+t,\pi/2-3t)
\]
is feasible for small positive \(t\), since these are strictly
free (\(\varepsilon<\pi/2\)); it increases their score from \(2\)
to
\[
 2+\frac{3\sin t-\sin3t}{2}=2+2\sin^3t>2.
\]
Thus \(r=4\) cannot maximize.

We have proved that a global maximum is equal to one of the
three displayed candidate values. Conversely, the candidate
angle vectors are all feasible since
\(a_r-\varepsilon=(2\pi-k\varepsilon)/r\ge0\).
This proves (3). \(\square\)

**Corollary 3 (small-mass penalty).** For each fixed \(k>3\),
as \(\varepsilon\downarrow0\),
\[
 \max P(\theta)=\frac9{8\pi}
 -\frac{\sqrt3(k-3)}{8\pi}\varepsilon
 +O_k(\varepsilon^2).
 \tag{4}
\]
If the minimum mass is \(q=\varepsilon/(2\pi)\), the first-order
penalty is \(\sqrt3(k-3)q/4\). For \(k=3\), the maximum is
\(9/(8\pi)\) for all admissible floors.

*Proof.* At zero floor, \((V_1,V_2,V_3)=(0,2,9/4)\).
Hence by continuity \(V_3\) uniquely wins for all sufficiently
small positive \(\varepsilon\). Differentiate \(V_3\) using
\(f'(2\pi/3)=\sqrt3/4\), \(f'(0)=0\).
For \(k=3\), the equiangular triple remains feasible and gives
the stated maximum directly from Theorem 2. \(\square\)

## 3. High-mass phase, complete equality cases and stability

Put \(T=2\pi-k\varepsilon\) and
\(g(t)=f(\varepsilon+t)-f(\varepsilon)\) for \(0\le t\le T\).
The elementary identity
\[
 g(s+t)-g(s)-g(t)
 =2\cos\left(\varepsilon+\frac{s+t}{2}\right)
       \sin\frac{s}{2}\sin\frac{t}{2}
 \quad(s,t\ge0,\ s+t\le T)
 \tag{5}
\]
governs the phase transition.

**Theorem 4 (sharp high-mass phase).** For \(k\ge5\) and
\(\pi/(k-2)\le\varepsilon\le2\pi/k\),
\[
 \boxed{\max P(\theta)
 =\frac{f(2\pi-(k-1)\varepsilon)
             +(k-1)f(\varepsilon)}{2\pi}.}
 \tag{6}
\]
For \(\varepsilon>\pi/(k-2)\), the **only** maximizing angular
multiset has one angle \(2\pi-(k-1)\varepsilon\) and
\(k-1\) angles \(\varepsilon\) (all equal at the upper endpoint).

At \(\varepsilon=\pi/(k-2)\), the **complete equality set**
comprises \(k-2\) angles equal to \(\varepsilon\) and two
angles \(a,b\ge\varepsilon\) with \(a+b=\pi\).
This includes configurations with one enlarged angle, and the
critical maximum equals
\[
 \frac{1+(k-2)\sin^2(\pi/[2(k-2)])}{2\pi}.
 \tag{7}
\]

*Proof.* Write \(t_i=\theta_i-\varepsilon\ge0\), so
\(\sum_i t_i=T\). The threshold ensures
\[
 \varepsilon+\frac{T}{2}
     =\pi-\frac{k-2}{2}\varepsilon\le\frac{\pi}{2}.
\]
The cosine in (5) is nonnegative for every permitted
\(s+t\), so \(g\) is superadditive. Merging all positive
\(t_i\)'s gives an objective at least as large and leaves
one excess equal to \(T\). This proves (6).

Above the threshold, the cosine is strictly positive for all
permitted merges, so a maximizing excess vector has at most
one positive component. At the threshold, a merge of two
positive components has zero gain precisely if their sum
equals \(T\). With three or more positive components, the
first merge has sum smaller than \(T\) and strictly raises
the score. Exactly two positive components have sum \(T\),
and their merge preserves the score. This proves all equality
cases. The critical pair obeys
\(a+b=2\varepsilon+T=\pi\), whence
\(f(a)+f(b)=1\), proving (7). \(\square\)

For \(k=4\), the threshold \(\pi/(k-2)=\pi/2\)
coincides with the unique feasible endpoint.

**Theorem 5 (quantitative sparsity stability).**
Under the hypotheses of Theorem 4, put
\(t_i=\theta_i-\varepsilon\). Then
\[
 \boxed{\max P(\theta)-P(\theta)
 \ge\frac{\cos(\varepsilon+T/2)}{\pi^3}
                    \sum_{i<j}t_it_j.}
 \tag{8}
\]
For \(\varepsilon>\pi/(k-2)\) the coefficient is positive.

*Proof.* At each successive merge of excesses \(s,t\),
formula (5) and monotonicity of cosine on \([0,\pi/2]\)
give a gain at least
\(2c\sin(s/2)\sin(t/2)\), where
\(c=\cos(\varepsilon+T/2)\ge0\).
Here \(0\le s,t\le T<\pi\).
Concavity of sine on \([0,\pi/2]\) implies
\(\sin(s/2)\ge s/\pi\), so the gain is
at least \(2cst/\pi^2\).
When \(t_1,\ldots,t_k\) are merged successively,
the sum of these products \(st\) is exactly
\(\sum_{i<j}t_it_j\).
Divide the total gain by \(2\pi\) to obtain (8). \(\square\)

**Example 6 (critical five-sector continuum).**
For \(k=5\), \(\varepsilon=\pi/3\), equivalently
minimum Gaussian cell mass \(1/6\), the maximum equals
\(7/(8\pi)\), with all maximizing angle multisets
\[
       (\pi/3,\pi/3,\pi/3,a,\pi-a),
             \quad \pi/3\le a\le2\pi/3.
\]
Thus maximizers are not isolated at the mass transition.

## 4. Four-sector closed form and cubic symmetry breaking

**Theorem 7 (complete four-sector formula).**
For \(0\le\varepsilon\le\pi/2\),
\[
 \boxed{\displaystyle
 M_4(\varepsilon)=
 \frac{1+\sin^3((\pi/2-\varepsilon)/3)}{\pi}.}
 \tag{9}
\]
For \(\varepsilon<\pi/2\), the only maximizing angular
multiset is \(((2\pi-\varepsilon)/3,
 (2\pi-\varepsilon)/3,(2\pi-\varepsilon)/3,\varepsilon)\).
At \(\varepsilon=\pi/2\), all four angles are \(\pi/2\).
Writing \(\varepsilon=\pi/2-s\), the exact cubic
symmetry-breaking law is
\[
 M_4(\varepsilon)-1/\pi
 =\sin^3(s/3)/\pi
 =s^3/(27\pi)+O(s^5).
 \tag{10}
\]

*Proof.* Let \(t=(\pi/2-\varepsilon)/3\in[0,\pi/6]\).
Using \(\sin3t=3\sin t-4\sin^3t\), the three
candidate scores in Theorem 2 simplify to
\[
 V_1=2-2\sin^3(3t),\quad
 V_2=2,\quad
 V_3=2+2\sin^3t.
\]
For \(t>0\), \(V_3>V_2\ge V_1\).
Theorem 2 gives (9). Its proof also gives uniqueness
here: nonuniform stationary pairs of free angles can
exist only if \((k-2)\varepsilon=\pi\), which for
\(k=4\) forces the endpoint \(\varepsilon=\pi/2\).
All other maximizers have equal free angles, and
the strict candidate comparison forces exactly three free
angles equal to \(a_3\). At the endpoint all angles are
forced. The Taylor expansion of sine proves (10).
\(\square\)

## 5. Best-constant global stability of three-sector fans

**Theorem 8 (sharp angular quadratic deficit).**
For all nonnegative \(\theta_1,\theta_2,\theta_3\)
summing to \(2\pi\),
\[
 \boxed{\displaystyle
 \frac9{8\pi}-P(\theta)
 \ge\frac{3}{16\pi^3}
             \sum_{i=1}^3(\theta_i-2\pi/3)^2.}
 \tag{11}
\]
The coefficient \(3/(16\pi^3)\) is **globally optimal**.
Equality occurs only at the equiangular triple and at
permutations of \((0,\pi,\pi)\).
In particular if every cell has positive mass, equality
requires equiangularity.

*Proof.* Let \(x_i=\theta_i/2\ge0\);
then \(x_1+x_2+x_3=\pi\).
Permute indices so \(x=x_1=\min_i x_i\in[0,\pi/3]\).
Write
\[
 x_2=(\pi-x)/2+t,\qquad
 x_3=(\pi-x)/2-t,
          \qquad |t|\le(\pi-x)/2\le\pi/2.
\]
The classical triangle identity
\(\sum_i\sin^2x_i=2+2\prod_i\cos x_i\)
and cosine addition give the exact defect decomposition
\[
 D:=\frac94-\sum_i\sin^2x_i
 =\left(\cos x-\frac12\right)^2
                     +2\cos x\sin^2t.
 \tag{12}
\]
The variance identity is likewise exact:
\[
 \sum_i(x_i-\pi/3)^2
         =\frac32(x-\pi/3)^2+2t^2.
 \tag{13}
\]
Since cosine is concave on \([0,\pi/3]\),
it lies above the chord joining \((0,1)\) to
\((\pi/3,1/2)\). Hence
\[
 \cos x-\frac12\ge\frac{3}{2\pi}(\pi/3-x),
 \quad
 \left(\cos x-\frac12\right)^2
       \ge\frac9{4\pi^2}(x-\pi/3)^2.
\]
Moreover \(\cos x\ge1/2\), while
\(\sin|t|\ge 2|t|/\pi\) on \(|t|\le\pi/2\).
Consequently,
\[
 2\cos x\sin^2t\ge\frac4{\pi^2}t^2
                          \ge\frac3{\pi^2}t^2.
\]
Combining with (12)--(13) yields
\[
 D\ge\frac{3}{2\pi^2}\sum_i(x_i-\pi/3)^2.
\]
Now \(9/(8\pi)-P=D/(2\pi)\), and
\(\theta_i-2\pi/3=2(x_i-\pi/3)\),
giving (11).

For equality the preceding \(t\) estimate is strict
whenever \(t\ne0\), so \(t=0\). Strict concavity of
cosine between its chord endpoints forces
\(x=0\) or \(x=\pi/3\), corresponding respectively
to \((0,\pi,\pi)\) or \((2\pi/3,2\pi/3,2\pi/3)\).
Both attain equality. The degenerate triple
fixes the global best possible constant. \(\square\)

## 6. Complete two-transition phase diagram

The exact three-candidate formula admits a sharper qualitative
description: as the minimum mass increases, the optimal number of
non-minimal cells changes **three, then two, then one**.

For \(T=2\pi-k\varepsilon>0\), put
\[
 \delta=T/6,\quad z=\varepsilon+2\delta,\quad
 \phi(\delta)=\arctan\!\left(
            \frac{\sin\delta}{2+\cos\delta}\right).
\]
The following exact trigonometric comparison identities
will be useful:
\[
 \begin{aligned}
 V_2-V_1
   &=-2\cos(\varepsilon+T/2)\sin^2(T/4),\\
 V_3-V_2
   &=(\cos\delta-1)
     \big[(2+\cos\delta)\cos z+\sin\delta\sin z\big]\\
   &=(\cos\delta-1)
       \sqrt{5+4\cos\delta}\cos(z-\phi(\delta)).
 \end{aligned} \tag{14}
\]
The first follows by midpoint addition for cosine. For the
second, expand the three cosines in
\(V_3-V_2=[-3\cos(\varepsilon+2\delta)
 +2\cos(\varepsilon+3\delta)+\cos\varepsilon]/2\)
and use
\(\cos2\delta=2\cos^2\delta-1\).

**Theorem 9 (unique two-stage symmetry breaking).**
For every \(k\ge5\) there is a unique
\[
 0<\varepsilon_*(k)<\frac{\pi}{k-2}
\]
such that the angular maximizing patterns are exactly as follows,
where a pattern with \(r\) free angles means \(r\) angles \(a_r\)
and \(k-r\) floor angles \(\varepsilon\).

| Minimum angle | Maximizing angular multisets |
|---|---|
| \(0\le\varepsilon<\varepsilon_*(k)\) | only the \(r=3\) pattern |
| \(\varepsilon=\varepsilon_*(k)\) | exactly the \(r=2\) and \(r=3\) patterns |
| \(\varepsilon_*(k)<\varepsilon<\pi/(k-2)\) | only the \(r=2\) pattern |
| \(\varepsilon=\pi/(k-2)\) | the complete two-excess continuum in Theorem 4 |
| \(\pi/(k-2)<\varepsilon\le2\pi/k\) | only the \(r=1\) pattern |

Here \(\varepsilon_*(k)\) is the unique root in the stated
interval of the explicit equation
\[
 (2+\cos\delta)\cos(\varepsilon+2\delta)
     +\sin\delta\sin(\varepsilon+2\delta)=0,
 \qquad \delta=\frac{2\pi-k\varepsilon}{6}.
 \tag{15}
\]
For \(k=4\), the \(r=3\) pattern wins at every
\(0\le\varepsilon<\pi/2\), and the endpoint is equiangular.

*Proof.* At \(\varepsilon=0\), one has
\(\delta=\pi/3,\ z=2\pi/3\), and
\[
 z-\phi(\delta)=\frac{2\pi}{3}
             -\arctan(\sqrt3/5)>\frac\pi2,
\]
because \(\arctan(\sqrt3/5)<\pi/6\).
At the upper feasibility endpoint \(T=0\),
\(z-\phi(\delta)=2\pi/k\le\pi/2\),
with strict inequality for \(k\ge5\).

To see that the crossing is unique, differentiate:
\[
 \phi'(\delta)=\frac{1+2\cos\delta}{5+4\cos\delta}
         \le\frac13
      \quad(0\le\delta\le\pi/3).
\]
Since \(z'_\varepsilon=1-k/3\) and
\(\delta'_\varepsilon=-k/6\),
\[
 \frac{d}{d\varepsilon}(z-\phi(\delta))
 \le 1-\frac{k}{3}+\frac{k}{18}
 =1-\frac{5k}{18}<0
 \quad(k\ge4).
\]
The argument \(z-\phi(\delta)\) stays within \([0,\pi]\).
Consequently its cosine changes sign exactly once
(for \(k=4\), only at the upper endpoint).
Because \(\cos\delta-1<0\) whenever \(T>0\),
identity (14) shows \(V_3>V_2\) before that
crossing and \(V_2>V_3\) after it.

The first identity in (14) shows
\(V_2>V_1\) below \(\varepsilon=\pi/(k-2)\),
\(V_2=V_1\) there, and \(V_1>V_2\)
above it (as long as \(T>0\)).
At the critical value, Theorem 4 proves
\(V_1=V_2\) is optimal and \(V_3\) is
strictly suboptimal for \(k\ge5\), because
the \(r=3\) pattern has three positive
excesses. Hence the \(V_3/V_2\) crossing
lies strictly below the critical value.
Above that critical value, Theorem 4
makes \(V_1\) the unique winning candidate.

Theorem 2 and its stationary-point proof
classify every maximizer: uniform free
angles except for the nonuniform two-angle
continuum, which can occur only at
\((k-2)\varepsilon=\pi\). Thus the table
gives the full equality classification,
not merely the maximal values. \(\square\)

## 7. Exact large-k transition scale

Define the explicit constant
\[
 \mu_*=
 2\pi-6\arccos\!\left(\frac{\sqrt{33}-1}{8}\right).
 \tag{16}
\]
This is positive and smaller than \(\pi\).

**Theorem 10 (asymptotic first phase boundary).**
As \(k\to\infty\),
\[
      \boxed{\displaystyle
      \varepsilon_*(k)=\frac{\mu_*}{k}+O(k^{-2})}.
 \tag{17}
\]
The second phase boundary
\(\pi/(k-2)=\pi/k+O(k^{-2})\).
Thus the two transitions remain distinct at leading order.

*Proof.* Put \(\mu=k\varepsilon\) in (15), so that
\(\delta=(2\pi-\mu)/6\) and
\(z=2\delta+\mu/k\).
As \(k\to\infty\), the left side of (15),
uniformly for \(\mu\) in compact subsets of \((0,\pi)\),
converges with an \(O(k^{-1})\) error to
\[
 H(\mu)=(2+\cos\delta)\cos(2\delta)
              +\sin\delta\sin(2\delta)
        =4\cos^2\delta+\cos\delta-2.
\]
The increasing positive root of \(4c^2+c-2=0\) is
\(c_*=(\sqrt{33}-1)/8\in(1/2,1)\).
Hence \(H\) has one zero at
\(\mu_*=2\pi-6\arccos c_*\), which belongs to
\((0,\pi)\); \(H(0)<0\), \(H(\pi)>0\).
Furthermore \(H'(\mu_*)>0\): indeed
\(\partial_\mu\cos\delta=\sin\delta/6>0\) and
\(8c_*+1>0\).

Theorem 9 supplies one zero \(\mu_k=k\varepsilon_*(k)\)
in \((0,k\pi/(k-2))\). For fixed
\(0<\mu_-<\mu_*<\mu_+<\pi\), the signs of
\(H(\mu_-),H(\mu_+)\) persist at large \(k\),
so \(\mu_k\) lies between these bounds.
Local uniform convergence and the lower bound on
\(H'\) near its simple zero give
\(|\mu_k-\mu_*|=O(1/k)\)
(by the mean value theorem).
Dividing by \(k\) proves (17).
The second-boundary expansion is algebraic. \(\square\)

## 8. Heterogeneous minimum masses: a polynomial-size exact reduction

The uniform mass condition in Theorem 2 is unnecessary for the
small-support principle. This provides an exact answer also when
the lower mass varies from sector to sector.

**Theorem 11 (arbitrary unequal angle floors).**
Let \(k\ge3\) and fix any real numbers
\(\ell_i\ge0\) with \(\sum_{i=1}^k\ell_i\le2\pi\).
For each nonempty set \(S\subseteq\{1,\dots,k\}\)
of cardinality \(r=|S|\le3\), put
\[
 a_S=\frac{2\pi-\sum_{j\notin S}\ell_j}{r},
 \quad
 W_S=r f(a_S)+\sum_{j\notin S}f(\ell_j).
 \tag{18}
\]
Call \(S\) admissible when
\(a_S\ge\max_{i\in S}\ell_i\).
There is at least one admissible singleton, and
\[
 \boxed{\displaystyle
 \max_{\theta_i\ge\ell_i,\ \sum\theta_i=2\pi}
 P(\theta)
 =\frac1{2\pi}
   \max_{\substack{S\ne\varnothing,\ |S|\le3\\
                     S\ {\rm admissible}}} W_S.}
 \tag{19}
\]
Consequently, even with completely heterogeneous minimum
Gaussian cell masses \(\ell_i/(2\pi)\), the exact global
optimization reduces to at most
\[
                 k+\binom{k}{2}+\binom{k}{3}
\]
explicit candidate values, a **cubic-size** list.

*Proof.* At least one singleton is admissible:
for any \(i\),
\[
 2\pi-\sum_{j\ne i}\ell_j
 =\ell_i+(2\pi-\sum_j\ell_j)\ge\ell_i.
\]
Each admissible \(S\) defines a feasible angle vector
by setting \(\theta_i=a_S\) for \(i\in S\), and
\(\theta_j=\ell_j\) otherwise. It remains to prove
that some such vector is optimal.

Choose any maximizer on the compact feasible polytope.
Let \(F=\{i:\theta_i>\ell_i\}\). If \(F\) is empty,
the vector is already represented by any admissible
singleton (all floors sum \(2\pi\)).
If \(F\) has one element, it is represented by that
singleton. When \(|F|\ge2\), all free coordinates
satisfy \(\sin\theta_i=\sin\theta_j\) by first-order
feasible perturbations.

The remainder of Theorem 2's active-face analysis uses
only the following facts: every constrained coordinate
is fixed at its floor, all free angles are positive, and
their total is at most \(2\pi\). It does **not** use equality
of the different floors. Explicitly, free angles above
\(\pi\) are impossible by opposite derivative signs;
free angles equal to \(\pi\) must form the two-angle
\((\pi,\pi)\) pattern; two free angles below \(\pi/2\)
yield a strictly positive second derivative; and a
single free small angle \(s<\pi/2\) with at least two
larger free angles \(\pi-s\) admits the strictly
positive second derivative
\(\tfrac12(r-1)(r-2)\cos s\).
If there are exactly two free angles \(s,\pi-s\),
their score is \(1\) independent of \(s\). Reduce
the smaller one to **its own** floor \(\ell_i\),
increasing the larger by the same amount. This
preserves the angle sum and objective, leaves only
one free coordinate, and produces a singleton
candidate.

Thus every remaining maximizer has all free angles
equal to some \(\alpha\ge\pi/2\). Their total is
at most \(2\pi\), so there are at most four. Four
equal free angles require all four to be \(\pi/2\),
and every other coordinate to be zero. Since
the four are strictly free, all have floors
strictly below \(\pi/2\), and the cubic perturbation
\((\pi/2+t,\pi/2+t,\pi/2+t,\pi/2-3t)\)
is feasible for sufficiently small \(t>0\)
and strictly increases the objective. Hence at most
three free angles remain.

Writing \(S=F\), the constraint forces their common
value to be \(a_S\). Since these angles exceed their
floors, \(S\) is admissible and the maximum equals
\(W_S/(2\pi)\). The candidate lower bound already
proved yields (19). \(\square\)

Theorems 2 and 11 produce exact finite-dimensional
optimization *certificates*: their formulas are
valid for arbitrary real floors. Rational-angle
specializations admit rigorous trigonometric interval
evaluation as in the companion checker. For
nonuniform floors, the concise two-transition
classification of Theorem 9 need not persist;
Theorem 11 is the correct general statement.


## 9. Universal radial fan reduction

The angular mechanism does not require a Gaussian density.
Let \(X\) be an \(\mathbb R^n\)-valued rotation-invariant random
vector, \(n\ge2\), with
\(\mathbb P(X=0)=0\) and \(0<\mathbb E\|X\|<\infty\).
Let \(R=\sqrt{X_1^2+X_2^2}\) and
\(\rho=\mathbb E R\in(0,\infty)\). Consider the same
cylindrical fan partition and define
\[
 \mathcal P_X(\theta)
 :=\sum_{i=1}^k
 \big\|\mathbb E[X\mathbf1_{A_i}]\big\|_2^2.
\]

**Theorem 12 (radial universality).**
For every rotation-invariant law above, the mass of each
fan cell is \(\theta_i/(2\pi)\) and
\[
 \boxed{\displaystyle
 \mathcal P_X(\theta)
     =\frac{\rho^2}{\pi^2}
           \sum_{i=1}^k\sin^2(\theta_i/2).}
 \tag{20}
\]
Consequently all maximizer descriptions, phase boundaries
and equality classifications in Theorems 2, 4, 7, 9,
10 and 11 hold **unchanged** under this law; the
optimal *value* equals the corresponding maximum
of \(\sum_i f(\theta_i)\) multiplied by \(\rho^2/\pi^2\).
The deficit inequalities in Theorems 5 and 8 also
transfer with the same positive factor
\(2\rho^2/\pi\) relative to their Gaussian versions.

*Proof.* Rotation invariance makes the polar direction
of \((X_1,X_2)\) uniform on the circle and independent
of its radius \(R\). The assumption of no atom at
\(X=0\) implies \(R>0\) almost surely. Hence
\(\mathbb P(X\in A_i)=\theta_i/(2\pi)\), and
the projected first moment of a centered sector
of angle \(\theta\) is
\[
  \frac{\mathbb ER}{2\pi}
     \int_{-\theta/2}^{\theta/2}
       (\cos t,\sin t)\,dt
 =\frac{\rho}{\pi}\sin(\theta/2)u.
\]
All other first-moment coordinates vanish by
reflection symmetry within each orthogonal direction.
Squaring and summing proves (20).

For the standard Gaussian planar projection,
\(\rho=\sqrt{\pi/2}\), making
\(\rho^2/\pi^2=1/(2\pi)\); thus every
objective, candidate, optimality, equality and deficit
comparison transfers by the factor
\((\rho^2/\pi^2)/(1/(2\pi))=2\rho^2/\pi\).
\(\square\)

The assumption \(\mathbb P(X=0)=0\) matters for
the minimum-cell-*mass* interpretation: an atom at
the origin could be assigned to one or multiple
sector boundaries. Without that assumption, the
angular formula for nonzero mass still holds, but
the cell probabilities need not be \(\theta_i/(2\pi)\).

## 10. Higher-dimensional equal-mass partitions beat planar fans

For nonempty sectors with a positive mass floor the
earlier results apply only within the planar fan class.
There is an exact and substantial obstruction to
promoting the **same numerical optimum** to general
Gaussian partitions.

Write \(\varphi(x)=(2\pi)^{-1/2}e^{-x^2/2}\)
and \(\Phi(x)=\int_{-\infty}^x\varphi(t)\,dt\).
For \(k\ge2\), let
\[
 m_k=\mathbb E\max\{Z_1,\dots,Z_k\},
 \qquad Z_i\stackrel{\rm iid}{\sim}N(0,1).
 \tag{21}
\]
Let \(v_1,\ldots,v_k\) be the vertices of a
unit-norm regular simplex in \(\mathbb R^{k-1}\):
\(\langle v_i,v_i\rangle=1\) and
\(\langle v_i,v_j\rangle=-1/(k-1)\) for \(i\ne j\).
Define its conical Gaussian cells by
\[
 B_i=\{x\in\mathbb R^{k-1}:
       \langle v_i,x\rangle
       \ge\langle v_j,x\rangle\text{ for all }j\}.
\]
Ties form Gaussian-null sets.

**Theorem 13 (strict Gaussian dimension jump).**
Every cell \(B_i\) has Gaussian measure \(1/k\), and
\[
 \boxed{\displaystyle
 \sum_{i=1}^k
 \left\|\int_{B_i}x\,d\gamma_{k-1}(x)\right\|^2
            =\frac{m_k^2}{k-1}.}
 \tag{22}
\]
For **every \(k\ge4\)**, this strictly exceeds the
entire planar fan class at the same prescribed
equal masses:
\[
 \boxed{\displaystyle
 \frac{m_k^2}{k-1}
     >\frac{k}{2\pi}\sin^2\frac{\pi}{k}.}
 \tag{23}
\]
In dimension three with four cells (regular tetrahedral
partition), the value is **exactly**
\[
 \boxed{\displaystyle
 \frac{3}{4\pi}
 \left(1+\frac{2}{\pi}\arcsin\frac13\right)^2
     >\frac1\pi .}
 \tag{24}
\]
Furthermore, as \(k\to\infty\), the ratio between
the two sides of (23) satisfies
\[
 \boxed{\displaystyle
 \frac{m_k^2/(k-1)}
 {\,k\sin^2(\pi/k)/(2\pi)}
              \sim \frac4\pi\log k.}
 \tag{25}
\]
In particular, the higher-dimensional improvement
is unbounded as the number of equal-mass cells grows.

*Proof of the exact simplex objective.* The
Gaussian scores \(Y_i=\langle v_i,G\rangle\)
have the same joint law as
\[
 \sqrt{\frac{k}{k-1}}(Z_i-\bar Z),
 \qquad \bar Z=k^{-1}\sum_jZ_j,
\]
as is seen from their covariance matrices.
Consequently
\[
 L:=\mathbb E\max_iY_i
        =\sqrt{\frac{k}{k-1}}\,m_k.
\]
The symmetry group of the simplex permutes
the Gaussian cells transitively, so each has
mass \(1/k\). The subgroup fixing \(i\)
forces \(b_i=\int_{B_i}x\,d\gamma\) to be a
multiple \(c v_i\), where \(c\) is the same
for every \(i\). Since the scores select their
own maximizing cells,
\[
 L=\sum_i\langle v_i,b_i\rangle=kc.
\]
Thus \(\sum_i\|b_i\|^2=kc^2=L^2/k
=m_k^2/(k-1)\), proving (22).
The unique equal-mass planar fan
has all \(\theta_i=2\pi/k\), giving the
right side of (23) by (1).

*Proof of the four-cell formula.* The maximum
\(M_k=\max_iZ_i\) has density
\(k\varphi(x)\Phi(x)^{k-1}\).
Integration by parts using
\(x\varphi(x)=-\varphi'(x)\) yields
\[
 m_k=k(k-1)\int_{\mathbb R}
             \varphi(x)^2\Phi(x)^{k-2}\,dx
     =\frac{k(k-1)}{2\sqrt\pi}
           \mathbb E[\Phi(W)^{k-2}],
 \tag{26}
\]
where \(W\sim N(0,\tfrac12)\). Put
\(H=2\Phi(W)-1\), which is odd in \(W\).
A standard geometric proof of the bivariate
normal sign identity gives
\[
 u:=\mathbb EH^2
  =\frac2\pi\arcsin\frac13.
 \tag{27}
\]
For completeness, conditionally on \(W\),
\(H=\mathbb E[\operatorname{sgn}(W-Z)\mid W]\).
Using two independent standard normals
\(Z,Z'\), the pair
\((W-Z,W-Z')\) is centered bivariate normal
with correlation \(1/3\). Its sign-product
expectation equals \(2\arcsin(1/3)/\pi\):
write the pair as two unit-length linear
forms of a standard isotropic planar
Gaussian and count their opposite-sign
angular wedges. Formula (27) follows.

Since odd moments of \(H\) vanish,
\[
 \mathbb E\Phi(W)^2=\frac{1+u}{4},
 \qquad
 \mathbb E\Phi(W)^3=\frac{1+3u}{8}.
\]
Equation (26) now gives the exact identities
\[
 m_4=\frac{3}{2\sqrt\pi}(1+u),
 \qquad
 m_5=\frac{5}{4\sqrt\pi}(1+3u).
 \tag{28}
\]
Substitution of \(m_4\) in (22) proves
the equality in (24).

*Proof of strict inequality for all k.*
The elementary Taylor lower bound
\(\arcsin t\ge t+t^3/6\) on \([0,1)\),
together with the classical rational
upper bound \(\pi<22/7\), gives
\[
 u>\frac{35}{162}.
 \tag{29}
\]
Set \(u_0=35/162\) and \(p_0=22/7\).
The following three **exact rational
inequalities** are immediate after
clearing positive denominators:
\[
 \begin{array}{ll}
 3(1+u_0)^2-4
       =3817/8748>0,&\qquad (29{\rm a})\\
 15(1+3u_0)^2-4p_0^2
       =58853/47628>0,&\qquad (29{\rm b})\\
 441(1+10u_0+5u_0^2)^2-512p_0^2
       =83693801929/3749847696>0.&\qquad (29{\rm c})
 \end{array}
\]
The first and (28) imply
\(m_4^2/3>1/\pi\), settling \(k=4\).

The second inequality implies
\(m_5^2>5\pi/12\). By coupling the
same initial iid normals, \(m_k\ge m_5\)
for all \(k\ge5\). For \(k=5,6\),
\[
 \frac{m_k^2}{k-1}>
  \frac{5\pi}{12(k-1)}
 \ge\frac{\pi}{2k}
 \ge\frac{k}{2\pi}\sin^2\frac{\pi}{k},
\]
where the middle inequality holds at
\(k=5,6\) and the last follows from
\(\sin x\le x\).

For \(k\ge7\), use (26) with \(k=7\)
and the vanishing of odd moments of \(H\):
\[
 m_7=\frac{21}{32\sqrt\pi}
       \left(1+10u+5v\right),
 \qquad v:=\mathbb E H^4\ge(\mathbb E H^2)^2=u^2.
\]
By (29 c) and (29),
\[
 m_7^2\ge
 \frac{441}{1024\pi}(1+10u+5u^2)^2
     >\frac\pi2.
\]
For every \(k\ge7\), monotonicity
\(m_k\ge m_7\) therefore gives
\[
 \frac{m_k^2}{k-1}
    >\frac{\pi}{2(k-1)}
    >\frac{\pi}{2k}
    \ge\frac{k}{2\pi}\sin^2\frac{\pi}{k}.
\]
This proves (23) without numerical
approximations. \(\square\)

*Proof of the logarithmic ratio.* Let
\(M_k=\max_{i\le k}Z_i\). For \(t>0\),
elementary integration by parts gives
\[
 \frac{t}{t^2+1}\varphi(t)
 \le1-\Phi(t)\le\frac{\varphi(t)}t.
 \tag{30}
\]
For fixed \(0<\eta<1\), set
\(t_\pm=(1\pm\eta)\sqrt{2\log k}\).
The lower-tail estimate in (30) gives
\(k(1-\Phi(t_-))\to\infty\), so
\(\mathbb P(M_k<t_-)\to0\).
The upper-tail estimate gives
\(k(1-\Phi(t_+))\to0\).
The negative part of \(M_k\) has expectation
at most \(2^{-(k-1)}/\sqrt{2\pi}\):
on \(\{M_k<0\}\), bound \(-M_k\)
by \(-Z_1\), and use independence
of the remaining \(k-1\) signs.
Thus
\[
 \mathbb EM_k\ge
       t_-\mathbb P(M_k\ge t_-)-o(1).
\]
For the upper bound,
\[
 \mathbb EM_k
 \le t_++\mathbb E(M_k-t_+)_+
 \le t_++k\int_{t_+}^\infty(1-\Phi(s))\,ds
 \le t_++\frac{k\varphi(t_+)}{t_+^2}.
\]
The final error tends to zero.
Letting \(\eta\downarrow0\) shows
\[
                   m_k\sim\sqrt{2\log k}.
\]
Finally,
\(\sin(\pi/k)\sim\pi/k\), so (22)
has order \(2\log k/k\), whereas
the equal-mass fan optimum has order
\(\pi/(2k)\). Their ratio is
\((4/\pi)\log k(1+o(1))\), as claimed.
\(\square\)

**Scope.** This is a lower construction for the
fully unconstrained fixed-mass partition problem,
not a proof that regular simplex cells globally
optimize it. It rigorously shows that the
planar fan value fails as an all-dimensions
mass-constrained inequality, already for \(k=4\).


## 11. Exact threshold for the tetrahedron to defeat every four-sector fan

The strict comparison in Theorem 13 occurs even without fixing
all four sector masses equal. A tetrahedral partition of
\(\mathbb R^3\) has four cells of mass \(1/4\), so it is
admissible whenever the prescribed **minimum** cell mass
is at most \(1/4\).

Let \(u=(2/\pi)\arcsin(1/3)\) as in (27) and put
\[
 \Delta_{\rm tet}=\frac34(1+u)^2-1.
 \tag{31}
\]

**Theorem 14 (sharp tetrahedron-versus-planar threshold).**
One has \(0<\Delta_{\rm tet}<1/8\), so
\[
 \boxed{\displaystyle
  \varepsilon_{\rm tet}
  =\frac\pi2-3\arcsin(\Delta_{\rm tet}^{1/3})
       \ \in(0,\pi/2).}
 \tag{32}
\]
For every \(0\le\varepsilon\le\pi/2\),
compare the fixed, equal-mass tetrahedral Gaussian
partition with the optimum over **all four-sector
planar Gaussian fans** whose every sector has mass
at least \(\varepsilon/(2\pi)\). Then:

- if \(\varepsilon<\varepsilon_{\rm tet}\),
  the planar fan optimum is **strictly greater**
  than the tetrahedral score;
- at \(\varepsilon=\varepsilon_{\rm tet}\),
  the two scores are equal;
- if \(\varepsilon>\varepsilon_{\rm tet}\),
  the tetrahedral score **strictly exceeds**
  the optimum over that entire planar fan class.

Exact rational interval evaluation additionally certifies
\[
              \frac\pi{50}
        <\varepsilon_{\rm tet}<\frac\pi{40}.
 \tag{33}
\]
Thus a minimum Gaussian mass just above
\(\varepsilon_{\rm tet}/(2\pi)\), which lies
between \(1/100\) and \(1/80\), already forces
a strict three-dimensional advantage for this
explicit tetrahedral competitor.

*Proof.* The rational lower bound \(u>35/162>1/5\)
from (29) gives
\[
 \Delta_{\rm tet}>
  \frac34(1+1/5)^2-1=\frac2{25}>0.
\]
For an elementary upper bound, the function
\(t\mapsto(1-t^2)^{-1/2}\) is convex on \([0,1/3]\).
Its trapezoidal upper bound gives
\[
 \arcsin(1/3)=\int_0^{1/3}\frac{dt}{\sqrt{1-t^2}}
 \le\frac16\left(1+\frac3{\sqrt8}\right)
 =\frac16+\frac1{4\sqrt2}<\frac{11}{32},
\]
since \(24/17<\sqrt2\).
Together with the classical lower bound \(\pi>25/8\),
this yields
\[
 u=\frac2\pi\arcsin(1/3)<\frac{11}{50}.
\]
Therefore
\[
 \Delta_{\rm tet}<
  \frac34(1+11/50)^2-1
  =\frac{1163}{10000}<\frac18.
\]
Since \(\arcsin\) is increasing on \([0,1]\),
\(0<\Delta_{\rm tet}<1/8\) implies
\(0<\arcsin(\Delta_{\rm tet}^{1/3})<\pi/6\),
establishing (32).

By Theorem 7, the planar four-sector optimum is
\[
 M_4(\varepsilon)
 =\frac{1+\sin^3((\pi/2-\varepsilon)/3)}{\pi}.
\]
By (24), the fixed tetrahedral score is
\[
 T_4=\frac{1+\Delta_{\rm tet}}{\pi}.
\]
The function
\(\sin^3((\pi/2-\varepsilon)/3)\)
is strictly decreasing in
\(\varepsilon\in[0,\pi/2]\), from \(1/8\)
to \(0\). Hence it crosses
\(\Delta_{\rm tet}\) exactly once, at
\(\varepsilon=\varepsilon_{\rm tet}\)
as given in (32), and the three strict/tie
cases follow.

For (33), using the exact rational
interval algorithm of check_exact.py,
one independently verifies
\[
 2V_3(4,\pi/50)
      >3(1+u)^2,\qquad
 2V_3(4,\pi/40)
      <3(1+u)^2.
\]
These are precisely the comparisons of
\(M_4(\pi/50),M_4(\pi/40)\)
with \(T_4\) after multiplication by \(4\pi\).
Both strict signs are independently
replayed in the companion checker.
Monotonicity then yields (33).
\(\square\)

**Corollary 15 (nontrivial interior dimension jump).**
For every \(k\ge4\), there exists
\(\varepsilon_0(k)<2\pi/k\) such that a
regular simplex Gaussian partition
of \(\mathbb R^{k-1}\) strictly outperforms
all \(k\)-sector planar Gaussian fans
at every common mass floor
\(\varepsilon\in(\varepsilon_0(k),2\pi/k]\).

*Proof.* The simplex partition has cell
masses exactly \(1/k\), and is feasible
throughout the given floor interval.
At the endpoint \(\varepsilon=2\pi/k\),
Theorem 13 gives a strict score gap.
The right side of the exact formula
in Theorem 2 is continuous in
\(\varepsilon\). The strict inequality
persists on a nontrivial interval
immediately below the endpoint.
\(\square\)


## 12. Consequences for positive-correlation Gaussian noise stability

The strict high-dimensional gap also persists for the
**full nonlinear Gaussian noise-stability functional**
at an explicitly quantified positive correlation.

Let \(G,G'\in\mathbb R^n\) be standard Gaussians
with \(\operatorname{Cov}(G,G')=\rho I_n\),
where \(0<\rho<1\).
For a measurable Gaussian partition
\(\mathcal A=(A_1,\dots,A_k)\), write
\[
 N_\rho(\mathcal A)
  =\sum_{i=1}^k
     \mathbb P\{G\in A_i,\ G'\in A_i\}.
 \tag{34}
\]
Let \(\mathcal S_k\) be the regular simplex partition
from Theorem 13. Let \(\mathcal Q_k\) be the
equiangular \(k\)-fan (with orthogonal extension
to \(\mathbb R^{k-1}\)), so all their cell masses
are \(1/k\).

**Theorem 16 (explicit small-noise stability
dimension jump).**
Put
\[
 D_k=\frac{m_k^2}{k-1}
          -\frac{k}{2\pi}\sin^2\frac\pi k>0.
 \tag{35}
\]
For every \(k\ge4\) and
\(0<\rho\le \min\{D_k,1/2\}\),
\[
 \boxed{\quad
       N_\rho(\mathcal S_k)>
       N_\rho(\mathcal Q_k).
       \quad}
 \tag{36}
\]
In particular, for **four equal-mass cells**
in dimension three, the fully explicit,
dimensionless correlation interval
\[
 \boxed{\displaystyle
 0<\rho\le \frac1{30}}
 \tag{37}
\]
already guarantees that the tetrahedral
Gaussian partition has strictly greater
noise stability than every four-equal-angle
planar sector partition.

*Proof.* Normalize the multivariate Hermite
polynomials \(H_\alpha\) to form an orthonormal
basis of \(L^2(\gamma_n)\).
The Gaussian generating function
\[
 \mathbb E
 e^{\langle s,G\rangle-\|s\|^2/2}
 e^{\langle t,G'\rangle-\|t\|^2/2}
          =e^{\rho\langle s,t\rangle}
\]
shows by coefficient comparison that
\(\mathbb E H_\alpha(G)H_\beta(G')
 =\delta_{\alpha\beta}\rho^{|\alpha|}\).
For cell indicators \(h_i=\mathbf1_{A_i}\),
set
\[
 W_j(\mathcal A)
 =\sum_{i=1}^k\sum_{|\alpha|=j}
       |\langle h_i,H_\alpha\rangle_{L^2(\gamma)}|^2
       \ge0.
\]
Parseval and monotone convergence yield
\[
 N_\rho(\mathcal A)
       =\sum_{j=0}^\infty\rho^j W_j(\mathcal A),
 \qquad
 \sum_{j=0}^\infty W_j(\mathcal A)=
       \sum_i\gamma_n(A_i)=1.
 \tag{38}
\]
If all cells have measure \(1/k\), then
\[
 W_0=\sum_i(1/k)^2=1/k,
 \qquad
 W_1=\sum_i
       \left\|\int_{A_i}x\,d\gamma_n(x)\right\|^2.
\]
For every such partition and \(0<\rho<1\),
the nonnegative remainder satisfies
\[
 0\le N_\rho(\mathcal A)
       -\frac1k-\rho W_1(\mathcal A)
       \le\rho^2\sum_{j\ge2}W_j(\mathcal A)
       \le\rho^2.
 \tag{39}
\]
Thus Theorem 13 and (39) imply
\[
 N_\rho(\mathcal S_k)-N_\rho(\mathcal Q_k)
 \ge\rho D_k-\rho^2.
 \tag{40}
\]
This lower bound is strictly positive for
\(0<\rho<D_k\).
At the endpoint \(\rho=D_k<1\),
the last inequality in (39) is strict
for \(\mathcal Q_k\), because
\(W_0(\mathcal Q_k)=1/k>0\).
Therefore the difference is strictly
positive also for \(0<\rho\le D_k\),
in particular on the range in (36).

In the four-cell case, the exact gap is
\[
 D_4=
 \frac{3(1+u)^2-4}{4\pi},\qquad
 u=\frac2\pi\arcsin\frac13.
\]
Using the certified rational bounds
\(u>35/162\) and \(\pi<22/7\)
from Theorem 13,
\[
 D_4>
 \frac{3817}{8748}\cdot\frac7{88}
 =\frac{26719}{769824}
 >\frac1{30}.
 \tag{41}
\]
The last strict inequality reduces
to the integer statement
\(30\cdot26719>769824\).
Hence (40) is positive for every
\(0<\rho\le1/30\), giving (37).
\(\square\)

**Remark (not a solution to Standard Simplex).**
The strict comparison in (36) is between
two **explicit equal-mass partitions**, not
against all possible Gaussian partitions.
The full fixed-mass Gaussian noise stability
optimization is a distinct problem. In the
four-cell case the planar competitor
\(\mathcal Q_4\) is the quadrant partition,
and its full noise stability has the
elementary exact value
\[
 N_\rho(\mathcal Q_4)
 =\left(\frac12+\frac{\arcsin\rho}{\pi}\right)^2
 \quad(0\le\rho<1),
\]
since the two coordinate-sign agreement
events are independent and each has
probability \(1/2+\arcsin\rho/\pi\).
This provides a separate expression against
which the small-noise theorem can be tested.


## 13. Exact analytic threshold beyond the first-Hermite comparison

The general remainder estimate in Theorem 16
is intentionally crude. For the four-quadrant planar
partition, one can use its **exact** noise stability
to obtain a much longer certified interval of
tetrahedral superiority.

Recall
\[
 T_4=\frac3{4\pi}(1+u)^2,\qquad
 u=\frac2\pi\arcsin\frac13,\qquad
 a(\rho)=\frac{\arcsin\rho}{\pi}.
\]
For \(0<\rho\le1\), set
\[
 F(\rho)=\frac{a(\rho)+a(\rho)^2}{\rho}.
 \tag{42}
\]

**Theorem 17 (sharp threshold for the first-Hermite
witness).**
There is a **unique** \(\rho_*\in(0,1)\)
such that
\[
 \boxed{\displaystyle
  a(\rho_*)+a(\rho_*)^2=\rho_* T_4 .}
 \tag{43}
\]
Its location is rigorously enclosed by
\[
 \boxed{\frac{29}{100}<\rho_*<\frac3{10}}.
 \tag{44}
\]
For every \(0<\rho\le\rho_*\), the
three-dimensional tetrahedral Gaussian
partition has strictly greater *full*
noise stability than the four-quadrant
Gaussian partition:
\[
 \boxed{N_\rho(\mathcal S_4)>
                  N_\rho(\mathcal Q_4).}
 \tag{45}
\]
The label "sharp" here refers exclusively to
the threshold at which the **first-Hermite
lower bound** ceases to imply (45);
we do not claim (45) fails for \(\rho>\rho_*\).

*Proof.* The Maclaurin expansion
\[
 \arcsin\rho=\sum_{j=0}^\infty
   \frac{\binom{2j}{j}}{4^j(2j+1)}
          \rho^{2j+1}
 \quad(0\le\rho<1)
\]
has strictly positive coefficients.
Consequently, \(F(\rho)\) is strictly
increasing on \((0,1)\), being a series
with positive coefficients for all
nonconstant nonnegative powers of \(\rho\).
It is continuous at the endpoints, with
\[
 F(0)=\frac1\pi<T_4,\qquad
 F(1)=\frac34>T_4.
\]
The first inequality is (24), and the second
follows e.g. from \(u<11/50,\ \pi>3\).
The intermediate value theorem and
strict monotonicity give the unique
positive root in (43).

As already derived in Theorem 16,
\[
 N_\rho(\mathcal Q_4)
       =\frac14+a(\rho)+a(\rho)^2
       =\frac14+\rho F(\rho).
\]
The tetrahedral Hermite expansion gives
\[
 N_\rho(\mathcal S_4)>
                \frac14+\rho T_4
           \qquad(\rho>0).
\]
Indeed its terms of Hermite degree at
least two are nonnegative and **not all
zero**: otherwise every cell indicator
would be Gaussian-a.e. affine, hence
constant because it is bounded,
contradicting its mass \(1/4\).
When \(0<\rho\le\rho_*\),
\(F(\rho)\le T_4\), proving (45),
including its endpoint strictly.

For (44), check_exact.py computes
outward rational intervals for both
\(\pi\) and \(\arcsin x\) at rational \(x\).
It verifies, using **exact integer
and rational arithmetic**,
\[
 \begin{split}
  F(29/100)&<T_4,\\
  F(3/10)&>T_4.
 \end{split}
\]
These strict comparisons certify
(44) by monotonicity. No approximate
quadrature or floating-point computation
enters the certificate. \(\square\)


## 14. Exact finite-dimensional dual for fixed-mass Gaussian partitions

The preceding results expose the main remaining problem:
what is the optimum over **all measurable Gaussian
partitions** with given positive cell masses?
There is an exact finite-dimensional variational
reduction, independent of any planar assumption.
Related power-diagram first-variation ideas appear
in the Gaussian partition literature, including
Khot--Naor and Heilman; the proof is included
for completeness, not claimed to be historically new.

Fix \(d\ge1,\ k\ge2\) and
\(p=(p_1,\dots,p_k)\) with
\(p_i>0,\ \sum_i p_i=1\).
Write
\[
 \mathcal M_d(p):=\sup_{\substack{
 (A_i)\ {\rm measurable\ partition\ of}\ \mathbb R^d\\
 \gamma_d(A_i)=p_i}}
 \sum_{i=1}^k
 \left\|\int_{A_i}x\,d\gamma_d(x)\right\|^2 .
 \tag{46}
\]
For a list \(v=(v_1,\dots,v_k)\) of vectors
in \(\mathbb R^d\), let
\[
 \Psi_v(\lambda):=
    \sum_{i=1}^k p_i\lambda_i+
   \mathbb E\max_{1\le i\le k}
     \left(\langle v_i,G\rangle-\lambda_i\right),
       \qquad \lambda\in\mathbb R^k.
 \tag{47}
\]

**Theorem 18 (exact Gaussian mass-constrained
dual reduction).** For every admissible
\((d,k,p)\),
\[
 \boxed{\displaystyle
 \sqrt{\mathcal M_d(p)}
 =\max_{\sum_i\|v_i\|^2=1}
      \ \min_{\lambda\in\mathbb R^k}
         \Psi_v(\lambda).}
 \tag{48}
\]
Both extrema on the right are attained.
The inner minimum can be normalized by
\(\min_i\lambda_i=0\); hence (48)
is an exact finite-dimensional optimization
over at most \(kd+k\) real parameters.

For pairwise **distinct** \(v_i\), an optimal
partition for the inner linear assignment
problem is precisely the Laguerre partition
\[
 A_i(v,\lambda)=\left\{x:
  \langle v_i,x\rangle-\lambda_i
     > \langle v_j,x\rangle-\lambda_j
      \text{ for every }j\ne i\right\},
 \tag{49}
\]
where \(\lambda\) minimizes (47).
The cells have exactly masses \(p_i\)
and their boundaries are contained in
affine hyperplanes.

Moreover, if \((A_i)\) **attains**
\(\mathcal M_d(p)\), all its Gaussian
first moments \(b_i=\int_{A_i}x\,d\gamma_d\)
are pairwise distinct. The partition is
then, up to Gaussian-null sets, a Laguerre
partition (49) with \(v_i=b_i\) for
some offsets \(\lambda_i\).

*Proof.* Begin with the **linear**
partition problem for fixed \(v\):
\[
 C_p(v):=\sup_{\gamma_d(A_i)=p_i}
          \sum_i\int_{A_i}\langle v_i,x\rangle\,
                     d\gamma_d(x).
\]
For arbitrary real \(\lambda_i\) and any
feasible partition, the pointwise maximum
inequality gives
\[
 \begin{aligned}
 \sum_i\int_{A_i}\langle v_i,x\rangle\,d\gamma
 &=\sum_i\int_{A_i}
           (\langle v_i,x\rangle-\lambda_i)\,d\gamma
           +\sum_i p_i\lambda_i\\
 &\le\mathbb E\max_i(\langle v_i,G\rangle-\lambda_i)
           +\sum_i p_i\lambda_i
  =\Psi_v(\lambda).
 \end{aligned}
\]
Thus \(C_p(v)\le\inf_\lambda\Psi_v(\lambda)\).

The dual function is continuous and invariant
under common shifts \(\lambda\mapsto\lambda+c(1,\dots,1)\).
Choose the representative with
\(\min_i\lambda_i=0\). Let \(i_0\) have
\(\lambda_{i_0}=0\). Then
\[
 \Psi_v(\lambda)
 \ge\sum_i p_i\lambda_i
       +\mathbb E\langle v_{i_0},G\rangle
 =\sum_i p_i\lambda_i
 \ge p_{\min}\max_i\lambda_i.
 \tag{50}
\]
Since \(p_{\min}>0\), this proves
coercivity on the closed gauge slice
\(\min\lambda=0\). Thus \(\Psi_v\)
has a minimizer \(\lambda^*\).

First suppose \(v_i\ne v_j\) whenever
\(i\ne j\). For every fixed \(\lambda\),
ties between any two affine scores
\(\langle v_i,G\rangle-\lambda_i\)
have Gaussian probability zero.
The pointwise maximum is Lipschitz
in \(\lambda\), so dominated convergence
gives
\[
 \frac{\partial\Psi_v}{\partial\lambda_i}
       =p_i-\gamma_d(A_i(v,\lambda)).
\]
At a global minimizer of this
translation-invariant differentiable
function all partial derivatives vanish.
Hence the Laguerre cells in (49)
have masses exactly \(p_i\).
They attain equality pointwise in the
weak-duality inequality, so
\[
 C_p(v)=\min_\lambda\Psi_v(\lambda).
 \tag{51}
\]

For arbitrary \(v\), approximate it
by vector lists \(v^{(m)}\) whose
entries are pairwise distinct.
The primal functional is Lipschitz:
\[
 |C_p(v)-C_p(w)|
 \le\mathbb E\|G\|
       \left(\sum_i\|v_i-w_i\|^2\right)^{1/2}.
\]
The same bound holds for
\(\big|\min_\lambda\Psi_v(\lambda)
     -\min_\lambda\Psi_w(\lambda)\big|\),
since the pointwise maxima differ by
at most \(\|G\|\max_i\|v_i-w_i\|\),
independently of \(\lambda\).
Taking limits extends (51) to
every \(v\), including duplicate
score vectors. This proves exact
linear duality without an unproved
tie-breaking assumption.

For a given partition, let
\(b_i=\int_{A_i}x\,d\gamma_d(x)\).
Euclidean norm duality yields
\[
 \left(\sum_i\|b_i\|^2\right)^{1/2}
 =\max_{\sum_i\|v_i\|^2=1}
          \sum_i\langle v_i,b_i\rangle.
\]
Taking suprema jointly over \(v\)
and the partitions, and then
applying (51), gives exactly (48).
The value \(C_p(v)\) is continuous
in \(v\), and the unit sphere in
\(\mathbb R^{kd}\) is compact, so
the outer maximum is attained.

It remains to justify the stated
structure for a partition that
attains \(\mathcal M_d(p)\).
Suppose two distinct cell indices
\(i,j\) have the same centroid
\(b_i=b_j=b\). Since both cells have
positive Gaussian measure and the
Gaussian law is nonatomic with
strictly positive density, choose
small disjoint balls around distinct
density points of these cells.
Within their intersections with
the cells, take subsets
\(E\subseteq A_i,F\subseteq A_j\)
of the same positive Gaussian mass.
The balls may be chosen so small
that \(\int_E x\,d\gamma\ne
      \int_F x\,d\gamma\).
Interchanging \(E\) and \(F\)
preserves every cell mass and replaces
\(b_i,b_j\) by \(b+\delta,b-\delta\)
for a nonzero vector \(\delta\).
Their squared-norm sum increases
strictly by \(2\|\delta\|^2\),
contradicting global maximality.
Thus the \(b_i\) are pairwise distinct.

Finally, take \(v_i=b_i\).
The optimal partition maximizes
the **linear** objective with these
weights. Indeed, if some other
feasible partition with moments
\(c_i\) had
\(\sum_i\langle b_i,c_i\rangle
  >\sum_i\|b_i\|^2\),
then
\[
 \sum_i\|c_i\|^2
 =2\sum_i\langle b_i,c_i\rangle
   -\sum_i\|b_i\|^2
   +\sum_i\|c_i-b_i\|^2
 >\sum_i\|b_i\|^2,
\]
a contradiction.
By (51), the linear objective has
a Laguerre maximizing partition
with offsets \(\lambda^*\).
For the distinct vectors \(b_i\),
its affine-score ties are
Gaussian-null. Equality in the
pointwise maximum inequality forces
the original partition to equal
that Laguerre partition almost
everywhere. \(\square\)

**Research boundary.** This exact duality
does *not* identify the maximizer in (48).
It rigorously reduces the remaining
unrestricted fixed-mass problem to
a finite-dimensional but generally
nonconvex variational optimization.
The special regular simplex supplies
an explicit feasible lower certificate;
a genuine solution of the corresponding
Standard Simplex question requires a
matching universal upper bound (or a
counterexample) for this dual objective.


## 15. Exact fixed-mass calibration cases

The dual reduction is consistent with two classical
extremal situations that can be evaluated exactly.
They delimit what is currently resolved in the
fully unrestricted partition problem.

**Corollary 19 (arbitrary two-cell masses;
equal three-cell masses).**
Let \(d\ge1\), \(0<p<1\), and
\(t_p=\Phi^{-1}(1-p)\). Then
\[
 \boxed{\displaystyle
 \mathcal M_d(p,1-p)
       =2\varphi(t_p)^2
       =\frac1\pi e^{-t_p^2}.}
 \tag{52}
\]
The maximizers are precisely, up to
Gaussian-null sets and Euclidean rotations,
a halfspace of Gaussian measure \(p\)
and its complement.

For \(d\ge2\), the uniform three-cell case
satisfies
\[
 \boxed{\displaystyle
 \mathcal M_d(1/3,1/3,1/3)
           =\frac9{8\pi}.}
 \tag{53}
\]
The upper bound in (53) is **inherited**
from the published OpenAI Gaussian propeller
theorem [OAI-096], whereas attainment follows
by the explicit 120-degree sector construction.

*Proof of (52).* Let \(A\subset\mathbb R^d\)
have mass \(p\) and \(b=\int_A x\,d\gamma_d\).
Since the entire Gaussian is centered,
the complement has first moment \(-b\);
the two-cell objective is \(2\|b\|^2\).
If \(b\ne0\), take \(u=b/\|b\|\) and
\(H=\{x:\langle u,x\rangle\ge t_p\}\),
which has measure \(p\). For every \(x\),
the factor \(\langle u,x\rangle-t_p\)
has the same sign as
\(\mathbf1_H(x)-\mathbf1_A(x)\)
whenever those indicators differ.
Therefore
\[
 \int(\langle u,x\rangle-t_p)
       (\mathbf1_H-\mathbf1_A)\,d\gamma_d\ge0.
\]
Because \(\gamma_d(H)=\gamma_d(A)=p\),
the threshold terms cancel, giving
\[
 \|b\|=\int_A\langle u,x\rangle\,d\gamma_d
 \le\int_H\langle u,x\rangle\,d\gamma_d
 =\int_{t_p}^\infty s\varphi(s)\,ds
 =\varphi(t_p).
\]
Equality requires \(A=H\) up to Gaussian
null sets, since the integrand is strictly
positive wherever the indicators differ
outside the null hyperplane. If \(b=0\),
the objective is zero, strictly below
the positive halfspace optimum.
Thus (52) and its equality classification
follow. The Gaussian propeller upper bound,
applied to three cells, and the explicit
equal 120-degree sectors prove (53).
\(\square\)

For \(k\ge4\) and positive fixed masses,
Theorem 18 supplies an exact dual framework
but **not** a solution of its nonconvex
outer optimization. For uniform masses
the regular simplex gives a rigorous
lower construction (Theorem 13); Theorem 13
alone does not identify the global maximum.


## 16. Provenance, audit and limitations

- **Comparator [OAI-096]:** OpenAI, *The Gaussian propeller bound
  in every dimension*, September 24, 2026; public source in the
  OpenAI Mathematics collection, result family 096.
  Its global theorem applies to all measurable Gaussian
  partitions and is stronger in that respect.
- **This note's additional statements:** constrained fan
  optimization for every number of sectors; complete
  high-mass equality classification; quantitative excess
  stability; four-sector cubic formula; sharp three-sector
  angular deficit; unequal floors; rotationally invariant
  radial laws; exact Gaussian simplex lower constructions
  disproving a naive all-dimensional extension of the
  planar constrained bounds; and a rigorously bracketed
  positive-correlation noise-stability comparison.
  All proofs are independent of upstream arguments.
- **Prior related work:** Steven Heilman, *Euclidean Partitions
  Optimizing Noise Stability*, arXiv:1211.7138, and
  *Stable Gaussian Minimal Bubbles*, arXiv:1901.03934,
  discuss the equal-measure Gaussian simplex problem and
  fixed-volume centroid objectives. The Gaussian
  multi-bubble *perimeter* theorem of Milman--Neeman is
  logically distinct from the first-moment problem.
- **Scope boundary:** our global **optimization** formulas
  concern conical planar fans. The general Gaussian
  partition results here are **lower-bound constructions
  only**, not global simplex optimality theorems.
  No claim of historical priority or novelty relative
  to full mathematical literature is made.
- **Verification:** The companion script check_exact.py
  checks nontrivial parameter examples by rational interval
  enclosures for \(\pi\) and cosine and scans discrete angle
  grids. The proofs do not rely on numerical verification.
