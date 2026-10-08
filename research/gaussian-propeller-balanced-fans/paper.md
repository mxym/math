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

## 9. Provenance, audit and limitations

- **Comparator [OAI-096]:** OpenAI, *The Gaussian propeller bound
  in every dimension*, September 24, 2026; public source in the
  OpenAI Mathematics collection, result family 096.
  Its global theorem applies to all measurable Gaussian
  partitions and is stronger in that respect.
- **This note's additional statements:** constrained fan
  optimization for every number of sectors; complete
  high-mass equality classification; quantitative excess
  stability; four-sector cubic formula; sharp three-sector
  angular deficit. The proofs here are independent of
  upstream arguments.
- **Scope boundary:** none of these results is asserted
  for arbitrary nonconical, nonfan cells under mass constraints.
  No claim of publication priority or novelty relative to
  the full mathematical literature is made at this stage.
- **Verification:** The companion script check_exact.py
  checks nontrivial parameter examples by rational interval
  enclosures for \(\pi\) and cosine and scans discrete angle
  grids. The proofs do not rely on numerical verification.
