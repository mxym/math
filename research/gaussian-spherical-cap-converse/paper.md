# A spherical-cap obstruction for Gaussian equal-mass centroid partitions

**Research manuscript · 7 October 2026 (PDT)**

This is a continuation of the mass-constrained Gaussian partition
programme and the previously released dimension-rate theorem.
All inequalities below concern **arbitrary measurable partitions**, not
only conical fans, power diagrams or the explicit cyclic constructions.

## Main results

Let \(\gamma_d\) denote the standard Gaussian law on \(\mathbb R^d\), and
\[
 F_d(k)=\sup_{\substack{(A_1,\ldots,A_k)\text{ partition}\\
                       \gamma_d(A_i)=1/k}}
 \sum_{i=1}^k \left\|\int_{A_i}x\,d\gamma_d(x)\right\|^2.
\]
Set \(L=\log k\), \(h_k=k\varphi(\Phi^{-1}(1-1/k))\),
\(U_k=h_k^2/k\), and \(F_\infty(k)=F_{k-1}(k)\).
Our prior exact all-mass theorem gives
\[
 0\le U_k-F_\infty(k)\le 2/k. \tag{1}
\]

**Theorem A (quantitative finite-dimensional spherical-cap converse).**
For \(k\ge2,d\ge3\), and any \(s\in(0,\sqrt d)\) satisfying
\[
 \mathcal B_{d,k}(s):=
 \frac{k}{s\sqrt{2\pi(1-1/d)}}
 \left(1-\frac{s^2}{d}\right)^{(d-1)/2}\le1,
 \tag{2}
\]
the global partition optimum satisfies the exact nonasymptotic bound
\[
 \boxed{\displaystyle
 kF_d(k)\le h_k\left(s+\frac{d}{(d-1)s}\right).}
 \tag{3}
\]
No orientation, regularity, symmetry, or assumed optimizer enters.

**Theorem B (explicit quadratic-logarithmic dimensional defect).**
For every integer \(k\) with \(L=\log k\ge100\), and every integer
\(d\ge L^2/\log L\),
\[
 \boxed{\displaystyle
 U_k-F_d(k)\ \ge\
      \frac1k\left(\frac{L^2}{d}-14\right).}
 \tag{4}
\]
The right side may be negative for large \(d\), in which case (4)
remains correct but is not informative.

**Theorem C (quadratic-logarithmic necessary dimension).**
Fix a finite constant \(C\ge0\).
If for all sufficiently large \(k\) there exists an exactly equal-mass
Gaussian \(k\)-partition in dimension \(d_k\) with
\[
 P(\mathcal A_k)\ge F_\infty(k)-C/k,
\]
then
\[
 \boxed{\displaystyle
 \liminf_{k\to\infty}\frac{d_k}{(\log k)^2}
                        \ge\frac1{C+16}.}
 \tag{5}
\]
Therefore **bounded additive \(O(1/k)\) error necessarily requires
dimension \(\Omega((\log k)^2)\)**.

The preceding cubic-logarithmic *sufficient* dimension bound,
\(d\le 8(\log k)^3+2\) for additive \(14/k\) error, is unchanged.
The remaining gap is now exactly between quadratic and cubic logarithms,
not between a quadratic-logarithmic / loglog lower and cubic-logarithmic
upper.

## 1. From any partition to a Gaussian spherical code

**Lemma 1 (centroid directions turn partitions into maxima).**
For any \(k\)-partition of exactly equal Gaussian masses, let
\(b_i=\int_{A_i}x\,d\gamma_d(x)\) and
\(u_i\in S^{d-1}\) be any unit direction along \(b_i\)
(arbitrary when \(b_i=0\)). Then
\[
 \boxed{\displaystyle
 \frac{k}{h_k}\sum_i\|b_i\|^2
       \le \mathbb E\max_i\langle u_i,G\rangle,
       \qquad G\sim N(0,I_d).}
 \tag{6}
\]

*Proof.* For every measurable \(A\) of Gaussian mass \(1/k\),
the sharp one-cell halfspace rearrangement gives
\[
 \left\|\int_A x\,d\gamma_d(x)\right\|
             \le\varphi(\Phi^{-1}(1-1/k))=h_k/k.
\]
Indeed the pointwise comparison of the set with the Gaussian
upper halfspace having the same mass and normal direction as its
moment has a nonnegative signed threshold integral.
Consequently, \(\sum_i\|b_i\|^2\le(h_k/k)\sum_i\|b_i\|\).
For each \(x\), \(\max_i\langle u_i,x\rangle
\ge\sum_i\mathbf1_{A_i}(x)\langle u_i,x\rangle\).
Integrating gives
\[
 \mathbb E\max_i\langle u_i,G\rangle
       \ge\sum_i\langle u_i,b_i\rangle=\sum_i\|b_i\|.
\]
Combine the two inequalities. \(\square\)

This is the central structural bridge: it is valid even for extremely
irregular partitions and converts their first-moment score into
a maximum of only \(k\) Gaussian linear forms.

## 2. A uniform spherical-cap tail

Let \(V\) be uniform on \(S^{d-1}\) for \(d\ge3\), and \(R=\|G\|\).
The standard Gaussian polar decomposition \(G=RV\) makes
\(R,V\) independent with \(\mathbb ER\le\sqrt d\).

**Lemma 2 (a cap estimate with its polynomial prefactor).**
For \(d\ge3\) and every \(0<a<1\),
\[
 \boxed{\displaystyle
 \Pr(V_1\ge a)\le
 \frac1{a\sqrt{2\pi(d-1)}}
            (1-a^2)^{(d-1)/2}.}             \tag{7}
\]

*Proof.* The first spherical coordinate has density
\[
 c_d(1-u^2)^{(d-3)/2}\mathbf1_{\{|u|<1\}},\quad
 c_d=\frac{\Gamma(d/2)}
              {\sqrt\pi\,\Gamma((d-1)/2)}.
\]
Log-convexity of the Gamma integral (by Hölder's inequality)
gives \(\Gamma(z+1/2)^2\le\Gamma(z)\Gamma(z+1)=
z\Gamma(z)^2\) for \(z>0\). Hence
\(c_d\le\sqrt{(d-1)/(2\pi)}\).
Since \(u\ge a\),
\[
 \begin{aligned}
 \int_a^1(1-u^2)^{(d-3)/2}du
 &\le\frac1a\int_a^1 u(1-u^2)^{(d-3)/2}du\\
 &=\frac{(1-a^2)^{(d-1)/2}}{(d-1)a}.
 \end{aligned}
\]
Multiplying the estimates proves (7). \(\square\)

**Lemma 3 (integrating a spherical cap union).**
For any \(k\) unit directions in \(\mathbb R^d\), define
\[
 B_{d,k}(a)=\frac{k}{a\sqrt{2\pi(d-1)}}
       (1-a^2)^{(d-1)/2}.
\]
If \(B_{d,k}(a)\le1\), then
\[
 \boxed{\displaystyle
 \mathbb E\max_{1\le i\le k}\langle u_i,G\rangle
 \le \sqrt d\,\left(a+\frac1{(d-1)a}\right).} \tag{8}
\]

*Proof.* Put \(T=\max_i\langle u_i,V\rangle\).
The union bound and Lemma 2 give
\(\Pr(T\ge u)\le B_{d,k}(u)\) for \(a\le u<1\).
Direct differentiation shows
\[
 \frac d{du}\log B_{d,k}(u)
   =-\frac1u-\frac{(d-1)u}{1-u^2}\le-(d-1)a
    \quad(u\ge a).
\]
Therefore \(B_{d,k}(u)\le
 B_{d,k}(a)\exp[-(d-1)a(u-a)]\), and hence
\[
 \mathbb ET\le a+\mathbb E(T-a)_+
 \le a+\int_a^1 B_{d,k}(u)\,du
 \le a+\frac{B_{d,k}(a)}{(d-1)a}
 \le a+\frac1{(d-1)a}.
\]
Independence and \(\mathbb ER\le\sqrt d\) prove (8).
There is no implicit assumption that the maximum is positive:
the first inequality \(T\le a+(T-a)_+\) holds pointwise. \(\square\)

*Proof of Theorem A.* Choose \(a=s/\sqrt d\) in Lemma 3.
Then \(B_{d,k}(a)=\mathcal B_{d,k}(s)\), and (8) becomes
\[
 \mathbb E\max_i\langle u_i,G\rangle
 \le s+\frac{d}{(d-1)s}.
\]
Insert this into Lemma 1 and take the supremum over partitions.
\(\square\)

## 3. A two-log-scale cap threshold

**Lemma 4 (universal explicit threshold).**
Suppose \(L=\log k\ge100\), \(d\ge L^2/\log L\),
and set
\[
 S=2L-\log L-\frac{2L^2}{d}+16,\qquad s=\sqrt S.
 \tag{9}
\]
Then \(0<S<d\), \(\mathcal B_{d,k}(s)<1\), and
\[
 \boxed{\displaystyle
 \left(s+\frac{d}{(d-1)s}\right)^2
 \le 2L-\log L-\frac{2L^2}{d}+24.}           \tag{10}
\]

*Proof.* The elementary inequality \(\log L\le\sqrt L\)
holds for \(L\ge1\). In particular, for \(L\ge100\),
\[
 d\ge L^2/\log L\ge L^{3/2}\ge10L.
\]
Also \(L^2/d\le\log L\), so
\[
 S\ge2L-3\log L+16\ge L,\qquad
 S\le2L+16\le3L<d.
\]
The logarithm of (2), using
\(\log(1-x)\le-x-x^2/2\) on \(0<x<1\), satisfies
\[
 \begin{aligned}
 \log\mathcal B_{d,k}(s)
 &\le L-\frac12\log S
       -\frac12\log(2\pi(1-1/d))\\
 &\quad-\frac S2-\frac{S^2}{4d}
          +\frac{S}{2d}+\frac{S^2}{4d^2}.
 \end{aligned}                               \tag{11}
\]
Write \(\Delta=2L-S=\log L+2L^2/d-16\).
A direct expansion gives
\[
 L-\frac S2-\frac{S^2}{4d}
   =\frac12\log L-8+\frac{L\Delta}{d}
                -\frac{\Delta^2}{4d}.
\]
Here \(\Delta\le3\log L\), and hence
\(L\Delta/d\le3(\log L)^2/L\le3\).
Moreover \(S\ge L\),
\(S/(2d)\le3/20\),
\(S^2/(4d^2)\le9/400\), and
\(2\pi(1-1/d)>1\).
Inserting these inequalities into (11) yields
\[
 \log\mathcal B_{d,k}(s)
          \le-8+3+\frac3{20}+\frac9{400}<0.
\]
Thus the cap union is strictly below one.

Since \(d\ge3\), \(d/(d-1)\le2\), and \(S\ge1\),
\[
 \left(s+\frac{d}{(d-1)s}\right)^2
 \le(s+2/s)^2=S+4+4/S\le S+8.
\]
Substitution of \(S\) proves (10). \(\square\)

**Lemma 5 (lower normal-tail centroid quantile).**
For \(k\ge e^{100}\) with \(L=\log k\),
\[
 \boxed{h_k^2\ge2L-\log L-4.}                \tag{12}
\]

*Proof.* Put \(t=\Phi^{-1}(1-1/k)>1\). The elementary Mills
bounds \(t\le h_k\le t+1/t\) and the lower Mills bound
\(\overline\Phi(t)\ge t\varphi(t)/(1+t^2)\) yield
\[
 L\le\frac{t^2}2+\log(t+1/t)
                  +\frac12\log(2\pi).
\]
The upper Mills bound gives \(t^2\le2L\).
For \(t\ge1\), \(t+1/t\le2t\le2\sqrt{2L}\),
and therefore
\[
 t^2\ge2L-\log L-\log(16\pi)>2L-\log L-4.
\]
The final elementary strict inequality follows, for instance,
from \(\pi<22/7\) and \(e>8/3\):
\(16\pi<352/7<4096/81<(e)^4\).
Since \(h_k\ge t\), (12) follows. \(\square\)

*Proof of Theorem B.* Combine Lemmas 1, 4 and Theorem A to obtain
\[
 kF_d(k)\le h_k H,\qquad
 H^2\le2L-\log L-\frac{2L^2}{d}+24.
\]
By Lemma 5,
\(h_k^2-H^2\ge 2L^2/d-28\).
The elementary identity
\[
 h_k(h_k-H)-\frac{h_k^2-H^2}{2}
                =\frac{(h_k-H)^2}{2}\ge0
\]
holds for all \(h_k,H\ge0\). Thus
\[
 h_k^2-kF_d(k)\ge h_k^2-h_kH
                \ge\frac{h_k^2-H^2}{2}
                \ge\frac{L^2}{d}-14.
\]
Divide by \(k\), proving (4). \(\square\)

## 4. Consequences for the exact dimension problem

*Proof of Theorem C.* Write \(L=\log k\) and fix \(C<\infty\).
The inherited universal equal-mass construction (1) implies
\[
 kF_\infty(k)\ge h_k^2-2.
\]
Therefore the assumed partition obeys
\(kF_{d_k}(k)\ge h_k^2-C-2\).

Set \(D_0=\lceil L^2/\log L\rceil\).
If \(d_k<D_0\), lift its partition cylindrically to
dimension \(D_0\), without changing the objective.
Theorem B applied in dimension \(D_0\) then implies
\[
 \frac{L^2}{D_0}\le C+16.
\]
But \(L^2/D_0\sim\log L\to\infty\), a contradiction
for all sufficiently large \(k\). Hence \(d_k\ge D_0\).
Applying Theorem B at the actual dimension \(d_k\) gives
\[
 h_k^2-C-2\le kF_{d_k}(k)
                 \le h_k^2-\frac{L^2}{d_k}+14,
\]
and therefore
\[
                   d_k\ge\frac{L^2}{C+16}.
\]
This holds for all sufficiently large \(k\), proving (5).
\(\square\)

**Comparison with the prior result.**
The earlier entropy / Gaussian rate–distortion converse established
only \(d\ge(2-o(1))L^2/\log L\) for additive \(O(1/k)\)
accuracy. Our sphere-union argument retains the
\(-\log L\) correction to the normal extreme tail **and**
the finite-dimensional \(L^2/d\) deficit simultaneously.
That yields the stronger order \(L^2\), not just a
constant improvement to the earlier argument.

The upper construction \(d\le8L^3+2\) is inherited
from the cyclic-orbit Gaussian partition theorem.
No \(O(L^2)\) construction is established here,
so a remaining logarithmic-factor gap persists.
This note does not claim to settle the full exact
dimension-rate function or the fixed-\(k\)
Standard Simplex optimality question.

## 5. Sources, novelty and verification contract

Mathematical inputs cited (and, where used critically, reproved):
the one-cell Gaussian rearrangement, Mills inequalities,
Gaussian polar independence, gamma log-convexity,
and exact mass-envelope \(U_k-F_\infty(k)\le2/k\).
The first four are classical; the last is proved in
the companion research note.

The classical spherical-cap union bound and its connection
to Gaussian process maxima have broad antecedents in
spherical code and high-dimensional geometry literature.
We do not claim that this exact form is historically new
without a wider specialist survey.

The checker supplies rational interval evidence of the
threshold algebra for several integer \(k,d\) pairs
without using floating-point certification. In particular
the universal lemma is established analytically, not by
numerical enumeration. All proof dependencies and scope
restrictions are disclosed in AUDIT.md.
