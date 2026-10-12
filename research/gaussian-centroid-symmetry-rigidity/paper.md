# Gaussian centroid symmetry-rigidity at quadratic-logarithmic dimension

Research note, 7 October 2026 (PDT). Analytic theorems and exact algebraic
Lean 4 formalization. No historical world-first claim.

## 1. Setup and main results

Let A=(A_1,...,A_k) be an arbitrary measurable equal-Gaussian-mass
partition in R^d, with gamma_d(A_i)=1/k. Define

\[
 b_i=\int_{A_i}x\,d\gamma_d(x),\qquad
 P(A)=\sum_i\|b_i\|^2,\qquad
 a_i=k\|b_i\|,\qquad
 \bar a=\frac1k\sum_i a_i,\qquad
 V(A)=\frac1k\sum_i(a_i-\bar a)^2.
\]
Let L=log k, t_k=Phi^{-1}(1-1/k), h_k=k phi(t_k), and
U_k=h_k^2/k. Let F_infty(k) be the global dimension-saturated
equal-mass squared-Gaussian-centroid optimum.

**Theorem A (universal variance-corrected finite-dimensional cap
bound).** For every equal-mass measurable partition A, all k with
L>=100, and all integers d>=L^2/log L,
\[
 \boxed{k(U_k-P(A))+V(A)\ge 2L^2/d-28.}\tag{1}
\]
In particular, if all conditional centroid lengths a_i are equal,
then V=0 and
\[
 \boxed{k(U_k-P(A))\ge 2L^2/d-28.}\tag{2}
\]
This doubles the  L^2/d coefficient available without a
centroid-length homogeneity assumption.

**Theorem B (asymptotically constant-sharp rigidity).**
Fix 0<c<infinity and any sequence d_k/L^2 -> c. For every
sequence of equal-mass partitions A_k,
\[
 \boxed{\liminf_{k\to\infty}
       \{k[U_k-P(A_k)]+V(A_k)\}\ge 2/c.}\tag{3}
\]
Thus a sequence of equal-centroid-length partitions at
d_k~c(log k)^2 necessarily loses at least (2/c+o(1))/k
relative to the independent one-cell halfspace envelope.
The analogous published general-partition obstruction was 1/c.

**Theorem C (quantitative symmetry breaking).**
Let gamma be Euler's constant, fix C>=0, and suppose
d_k/L^2->c>0 and
P(A_k)>=F_infty(k)-C/k. Then
\[
 \boxed{\liminf_{k\to\infty}V(A_k)\ge
        \max\{0,2/c-C-2(1-\gamma)\}.}\tag{4}
\]
If v_*=2/c-C-2(1-gamma)>0, every fixed 0<v_0<v_*
forces, for sufficiently large k, at least
\[
 \boxed{\frac{v_0}{2h_k^2}k
       =\left(\frac{v_0}{4}+o(1)\right)\frac{k}{\log k}}
                                                         \tag{5}
\]
cell centroids to differ in length from the average by
at least sqrt(v_0/2). Therefore sufficiently accurate
partitions below the symmetry threshold cannot conceal
all irregularity in o(k/log k) exceptional cells.

Theorem C does not assert that all optimizers have equal-norm
centroids. Its message is the opposite: if a partition
outperforms the symmetric dimensional obstruction, the
failure of that symmetry must be measurable and quantitative.

## 2. Exact variance identity and Gaussian support function

**Lemma 1 (centroid variance identity).** Every equal-mass
partition satisfies the following *exact* identities:
\[
 kP(A)=\frac1k\sum_i a_i^2=\bar a^2+V(A),\qquad
 k[U_k-P(A)]+V(A)=h_k^2-\bar a^2.             \tag{6}
\]
*Proof.* Since a_i=k||b_i||, we have kP=(1/k)sum a_i^2.
Expanding the definition of variance gives
V=(1/k)sum a_i^2-(bar a)^2. Since kU_k=h_k^2,
the second identity follows. QED.

**Lemma 2 (support-function bridge).** For each nonzero b_i put
u_i=b_i/||b_i||; choose any unit u_i for zero b_i.
For a standard Gaussian G in R^d,
\[
   0\le\bar a\le \mathbb E\max_i\langle u_i,G\rangle. \tag{7}
\]
*Proof.* Pointwise, max_i <u_i,x> is at least
sum_i 1_{A_i}(x)<u_i,x>. Integrating yields
E max_i<u_i,G> >=sum_i<u_i,b_i>=sum_i||b_i||=bar a.
QED.

For d>=3 and s in (0,sqrt d), set
\[
 B_{d,k}(s)=
  \frac{k}{s\sqrt{2\pi(1-1/d)}}
    \left(1-\frac{s^2}{d}\right)^{(d-1)/2},\qquad
 H_{d,k}(s)=s+\frac{d}{(d-1)s}.              \tag{8}
\]

**Lemma 3 (integrated spherical-cap maximum).**
If B_{d,k}(s)<=1, then E max_i <u_i,G><=H_{d,k}(s)
for arbitrary unit directions u_i.

*Proof.* Let V be uniform on S^{d-1}. Gamma log-convexity bounds the
normalizing constant in the density of V_1 by sqrt((d-1)/(2pi)).
Integration by parts of the density
c_d(1-t^2)^((d-3)/2) yields
\[
 \Pr(V_1\ge a)\le\frac{(1-a^2)^{(d-1)/2}}
                         {a\sqrt{2\pi(d-1)}}.
\]
The logarithmic derivative of this cap envelope on [a,1)
is at most -(d-1)a. A union bound and tail integration
therefore give E max_i<u_i,V> <= a+1/((d-1)a)
if the union envelope at a is <=1.
This spherical expected maximum is nonnegative because
it is at least E<u_1,V>=0.
The Gaussian polar decomposition G=RV has independent
R and V and E R <=sqrt d. Substitute a=s/sqrt d. QED.

**Proposition 4 (exact nonasymptotic cap–variance inequality).**
Whenever B_{d,k}(s)<=1,
\[
 \boxed{k[U_k-P(A)]+V(A)\ge h_k^2-H_{d,k}(s)^2.}\tag{9}
\]
*Proof.* Lemmas 1--3 give 0<=bar a<=H_{d,k}(s)
and k(U-P)+V=h_k^2-bar a^2. QED.

The proof uses neither an optimality condition nor any regularity,
conical geometry, stationary Voronoi property or assumption
that an optimizing partition exists.

## 3. Finite and asymptotic dimension applications

For L>=100 and d>=L^2/log L, the previously certified
spherical-cap threshold
\[
 s^2=2L-\log L-2L^2/d+16
\]
lies strictly between 0 and d and satisfies
\[
 B_{d,k}(s)<1,\qquad
 H_{d,k}(s)^2\le2L-\log L-2L^2/d+24.         \tag{10}
\]
These inequalities were proved analytically, with a pure-rational
threshold checker, in the prior spherical-cap note.
The classical Gaussian Mills bound gives
\[
                   h_k^2\ge2L-\log L-4.     \tag{11}
\]
Subtract (10) from (11), then apply Proposition 4:
\[
 k(U_k-P(A))+V(A)\ge2L^2/d-28.
\]
This proves Theorem A.

For the asymptotic result, fix eta>0 and d/L^2->c>0.
Choose instead
\[
 s^2=2L-\log L-\log(4\pi)-2L^2/d+\eta.
\]
The exact cap asymptotic, proved in the sharp
dimension-rate companion using
log(1-x)=-x-x^2/2+O(x^3/(1-x)), yields
\[
 \log B_{d,k}(s)=-\eta/2+o(1)<0,\quad
 H_{d,k}(s)^2=h_k^2-2L^2/d+\eta+o(1).
                                                        \tag{12}
\]
The Mills expansion
h_k^2=2L-log L-log(4pi)+2+o(1) is used in
this cancellation.
Proposition 4 gives
k(U-P)+V >=2L^2/d-eta+o(1).
Take liminf and then eta->0, proving Theorem B.

## 4. Homogeneous partitions, exact group actions and rigidity

Call A *transitively equivariant* if a subgroup H of O(d)
permutes its cells transitively, up to Gaussian-null sets.

**Lemma 5.** Every transitively equivariant A has V(A)=0.

*Proof.* If T in O(d), invariance of standard Gaussian measure
and change of variables give b_{TA}=T b_A. Orthogonal maps
preserve norms, so all conditional centroid lengths are equal,
and V=0. QED.

This class includes regular-simplex Voronoi fans, cyclic score
orbits, and full-rank binary linear-code sign orbits, whose
coordinate-level group law has been Lean-formalized below.

**Corollary 6 (symmetry costs twice the general dimensional
coefficient).** If d_k/L^2->c and A_k are norm-homogeneous,
\[
 \liminf k[U_k-P(A_k)]\ge2/c.                \tag{13}
\]
If these partitions also satisfy
P(A_k)>=F_infty(k)-C/k, then
\[
                    c\ge2/[C+2(1-\gamma)]. \tag{14}
\]
Here gamma is Euler's constant.

*Proof.* The variance vanishes; apply Theorem B.
The simplex/Gumbel comparison of the sharp dimension-rate
paper proves
\[
             k[U_k-F_\infty(k)]
                  \le2(1-\gamma)+o(1).
\]
Hence near-optimality implies k(U-P)<=C+2(1-gamma)+o(1).
Combine with (13). QED.

*Proof of Theorem C.* Combining near-optimality with the same
simplex/Gumbel comparator yields
limsup k(U-P)<=C+2(1-gamma).
Subtract this from Theorem B and use V>=0
to obtain (4).

Every a_i lies in [0,h_k] by the sharp Gaussian halfspace
bound. Therefore |a_i-bar a|<=h_k.
If J is the set on which
|a_i-bar a|>=sqrt(v_0/2), then
\[
 V=\frac1k\sum_i(a_i-\bar a)^2
       \le v_0/2+(|J|/k)h_k^2.
\]
Since (4) gives V>=v_0 eventually, (5) follows.
Finally h_k^2~2log k, proving the stated cell-count
asymptotic. QED.

**Interpretation.** If c<2/[C+2(1-gamma)], no partition
with all centroid norms equal can meet additive C/k
accuracy at this dimension. Any such accurate general
partition must exhibit conditional centroid-norm variance
of at least 2/c-C-2(1-gamma) asymptotically, and at least
order k/log k measurably exceptional cell centroids.
This is a structural restriction on potential optimal
partitions, not a claim of global optimality for any
particular Gaussian code.

## 5. Lean and exact proof-evidence boundaries

The standalone Lean 4.34.1 file
formal/GaussianCodeCore.lean contains kernel-checked
theorems for the binary character law
chi_(u+v)(g)=chi_u(g)chi_v(g),
the coordinate sign-square identity, and the
corresponding diagonal sign-reflection action.
These are exact algebraic ingredients of code-orbit
transitivity. They do **not** formalize Gaussian
measure invariance, the cap tail, Berry–Esseen
or the complete analytic theorem.

A Python checker validates the pure finite
centroid-variance identity over diverse rational
profiles, including profiles with unequal centroids.
The analytic proofs above, not those finite tests,
establish universal validity.

## 6. Provenance and open boundaries

The Gaussian cap and tail constants are inherited from the
public spherical-cap converse and sharp dimension-rate
companion, where proofs and outward-rational numerical
tests are independently available. Gaussian orthogonal
invariance and conditional-centroid identities are classical.

The present theorems isolate and quantify a *variance*
penalty in every dimension-sensitive spherical-cap argument.
This is a meaningful refinement of the previous
unrestricted lower bound for transitive/equal-norm candidates,
not a resolution of the full optimal Gaussian partition
geometry. The sharp dimension coefficient, the possible
necessity of symmetry breaking for true finite-dimensional
optimizers, and the fixed-k Standard Simplex optimality
problem are still open.

No historical novelty or journal-priority claim is made.
