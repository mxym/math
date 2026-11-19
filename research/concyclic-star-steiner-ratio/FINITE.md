# A sharp every-cardinality star bound on arbitrary circles

For n≥2 distinct *concyclic* sites in the Euclidean plane and arbitrary positive demand masses, the minimum nodal star divided by the unrestricted Weber minimum is at most
$$
 C_n=(2/n)\cot(\pi/(2n)).
$$
The regular n-gon with equal weights attains this. No assumptions on the circle center, angular gaps, or Weber point. Zero masses may be deleted since doing so removes candidate centers and C_n increases in n (tan x/x increases on (0,π/2)). This proves only the concyclic case of the stronger finite-cardinality conjecture, not that conjecture for arbitrary planar point sets. Dumitrescu–Tóth–Xu proved the corresponding estimate for unit sites **with the circle centered at the Weber point**, and separately for regularly spaced rays. The present proof strengthens the unrestricted-cardinality circular estimate in CONCYCLIC.md. No claim of bibliographic priority.

## 1. The scalar claim suffices

Fix any reference o. If it is a site the result is immediate; otherwise invert in the unit circle about o=0: x_i=p_i/|p_i|², so d(p_i,p_j)=|p_i||p_j|d(x_i,x_j). If the inverse sites lie on a line, put equal α-masses at its two extreme sites. Their mean distance to any inverse site is half their separation, which is at most their mean distance to the origin. If the inverse sites lie on a circle, write x_i=a_0+R u_i, u_i=exp(iθ_i) in circular order, ζ=−a_0/R. Define x_i^ang=(θ_{i+1}−θ_i)/4 with cyclic positive gaps, temporarily denoting these **angular** numbers by x_i below; their sum is π/2. Set τ_i=tan x_i, h_i=τ_i+τ_{i−1}, H=Σh_i. By the half-angle quadrature in CONCYCLIC.md,
$$
  \sum_i h_i |u_i-u_j|=4 \quad(\text{every }j).
$$
Indeed, |e^{it}−z| is the norm of a fixed real-linear map on (cos(t/2),sin(t/2)); this map has rank one with constant sign on each node-free interval when z is a node. Sine interpolation of the two endpoint vectors followed by integration gives weights 2τ_i at each end; the full integral when z is a node equals 8. We will prove the sharp inequality
$$
 Q(\zeta)=\sum_i h_i |u_i-\zeta|\ \ge H_0:=2n\tan a,\qquad a=\pi/(2n). \tag{1}
$$
Then α_i=h_i gives Σα_i d(x_i,x_j)≤C_n Σα_i |x_i| in the original inverse coordinates. Sampling a candidate with probabilities proportional to α_i|x_i| yields expected distance to each p_j at most C_n|p_j|, and summing proves the result for all demands. The case n=2 follows instead immediately from the existence of a nodal weighted median on a segment. A regular n-gon has its center as Weber point by symmetry and convexity and, on the unit circle, its nodal star cost is Σ_{j=1}^{n−1}2 sin(πj/n)=2 cot(π/(2n)), versus free cost n.

It suffices in (1) to consider t=|ζ|≤1, since projecting any exterior ζ radially into the closed disk decreases its distance to every node.

## 2. Two lower estimates for Q

Write J for counterclockwise rotation by π/2 of a real planar vector. Let m_i be the unit tangent at the midpoint angle (θ_i+θ_{i+1})/2. Set v_i=m_i/(2 cos²x_i). In complex coordinates centered at the angle θ_i, 
$$
 e^{-i\theta_i}(v_i-v_{i-1})
 =\tfrac i2[(1+i\tau_i)^2-(1-i\tau_{i-1})^2]
 =-h_i-i h_i(\tau_i-\tau_{i-1})/2.
$$
Thus Σh_i[u_i+(τ_i−τ_{i−1})Ju_i/2]=0. Put d_i=τ_i−τ_{i−1}. From the Pythagorean identity, 
$$
 |u_i-\zeta|\ge 1-\zeta\cdot u_i+
 \frac{(\zeta\cdot Ju_i)^2}{2(1+t)}.
$$
This also holds at ζ=u_i, by continuity. After weighting, use Σh_i u_i=−Σh_i d_i Ju_i/2 and complete the square termwise. This gives
$$
 Q(\zeta)\ge H-\tfrac{1+t}{8}\sum_i h_i d_i^2. \tag{2}
$$

A complementary bound is
$$
 Q(\zeta)\ge \pi(1+t^2/4)+k(t)(H-\pi),\qquad k(t)=(1-t)^2/(1+t). \tag{3}
$$
For t<1 the function g(θ)=|e^{iθ}−ζ| satisfies g''+g/4=(1−t²)²/(4g³)≥k/4. Hence g−k is dominated on each gap by its half-angle sine interpolant. This follows, for example, from the positive Dirichlet Green kernel of −d²/dθ²−1/4 on a gap (s,u) of length less than 2π: for θ≤v its kernel is 2 sin((θ−s)/2)sin((u−v)/2)/sin((u−s)/2), and it is symmetric. Integrating the endpoint interpolants yields Q−kH≥(1/2)∫g−kπ. By Parseval applied to the analytic square root (1−t z)^{1/2} on the disk, its first two coefficients alone give ∫g/(2π)≥1+t²/4. The case t=1 follows by continuity.

## 3. The nodal quadrature defect

Put u=tan a and v=max τ_i≥u. Let
$$
 g(s)=s-u-(1+u^2)(\arctan s-\arctan u),\qquad
 K(s,u)=\frac{3s^3+6s^2u+4su^2+2u^3}{5(s+2u)}.
$$
We have H−H_0=2Σg(τ_i) by Σx_i=na. Since g'=(s²−u²)/(1+s²), on the interval between u and s integrate the positive weight |y²−u²| times 1/(1+y²). Its total unnormalized mass is (s−u)²(s+2u)/3. Its weighted mean of y² equals K(s,u), by elementary integration (extend at s=u by continuity). Jensen for x↦1/(1+x) gives
$$
 g(s)\ge (s-u)^2(s+2u)/[3(1+K(s,u))].
$$
K is increasing in both nonnegative arguments: the numerators of its partial derivatives, with common denominator 5(2u+s)², are 6(u+s)(u²+3us+s²) in s and 2u(4u²+7us+4s²) in u. Also K(s,u)≤v² when s,u≤v, by its weighted-mean interpretation.

For any x,y≥0, the identity
$$
 4[(x-u)^2(x+2u)+(y-u)^2(y+2u)]-3(x+y)(x-y)^2
 =(x+y-2u)^2(x+y+4u)
$$
is nonnegative. Summing over adjacent τ values therefore gives
$$
 \sum_i h_i d_i^2\le 4(1+K(v,u))(H-H_0).
$$
Because H≥H_0 by Jensen, (2) proves (1) whenever
$$
 (1+t)(1+K(v,u))\le2. \tag{4}
$$

## 4. Close the scalar complementary region for n≥4

If (4) fails and n≥5, since K(v,u)≤v² we have b:=arctan v> (arccos t)/2 ≥ (π/4)(1−t); the last bound uses concavity of arccos on [0,1]. The simple inequality tan b−b≥b³/3 follows by integrating tan²b≥b². Hence H−π=2Σ(tan x_i−x_i)≥2b³/3. Inserting this in (3) proves (1) once
$$
  \tfrac{\pi}{4}t^2+\tfrac{\pi^3}{96}\frac{(1-t)^5}{1+t}
  >10\tan(\pi/10)-\pi. \tag{5}
$$
Indeed 2n tan(π/(2n)) decreases in n. The RHS is below 108/1000; the LHS is above 108/1000 on [0,1] by the explicit rational certificate below.

For n=4, u=√2−1 and H_0−π<1723/10000. For t≥47/100 already πt²/4>1723/10000. For t≤47/100 put V=118/100−11t/10. The elementary rational bounds
$$
 K(V,83/200)<(1-t)/(1+t),\qquad
 \pi t^2/4+k(t)\cdot 2[V-675/1000-(V-4/5)/(1+(4/5)^2)]>1723/10000 \tag{6}
$$
hold on this whole interval. By u<83/200, monotonicity of K and failure of (4), v>V. Convexity of s−arctan s gives 2(v−arctan v)≥2[V−675/1000−(V−4/5)/(1+(4/5)²)] because arctan(4/5)=π/4−arctan(1/9)<675/1000. This is a lower bound for H−π. Thus (6) and (3) give (1).

**Scalar certificate.** The accompanying finite_check.py uses only integer fractions. For t∈[j/10000,(j+1)/10000]=[A,B], bound each increasing positive factor at A and each decreasing one at B. For (5), use (31415/10000)A²/4+(31415/10000)³(1−B)^5/[96(1+B)]>108/1000. For (6), compare K(V(A),83/200) with (1−B)/(1+B); in the second inequality use A², k(B) and the positive tangent bracket at B. The regular-input comparisons use tan²(π/10)=(5−2√5)/5, 3.1415<π<3.1416 (certified from Machin's identity), and direct squares of rational bounds for √2,√5. Every cell is strictly certified, with minima exceeding the stated comparisons by respectively 1874, 16377 and 853 parts per million; there is no sampling inference.

## 5. The three-node case directly

Write a,b,c for the side lengths opposite the three normalized nodes, and let s=(a+b+c)/2, x=s−a,y=s−b,z=s−c. All are positive. The weights w_i=h_i/4 solve D w=1 for their mutual distance matrix. This matrix has determinant 2abc and the unique solution is w_1=ax/(abc), w_2=by/(abc), w_3=cz/(abc). Write A=ax,B=by,C=cz and T_p,T_W for the areas of the triangles with sides (a,b,c) and (A,B,C). The latter is a triangle since B+C−A=2yz and its cyclic mates are positive.

Take vectors f_1,f_2,f_3 of lengths A,B,C with sum zero. They can be rotated and reflected as desired. Duality of the Euclidean norm gives for every ζ
$$
 abc\sum_i w_i|u_i-\zeta|\ge
 \max_{\text{rotations/reflections}}\sum_i f_i\cdot (u_i-u_3)=:L.
$$
To compute the maximum, take the square modulus of (u_1−u_3)conj(f_1)+(u_2−u_3)conj(f_2), choosing the reflection so that the angle sines multiply positively; the common rotation makes this sum real and nonnegative. Law of cosines and the area formula then give
$$
 2 L^2=a^2(B^2+C^2-A^2)+b^2(A^2+C^2-B^2)+c^2(A^2+B^2-C^2)+16T_pT_W.
$$
Let p=x+y+z,q=xy+yz+zx,r=xyz. Heron gives T_p²=pr, T_W²=r² q and abc=pq−r. Substituting a=y+z,A=x(y+z) and cyclically into the displayed formula gives
$$
 4L^2-3(abc)^2=p^2q^2-18pqr-15r^2+32r\sqrt{pqr}
 =r^2(U-3)(U-1)^2(U+5),\quad U=\sqrt{pq/r}\ge3
$$
by AM–GM. Thus Σ w_i|u_i−ζ|≥√3/2, or Q(ζ)≥2√3=6 tan(π/6). This argument does not rely on an interior weighted Fermat point. ∎

The n=3 argument actually bounds the star ratio for all weighted triangles; every noncollinear triangle is of course concyclic. No part of this note reduces arbitrary four-or-more-site planar sets to circles.
