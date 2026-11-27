# Exact independence-root counts and a sharp sector for weighted spiders

A spider consists of a center joined to \(k\) paths (legs), each of
positive length. Give every vertex a positive real weight \(w_v\), and
write \(I(x)=\sum_{S\ {\rm independent}}x^{|S|}\prod_{v\in S}w_v\).
[Zhang and Tu, Theorem 4](https://arxiv.org/abs/2609.04694) proves that
every **unweighted** spider has all independence roots in the open
left half-plane. The results here concern the sector valid for arbitrary
positive weights, and the exact real and complex root counts when all
legs carry copies of the same weight sequence. These are root statements,
not a new general unimodality or log-concavity claim.

## Results

**Arbitrary weighted legs.** For \(k\ge2\), every root \(x\) satisfies
\[
 |\arg x|>\frac{\pi}{k-1}
 \quad\text{if } k\ge3,
\]
and all roots are negative real if \(k=2\). More precisely, for any root
with \(y=-x\) in the upper half-plane, there is a winding index
\(j=1,\ldots,\lfloor(k-1)/2\rfloor\) such that
\[
 0<\arg y<\frac{k-2j}{k-1}\pi . \tag{1}
\]
The angle at each index is best possible in the class of weighted
spiders, already by varying only the center weight of a star. In
particular all weighted three-leg spiders are strictly Hurwitz stable;
for every \(k\ge4\) there is a weighted \(k\)-leg star with a root of
positive real part. The unweighted theorem above is stronger than
the present sector for unweighted \(k\ge4\).

**Identically weighted legs.** Suppose the \(k\ge2\) legs each have
\(\ell\ge1\) vertices apart from the center, with weights
\(w_1,\ldots,w_\ell>0\) in order away from that center. Let
\(m=\lfloor\ell/2\rfloor\). The exact count of real roots is:
 
| Leg length | \(k\) odd | \(k\) even |
|:--|--:|--:|
| \(\ell=2m+1\) | \(m+1\) | \(2m+2\) |
| \(\ell=2m\) | \(m+1\) | \(2m+1\) |

They are all negative and simple, and the proof locates them between
adjacent resolvent poles. The degree is \(k(m+1)\) for odd \(\ell\)
and \(km+1\) for even \(\ell\). For each possible winding index \(j\),
the upper \(y\)-half-plane has exactly \(m+1\) roots of that index if
\(\ell\) is odd, and exactly \(m\) if \(\ell\) is even, counted with
multiplicity; the lower half-plane follows by conjugation. Thus, among
these spiders, a branching center (\(k\ge3\)) always forces nonreal
roots, independently of all common positive leg weights and the
positive center weight.

## A one-leg resolvent

Let \(A(x)\) be the independence polynomial of a leg alone, \(B(x)\)
the polynomial after deleting its first vertex, and \(C(x)\) that
after also deleting its second (take \(B=C=1\) if \(\ell=1\)).
Then \(A=B+w_1xC\). Put \(R(y)=A(-y)/B(-y)\).
Let \(J\) be the symmetric \(\ell\)-by-\(\ell\) tridiagonal matrix
with diagonal zero and off-diagonal entries
\(\sqrt{w_2},\ldots,\sqrt{w_\ell}\).
The path-edge matching expansion of the determinant gives
\(B(-y)=\det(I-\sqrt y\,J)\), and the first principal cofactor
is \(C(-y)\). Indeed, each nontrivial cycle in a nonzero determinant
term is an edge transposition; disjoint such edges identify
exactly the independent sets of the suffix path. Thus \(C/B\)
is the first diagonal entry of this resolvent.

The eigenvalues of \(J\) are simple: the first coordinate of an
eigenvector determines all others by the tridiagonal recurrence and
cannot vanish. They are symmetric about zero by conjugating with
alternating signs. Pairing a positive eigenvalue with its negative
in the spectral expansion gives
\[
 R(y)=1-\gamma y-\sum_{i=1}^m d_i\,\frac{y}{1-\lambda_i y},\qquad
 \lambda_i,d_i>0,\quad
 \gamma>0\iff \ell\text{ is odd}. \tag{2}
\]
Here \(\lambda_i\) is the square of a positive eigenvalue, the \(d_i\)
are \(w_1\) times the combined squared first coordinates in a paired
orthonormal eigenbasis, and the zero eigenvalue supplies \(\gamma\)
if present. In particular all poles \(1/\lambda_i\) are simple with
nonzero residues, and none of them is a zero of \(A(-y)\).

## Sector and sharpness

For \(0<\theta=\arg y<\pi\), the angle of \(1-\lambda y\) lies
strictly between \(\theta-\pi\) and zero. Thus every summand
\(-d_i y/(1-\lambda_i y)\) of (2) lies strictly in this same
sector. The terms \(1\) and \(-\gamma y\) are on its boundary rays
(the latter if present). The opening is less than \(\pi\) and there
is at least one nonconstant term, so their sum has the strict bound
\[
                   \theta-\pi<\arg R(y)<0. \tag{3}
\]

Writing \(R_a\) for the individual leg ratios and \(\tau>0\) for the
center weight, deletion of the center gives the nonreal root equation
\(\prod_a R_a(y)=\tau y\), because no \(B_a(-y)\) vanishes off the
positive real axis. The sum of their principal arguments is
\(\theta-2\pi j\) for an integer \(j\). By (3) it is negative and
greater than \(k(\theta-\pi)\). This forces \(j\ge1\) and gives (1),
including its index range. No nonreal roots are possible if \(k=2\),
and positivity of coefficients rules out nonnegative real roots.
For \(k=3\), the only index is \(j=1\), and (1) gives
\(0<\theta<\pi/2\).

For sharpness, take unit leaf weights on a star and let \(\tau\)
tend to infinity. Substituting \(y=s v\) with \(s=\tau^{1/(k-1)}\)
in \((1-y)^k-\tau y\) and dividing by \(s^k\) gives a limit
\((-v)^k-v\). Each nonzero limiting root is simple. Its upper-half-plane
arguments are exactly \(\theta_j=(k-2j)\pi/(k-1)\) for the indices
in (1). Around each such root, small disjoint circles and Rouché's
theorem give a converging root of the scaled polynomial. For a star
\(R(y)=1-y\), so the limiting sum of the leg arguments near that
root is \(k(\theta_j-\pi)=\theta_j-2\pi j\), which identifies
the index for all sufficiently large \(s\). In particular
\(\theta_1>\pi/2\) for \(k\ge4\), giving a root \(x\) with
\(\Re x>0\). This proves sharpness for the weighted class, with the
strict boundary in (1) not attained.

## Repeated legs: scalar equation and all real roots

For identical legs, put \(\alpha=1/k\) and
\(F(y)=y^{-\alpha}R(y)\), with the principal power off the
nonpositive real axis. The independence-root equation in \(y\)
is \(A(-y)^k-\tau y B(-y)^k=0\), equivalently \(F(y)^k=\tau\);
this includes positive \(y\) by continuous extension, with no
root at a pole or at zero.

On the positive real axis away from the poles,
\[
 yR'(y)-\alpha R(y)
 =-\alpha-\gamma(1-\alpha)y
   -\sum_i d_i y\,\frac{(1-\alpha)+\alpha\lambda_i y}
                          {(1-\lambda_i y)^2}<0. \tag{4}
\]
Hence \(F'<0\) on each interval of regularity.
At zero its limit is \(+\infty\), at a pole it has left limit
\(-\infty\) and right limit \(+\infty\). As \(y\to+\infty\),
it tends to \(-\infty\) if \(\ell\) is odd
(\(\gamma>0\)), and to \(0\) from above if \(\ell\) is even
(\(R(+\infty)=1+\sum_i d_i/\lambda_i>0\)).
So each of the \(m\) bounded intervals from zero to the last pole
has exactly one point with \(F=+\tau^{1/k}\), and one with
\(F=-\tau^{1/k}\) when \(k\) is even. The last interval has
the positive point and also the negative point precisely
when both \(k\) is even and \(\ell\) is odd. If there are no poles,
the interval \((0,\infty)\) is the last one. At every real root,
(4) implies \((F^k-\tau)'\ne0\), and multiplying by
\(yB(-y)^k\) does not change multiplicity. This proves the table.
The degree follows directly from the two terms with distinct
degrees, using degrees \(\lceil\ell/2\rceil,\lfloor\ell/2\rfloor\)
of the respective leg polynomials.

## Repeated legs: counting one complex branch

For upper-half-plane \(y\), (3) implies
\[
 -\pi+(1-\alpha)\arg y < \arg F(y)<-\alpha\arg y,
\]
with no angle wrapping. An upper-half-plane root with winding
index \(j\) therefore solves \(F(y)=\tau^{1/k}e^{-2\pi i j/k}\).
Consider the entire connected target region
\(\mathcal W=\{w:-\pi<\arg w<-\pi/k\}\).
For a compact set of targets in \(\mathcal W\), all upper-half-plane
solutions of \(F(y)=w\) stay in a compact subset of that half-plane.
Indeed, on the positive axis away from zero and the poles the
boundary value of \(F\) is real. On the negative axis the upper
boundary value lies on the ray of angle \(-\pi/k\), because
\(R(-r)=A(r)/B(r)>0\) for \(r>0\). At zero or a pole the modulus
goes to infinity. At infinity the modulus uniformly tends to
infinity for odd \(\ell\), by (2), or to zero for even \(\ell\).
Thus the argument principle makes the number of solutions counted
with multiplicity constant in \(\mathcal W\).

Let \(w=-t-i\eta\) with \(t>0\) fixed and \(\eta>0\) tending to zero.
The same compactness analysis, now allowing limiting positive
boundary points, shows that every solution accumulates at a positive
real point with \(F=-t\): no interior point can map to the negative
real axis, by the strict angle bounds. By (4) these points have
strict negative derivatives; each local inverse gives exactly one
solution above the real axis for small positive \(\eta\).
Their number is \(m+1\) if \(\ell\) is odd and \(m\) if it is even.
Every required nonreal branch target belongs to \(\mathcal W\),
completing the count. Multiplicity of \(F-w\) agrees with the
independence polynomial's multiplicity since \(w\ne0\) and
\(yB(-y)^k\ne0\) at those points.

The exact companion fixtures check path and spider expansion by
independent-set enumeration, the real-root table by rational Sturm
chains, and weighted stability and instability cases by rational
Routh arrays. The sector and complex branch counts are analytic.
