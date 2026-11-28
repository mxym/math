# Rigidity of single-response Gaussian location transport on odd grids

This note asks whether an arbitrary Markov kernel on a single wrapped
response can change the unknown location by a prescribed permutation
while keeping a given Gaussian location model. The kernel is not
assumed linear, additive, deterministic, or efficient. The answer for
keeping the same spherical law is exact: only a signed permutation of
the coordinates followed by a translation. A separate Fourier
obstruction quantifies the width loss that would be necessary for
other affine permutations. These are restrictions on an abstract
class of sample transformations, not a search algorithm, an
implementation assessment, or a bound on unrestricted Ring-LWE.

## 1. Model and theorems

Let \(d\ge1\), let \(q\ge3\) be odd, and put \(H=(\mathbb Z/q)^d\).
Use the grid \(h/q\) in \(\mathbb T^d\), with \(\mathbb T=\mathbb R/\mathbb Z\).
For \(0<b<1\), let \(P_h^{(b)}\) have Haar density
\[
 p_h^{(b)}(x)=\prod_{i=1}^d f_b(x_i-h_i/q),\qquad
 f_b(t)=\sum_{m\in\mathbb Z}b^{m^2}e^{2\pi i mt}.
\]
This is a wrapped spherical Gaussian in the product coordinates,
with circle width \(\sqrt{-\log b/\pi}\). Consider a bijection \(\pi:H\to H\)
and a Markov kernel \(K\) from \(\mathbb T^d\) to itself. The kernel
cannot depend on the unknown \(h\).

Write \(H_{\rm ell}(P,Q)^2=1-\int\sqrt{dP\,dQ}\) for squared
Hellinger distance, and \(\operatorname{TV}\) for total variation.
For \(b,b'\in(0,1)\), assume the conditional errors obey
\[
 \sup_{h\in H}\operatorname{TV}(KP_h^{(b)},P_{\pi(h)}^{(b')})
       \le \varepsilon. \tag{1}
\]

**Theorem A (rigidity).** If \(b'=b\) and \(\varepsilon=0\), then
\(\pi(h)=Ph+c\) for a signed permutation matrix \(P\) and \(c\in H\).
Moreover, for Haar almost every \(x\), \(K(x,\cdot)\) is the point
mass at \(Px+c/q\pmod{\mathbb Z^d}\). Conversely this deterministic
map has the stated exact property. There are absolute \(b_0,C_0>0\)
such that, for \(b'=b\le b_0\), every non-signed-affine \(\pi\) in (1)
satisfies \(\varepsilon\ge C_0 b^2/q^2\), independent of \(d,q\).
For a fixed \(b\in(0,1)\) an exact lower bound in terms of two
Hellinger distances is given below. The approximate result concerns
the permutation, not pointwise closeness of the kernel.

**Theorem B (harmonic obstruction with unequal widths).** For
\(v\in H\), let \(m_q(v)=\min_{k\in\mathbb Z^d,\ k\bmod q=v}\|k\|^2\).
For any \(w\in\mathbb Z^d\) and \(v\in H\), (1) implies
\[
 (b')^{\|w\|^2}
 \left|\frac{1}{|H|}\sum_{h\in H}
       e^{2\pi i(v\cdot h-w\cdot\pi(h))/q}\right|
 \le
 \left(\sum_{k\bmod q=v} b^{2\|k\|^2}\right)^{1/2}+2\varepsilon.
 \tag{2}
\]
If \(\pi(h)=Th+c\) with \(T\in\operatorname{GL}_d(\mathbb Z/q)\),
fix \(q,d,T\) and suppose (1) holds exactly as \(b\downarrow0\).
Then necessarily
\[
 \liminf_{b\downarrow0} \frac{\log b'}{\log b}
 \ \ge\
 \beta_q(T):=\max_{v\in H\setminus\{0\}}\frac{m_q(T^{\mathsf T}v)}{m_q(v)} .
 \tag{3}
\]
The condition \(\beta_q(T)=1\) holds exactly for signed permutations.
For example the two-dimensional shear with \(T^{\mathsf T}(1,1)=(1,2)\)
has \(\beta_q(T)\ge5/2\) for odd \(q\ge5\); a bound based only on
the images of the coordinate unit vectors would give 2. For a
fixed unimodular integer \(T\) and \(q\to\infty\), \(\beta_q(T)\to
\|T\|_{\rm op}^2\).

Even for arbitrary bijections, at fixed \(d,q\) every
non-signed-affine permutation requires \(b'=O_{d,q}(b^2+\varepsilon)\)
as \(b\downarrow0\). None of these unequal-width statements claims
sufficiency or an optimal positive construction.

## 2. The Hellinger geometry detects neighboring locations

Let \(g_b=\sqrt{f_b}\) and \(A_b(t)=\int_{\mathbb T}g_b(u)g_b(u-t)\,du\).
The Jacobi product
\[
 f_b(t)=\prod_{j\ge1}(1-b^{2j})
    \bigl(1+2b^{2j-1}\cos(2\pi t)+b^{4j-2}\bigr)
\]
has positive factors and makes \(g_b\) strictly decreasing in
the circular distance from zero on \([0,1/2]\). The product follows
from the [Jacobi triple product](https://dlmf.nist.gov/20.5.E9).
The autocorrelation \(A_b\) is also strictly decreasing there.
For completeness, level sets of \(g_b\) above its minimum are
centered arcs of radius \(r\in(0,1/2)\). For two arcs of radii
\(r,s\), write
\[
 m(t)=(r+s-t)_+-(|r-s|-t)_+,\quad t\ge0.
\]
For center displacement \(t\in[0,1/2]\), their overlap length on
the circle is \(m(t)+m(1-t)\). This is nonincreasing: wherever the
second term has derivative \(+1\), \(t>1-r-s\ge|r-s|\) and
\(t\le1-t<r+s\), so the first has derivative \(-1\).
For \(t_1<t_2\), radii both close to an \(r\) with \(t_1<2r<t_2\)
give positive overlap at \(t_1\) and none at \(t_2\). Such choices
occur on a positive-measure region of level pairs because \(g_b\)
is continuous and strictly decreasing at those radii. The layer
integral for \(g_b(u)g_b(u-t)\) proves strictness.

By tensorization of the affinity,
\[
 H_{\rm ell}\bigl(P_h^{(b)},P_{h'}^{(b)}\bigr)^2
       =1-\prod_{i=1}^d A_b((h_i-h'_i)/q). \tag{4}
\]
Among distinct pairs, the minimum \(h_1=\sqrt{1-A_b(1/q)}\)
occurs exactly for differences \(\pm e_i\), those of a
nearest-neighbor pair on the grid. In the case where some
non-neighboring pair exists, define
\[
 h_2=\min\left\{
 \sqrt{1-A_b(1/q)^2}\ (d\ge2),\
 \sqrt{1-A_b(2/q)}\ (q\ge5)\right\},
 \tag{5}
\]
taking the minimum of only the available terms. Strict decrease and
\(0<A_b(1/q)<1\) imply \(h_2>h_1\), and (5) is the minimum on
non-neighboring pairs. The only case with no non-neighbor is
\(d=1,q=3\), where every bijection is signed-affine.

Hellinger distance contracts under \(K\). Its triangle inequality
and \(H_{\rm ell}\le\sqrt{\operatorname{TV}}\) imply for every
neighboring pair \(h,h'\) in the same-width case that
\[
 H_{\rm ell}\bigl(P_{\pi(h)}^{(b)},P_{\pi(h')}^{(b)}\bigr)
      \le h_1+2\sqrt{\varepsilon}.
\]
If \(\varepsilon<(h_2-h_1)^2/4\), every edge maps to an edge.
Bijection on a finite vertex set then gives an automorphism of the
nearest-neighbor graph.

Here is an elementary description of that graph's automorphisms.
At each vertex, two incident edges point along opposite directions
in the same coordinate exactly when they do not lie in a common
four-cycle through the vertex. Two different directions give a
square; two opposite directions have no second common neighbor,
since \(q\) is odd (including \(q=3\)). Thus the edge actions at
a vertex pair the directions and are signed permutations. After
a translation, permutation, and sign flips, an automorphism may
be assumed to fix zero and all its neighbors. If it fixes \(x\)
and all its neighbors, consider \(y=x+e\) for a signed
coordinate vector \(e\). For every other coordinate direction
\(e'\), the unique common neighbor of \(y\) and \(x+e'\) other
than \(x\) is \(y+e'\); hence it is fixed. The last neighbor \(y+e\)
is the unique opposite of \(x\) at \(y\) and also is fixed.
Connectedness proves the normalized automorphism is the identity.
This is also the cycle case of the Cartesian-product automorphism
theorem; see [Imrich's original automorphism theorem](https://www.sciencedirect.com/science/article/pii/0095895671900086) and [Imrich, Klavžar and Rall, Theorem 15.5](https://www.routledge.com/Topics-in-Graph-Theory-Graphs-and-Their-Cartesian-Product/Imrich-Klavzar-Rall/p/book/9781568814292).

To obtain the uniform small-\(b\) bound, the Fourier coefficients of
\(g_b\) have \(\widehat g_b(\pm1)=b/2+O(b^2)\), and the sum of
\(k^2|\widehat g_b(k)|^2\) over \(|k|\ge2\) is \(O(b^4)\).
These follow by Taylor expansion
\(g_b(t)=1+b\cos(2\pi t)+O_{C^1}(b^2)\) and Parseval applied
to the derivative of the remainder. The inequality
\(1-\cos(k u)\le k^2(1-\cos u)\) for integer \(k\) now gives, uniformly in \(t\),
\[
 1-A_b(t)=b^2\sin^2(\pi t)(1+O(b)).
 \tag{6}
\]
For odd \(q\ge5\) the ratio \(\sin(2\pi/q)/\sin(\pi/q)\)
is at least \(2\cos(\pi/5)>1\). In the two-coordinate term the
ratio to \(h_1\) is \(\sqrt{1+A_b(1/q)}\), bounded away
from 1 for small \(b\). Therefore \(h_2-h_1\ge c h_1\ge c' b/q\)
with absolute positive constants. Any non-signed-affine
permutation violates the strict upper threshold, proving the
claimed \(C_0 b^2/q^2\) lower bound.

## 3. Exact kernel rigidity

In the exact same-width case, compose the output with the inverse
of the affine torus map established in Section 2. That map preserves
the noise shape, so the resulting kernel \(L\) fixes all \(P_h^{(b)}\).
Under \(X\sim P_0^{(b)}\), \(Y\sim L(X,\cdot)\), both marginal
laws are \(P_0^{(b)}\). Set \(r_h(x)=p_h^{(b)}(x)/p_0^{(b)}(x)\).
By the equality of all the output laws,
\(\mathbb E[r_h(X)\mid Y]=r_h(Y)\). Each \(r_h\) is bounded at
fixed \(b,d,q\), so identical marginals and the variance decomposition
force \(r_h(X)=r_h(Y)\) almost surely. The finite collection of
these equalities holds simultaneously.

This likelihood-ratio vector distinguishes all points of \(\mathbb
T^d\). Indeed the entries associated with shifting only coordinate
\(i\) reveal the vector \((f_b(t-k/q)/f_b(t))_{k\in\mathbb Z/q}\)
at \(t=x_i\). By strict radial monotonicity, the two largest
entries identify the two nearest grid points (choose a fixed
tie convention if needed). They are adjacent, and any \(t\) for which
they are the nearest pair lies on their closed short arc.
On that arc the ratio of the values of \(f_b\) about its two
endpoints is strictly monotone, since one distance strictly
increases while the other strictly decreases. Thus those
entries specify \(t\), including endpoints and midpoints.
Applying this in every coordinate gives \(X=Y\) almost surely.
Since \(p_0^{(b)}>0\), \(L(x,\cdot)=\delta_x\) Haar almost
everywhere. Undoing the composition proves Theorem A.

## 4. Harmonic constraints

For \(v\in H\), define the complex density
\[
 F_v(x)=\frac1{|H|}\sum_{h\in H}e^{2\pi i v\cdot h/q}p_h^{(b)}(x)
       =\sum_{k\bmod q=v}b^{\|k\|^2}e^{2\pi i k\cdot x}.
\]
The equality is finite-grid orthogonality applied to the absolute
Fourier series. For the unit-modulus output observable
\(e^{-2\pi i w\cdot y}\), its expectation in the target law is
\((b')^{\|w\|^2}e^{-2\pi i w\cdot\pi(h)/q}\).
Replacing the target by the actual law costs at most
\(2\varepsilon\) per expectation by (1). After taking the
\(v\)-weighted average over \(h\), the actual expectation
has modulus at most \(\|F_v\|_1\), because the pullback of a
unit-modulus observable under a Markov kernel is bounded by
one. Parseval and Cauchy–Schwarz then give (2).

With odd \(q\) there is a unique centered representative for
each residue, and in one coordinate the first possible strictly
larger squared norm differs by at least \(q\). The tail relative to
the centered term in the squared coefficients of \(F_v\) is
\(O_{q,d}(b^{2q})\) as \(b\downarrow0\), uniformly over the
finite \(H\), by a geometric bound on each one-dimensional
Gaussian series and multiplication over the fixed \(d\).
Thus the square root on the right of (2) is
\(b^{m_q(v)}(1+O_{q,d}(b^{2q}))\).
For an affine permutation and any \(w\bmod q\ne0\), the
Fourier coefficient on the left of (2) has modulus 1 at
\(v=T^{\mathsf T}w\bmod q\). Take \(w\) centered and
\(\varepsilon=0\), divide logarithms by the negative \(\log b\),
and maximize over \(w\bmod q\) to get (3).
Since the finite invertible map \(T^{\mathsf T}\) permutes the
residues, \(\beta_q(T)\ge1\); equality requires every norm to
be preserved around its finite permutation orbit. In particular
every \(e_i\) must map to \(\pm e_j\), and invertibility makes
the target axes distinct. The converse follows immediately.
For a fixed unimodular integer \(T\), comparison with the
image of each centered \(w\) gives \(\beta_q(T)\le\|T\|_{\rm op}^2\).
Integer vectors with directions arbitrarily close to a maximizing
unit vector have fixed finite coordinates once a directional
accuracy is chosen; for large enough \(q\) neither \(w\) nor
\(T^{\mathsf T}w\) wraps, giving the matching limit.

Finally, for any bijection let \(z_i(h)=e^{-2\pi i\pi_i(h)/q}\).
It has constant modulus 1 and mean zero because \(\pi_i\) is
uniform when \(h\) is uniform. Suppose all its nonzero Fourier
coefficients lie on the axes \(\{\pm e_j\}\). Then \(z_i=\sum_j g_j(h_j)\)
with \(g_j(u)=a_j e^{2\pi i u/q}+c_j e^{-2\pi i u/q}\) of mean
zero. Taking the conditional expectation of \(|z_i|^2\) given
\(h_j\) and using independence shows \(|g_j|\) is constant in
\(h_j\). For odd \(q\), the two frequencies \(\pm2\bmod q\)
are nonzero and distinct, so constancy gives \(a_j\overline{c_j}=0\).
Conditioning on \(h_j,h_k\) now shows \(\operatorname{Re}
(g_j(h_j)\overline{g_k(h_k)})=0\) for distinct \(j,k\).
A nonzero \(g_j\) is a scalar times a one-coordinate character,
whose values span \(\mathbb C\) as a real vector space
because \(q\ge3\). Thus at most one \(g_j\) is nonzero.
If this conclusion holds for all \(i\), the \(q\)-th-root
range forces each scalar to be a \(q\)-th root, and bijectivity
forces different chosen axes, so \(\pi\) is signed-affine.
Otherwise some \(i\) has a nonzero coefficient at
\(m_q(v)\ge2\). There are only finitely many bijections at fixed
\(q,d\), so the nonzero coefficient's magnitude is bounded below
by a positive constant depending only on \(q,d\). Apply (2)
with \(w=e_i\), proving \(b'=O_{d,q}(b^2+\varepsilon)\).

## 5. Scope in the dual torus

In a dyadic cyclotomic with odd modulus \(q\), the codifferent of
\(\mathbb Z[Y]/(Y^d+1)\) is \((1/d)R\). Its coefficient coordinates
identify the continuous canonical spherical noise on the codifferent
torus with \(p^{(b)}_0\), since the power basis is orthogonal.
In the [LPR definition](https://web.eecs.umich.edu/~cpeikert/pubs/ideal-lwe.pdf)
fix a public coefficient that is a unit. Multiplication by this
coefficient permutes all \(q\)-grid signal locations for scalar
Ring-LWE. Thus Theorem A applies to a proposed conditional
response channel for this unit coefficient, when mapping it to
another fixed unit coefficient, with the label permutation
composed with the two unit multiplications. Conditional
uniformity over all hidden labels is essential. This is
a single response, same torus/modulus, fixed-unit obstruction;
it is not a restriction on maps mixing different coefficients
in their conditional distributions, using several samples
jointly, having side information, only preserving an average
over hidden values, or changing the ring/modulus.

The comparison of families by channels is classical
[Blackwell](https://doi.org/10.1214/aoms/1177729032).
The earlier [affine divisor-quotient note](affine-divisor-quotient-noise.md)
treats different moduli with pre-assumed pointwise affine
transforms and independent dithers. Here the Markov kernel
is arbitrary, and the exact conclusion about its shape is
derived from the family itself. [Bogdanov, Tan and Vasudevan](https://arxiv.org/abs/2610.12913)
study sample-preserving **search-to-decision reductions** over
finite fields, not the stated single-response equality of
conditional torus experiments. This note does not constrain
their reduction or give a general classical running-time
conclusion. The companion checker verifies finite graph and
frequency-bookkeeping identities on small synthetic grids,
not the analytic inequalities.
