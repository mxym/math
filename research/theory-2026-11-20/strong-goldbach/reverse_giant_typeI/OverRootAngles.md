# A fixed-target over-root angle in the double giant remainder

Keep the exact signed remainder \(\mathcal D_I\) of
[SecondTypeI.md](SecondTypeI.md) and all its cuts. Thus
\(N\) is prescribed even, \(L=\log N\), \(S=\exp((\log L)^4)\),
\(B=N/S\), and \(I\subset[N^{1/2+\varepsilon},B]\).
In \(bj+amk=N\) let
\[
 t=\frac{\max(\log a,\log(mk))}{L},\qquad s=\frac{\log b}{L}.
\]
For fixed \(\eta>0\) define the following actual subregion:
\[
 s\ge \tfrac12+\eta,\qquad
 \frac{56t-17}{23}+\eta\le s\le t-\eta.                         \tag{1}
\]

**Theorem.** The restriction of \(\mathcal D_I\) to (1)
is \(O_{A,\varepsilon,\eta,J_0}(NL^{-A})\) for every fixed
\(A>0\), uniformly in the prescribed even target.
It is a signed deletion of an over-root region and does
not control the full surviving remainder. For example,
the exponents \((a,m,k,b)=(.506,.245,.249,.504)\)
of \(N\) satisfy the strict exponent rails for
\(\eta=.001\), with \(ak\) of exponent \(.755\).
This is outside both the fixed sub-root range of
[ConductorHalf.md](ConductorHalf.md) and all three
[integer rectangles](IntegerRectangles.md) on any
giant interval admitting that exponent. These exponents
describe the geometric chart, not a claim of an individual
prime or factorization at these exact powers.

## 1. Independent boxes with residue exactly \(N\)

Open \(d\mid m,\ d<amk/B\), and put
\[
   h=ad,\qquad n=m/d,\qquad w=nk,\qquad y=hw.
\]
Only \(d\ll_{J_0}S\) is possible. The exact residue is
\(h w\equiv N\bmod b\), not \(a n k\equiv N\overline d\).
Use independent literal intervals \(J_h,J_d,J_n,J_k\)
obtained from a log mesh. On each box the two sequences are
\[
 \gamma(h)=1_{h\in J_h,\,(h,N)=1}
     \sum_{d\mid h,\ d\in J_d}\mu(d)\mu(h/d),\qquad
 \xi(w)=1_{(w,N)=1}
     \sum_{\substack{nk=w\\n\in J_n,\ k\in J_k}}1.                \tag{2}
\]
The \(d\)-factor has not been replaced by another Möbius
coefficient on \(h\): \(\mu(d)\mu(h/d)\) is kept including
shared factors. Both coefficients are bounded in absolute
value by \(\tau\). For positive upper counts replace all
Möbius factors in (2) by \(1\) and drop the target masks.
For either version the input intervals are fixed before
varying \(b\), and independent of \(N\bmod b\).

The longer sequence is Siegel–Walfisz in the exact sense of
[Fouvry–Radziwiłł, Definition 1](https://arxiv.org/abs/1812.00562v2).
Here are proofs of the required uniformity. Write \(T\) for
the length scale of the longer factor, which is polynomial
in \(N\), not the length of its short endpoint interval.

* If \(\gamma\) is longer and signed, fix \(d\). In a reduced
  class \(c\bmod q\), \(d\) must be a unit modulo \(q\), and
  the \(a=h/d\) residue is \(c\overline d\bmod q\).
  An auxiliary coprimality mask \(r\) also requires
  \((d,r)=1\) and imposes the mask \(Nr\) on \(a\).
  Use the exact identity
  \(\mu(a)1_{(a,Nr)=1}=\sum_{e\mid a,\ P^+(e)\mid_{\rm supp}Nr}\mu(a/e)\).
  For \(q\le L^C\), split \(e\) at \(\sqrt{T/d}\);
  the smaller terms use classical Möbius Siegel–Walfisz
  on the actual reduced residue if \((e,q)=1\), and
  the larger are bounded by the reciprocal Rankin tail.
  The Euler norm of \(N\) at \(1-1/(10\log L)\) is
  \((\log L)^{O(1)}\) by
  [SecondTypeI.md](SecondTypeI.md), §1, and the extra
  factor for \(r\) is at most \(\tau(r)^2\), even if
  \(r\) is not polynomially bounded. This also proves
  the bound without a residue for the reduced principal
  sum, using \(Nqr\) as mask and \(q\le L^C\).
  Both bounds before the \(d\)-sum are
  \(O_A((T/d)L^{-A}\tau(r)^2)\). At larger \(q\), use
  the trivial \(O(T/(dq)+1)\) and principal
  \(O(T/(d\varphi(q))+1)\), and \(\varphi(q)\gg\sqrt q\).
  Summing \(d\) costs the usual harmonic and an additive
  \(O(S)\), negligible at the polynomial scale \(T\).
* If \(\gamma\) is longer and positive, fix \(d\) as above.
  For the progression count on \(a\) use inclusion–exclusion
  over primes of \(r\) outside \(q\). The main density is
  \(\prod_{p\mid r,\,p\nmid q}(1-1/p)/q\), exactly equal
  to the corresponding reduced principal density.
  The class count error is \(O(\tau(r))\) and the
  principal error is \(O(\tau(qr)/\varphi(q))\ll\tau(r)\).
  Summing up to \(O(S)\) values of \(d\) is again
  power-small relative to \(T\).
* If \(\xi\) is longer, fix the shorter of \(n,k\).
  The other is an interval of scale at least \(\sqrt T\),
  where a reduced class exists only when the short factor
  is a \(q\)-unit. Impose the auxiliary units \(r\) and,
  in the actual version, the target units \(N\) by the
  same inclusion–exclusion and density identity. The
  total absolute floor is
  \(O(T^{1/2}\tau(r)\tau(N))=T^{1/2+o(1)}O(\tau(r))\).
  Here \(\tau(N)\) is used only with a power reserve.
  The positive version has the same proof without \(N\).

All expansions allow arbitrary real interval endpoints and
the uniformly bounded scale ratios. The sign in the first
bullet matters; no arbitrary signed divisor coefficient
is presumed Siegel–Walfisz.

## 2. The dispersion rails and the arithmetic boundary

On a box meeting the physical central range \(y\asymp N\),
embed the short and long factor intervals of \(h,w\)
in \([M_0,2M_0]\), \([T,2T]\), using their own lower
endpoints after a finer box mesh if needed. The scale
\(X_0=M_0 T\) satisfies \(X_0\asymp_{J_0}N\).
The exponent of \(T\) equals \(t+o(1)\), because
\(h=ad\), \(w=mk/d\), and \(d\ll S=N^{o(1)}\).
In (1) one has \(t\ge.5+2\eta\), so the long orientation
does not change across such a box for large \(N\).
The rails in [Fouvry–Radziwiłł, Theorem 1.1](https://arxiv.org/abs/1812.00562v2)
are
\[
   T^{56/23}X_0^{-17/23+\epsilon_0}\le R\le T X_0^{-\epsilon_0}
   \qquad(b\asymp R).
\]
They hold with \(\epsilon_0>0\) sufficiently small
depending on the fixed \(\eta\); fixed factors at the
ends of a modulus dyad are absorbed by the margins.
The same rails hold for the immediately intersecting
boundary boxes of a log-fine mesh.

The published statement uses \(1\le |a_0|\le X_0\),
whereas its residue parameter here is \(a_0=N\).
We use the fixed-factor extension \(|a_0|\le C_{J_0}X_0\)
audited in [the balanced-semiprime giant cross estimate](../balanced_semiprime_giant_cross/Proof.md),
§1. In the primary proof, the divisor estimates of
§§3.1 and 4.1 use only
\(|uv-a_0|\ll_C X_0\); reduced-class zero modes only
need \((a_0,b)=1\). The smooth reciprocal phase of
§3.2 has logarithmic derivative bounded on its
support by \(O(|a_0|H_0/(T R))\),
with \(H_0\ll X_0^\theta R/M_0\) as in (14).
It stays \(O_C(X_0^\theta)\).
The incomplete Kloosterman gcd bound there uses
\(\tau(a_0h')\ll X_0^{O(\theta)}\) at the same
polynomial range. In §4.4 the Bettin–Chandee
prefactor uses \(|a_0|R' H_0/T^2\) with
\(R'\ll T/R\) as in (35); it too remains
\(O_C(X_0^\theta)\). The fixed enlargement does
not change the powers in (42)–(44). No reduction
of the macroscopic target to a variable residue
representative, and no moduli coprime to the
target removed by fiat, are used.

Theorem 1.1 now gives an absolute sum of errors
\(O_A(NL^{-A})\) across each modulus dyad for each
of the fixed independent boxes, in both versions
of (2). The reduced principal is exactly the
product with \((hw,b)=1\) divided by \(\varphi(b)\).
Thus for each fixed box one may select arbitrary
subsets of the moduli and multiply by bounded
box weights depending on \(b\).

To handle all literal gates, mesh four positive
coordinates \(h,d,n,k\) with relative width
\(O(L^{-F})\), with \(F\) fixed and large.
The number of initial dyads and log-fine boxes
is a fixed power of \(L\); the \(d\)-axis is
meshed, not summed in \(O(S)\) separate boxes.
All effective conditions, including the strict
short cutoff and the lower \(Z\)-cut, are planes
in the log coordinates for fixed \(b\):
\[
   ak=hk/d,\quad am=hn,\quad y=hnk,\quad
   d<hnk/B,\qquad dnk>N/(b^2H L^{2D_1}).
\]
The exponent test (1) is also a finite set of such
planes on each long orientation. Use the **positive**
box estimate for any cells meeting a plane.
At fixed physical \(d\), count actual \(a,n,k\);
one confined coordinate is always polynomially
long. For a plane involving \(h\), use \(a=h/d\),
which is polynomially long since \(d\ll S\) and
\(h\) is at a balanced polynomial scale.
Otherwise the plane involves \(nk\), or one of
\(n,k\) of known polynomial scale; at least one
of \(n,k\) is polynomially long because
\(nk\asymp N/h\). For each fixed pair of the
other *integer* coordinates, the confined
coordinate has log width \(O(L^{-F})\); its
integer floor is absorbed in this length.
Exact dyad axes can be imposed before meshing.
In a dyad with \(h\asymp X_1,n\asymp Y,k\asymp Z_1\)
and \(X_1 Y Z_1\asymp N\), the positive principal
boundary mass is therefore
\[
 \ll \frac{X_1 Y Z_1 L^{-F}}{\varphi(b)}
                  \sum_{d\ {\rm in\ dyad}}\frac1d.
\]
Together with the arbitrarily log-small
arithmetic errors, this pays all positive
boundary rows, including their \(\log j\log k\)
weights. For interior boxes, these weights
vary by \(O(L^{2-F})\) since \(N-y\) is central.
Use the positive estimate once more for this
replacement. All signed model boundaries
are dominated by the same positive principal.
The hard gates and true log weights are thus
restored in the reduced principal.

## 3. The literal signed principal

In the restored principal, fix \(b,d,n,k\)
with their actual units at \(bN\). The remaining
\(a=h/d\) is in a real interval for each of
the two orientations, since all conditions at
fixed \(b,d,n,k\) are linear inequalities
in \(\log a\) on an orientation.
The coefficient in \(a\) is
\(\mu(a)1_{(a,bN)=1}\), with
\(\log((N-adnk)/b)\) of supremum and variation
\(O(L)\). Unit-masked ordinary Mertens at the
polynomial scale \(X_1/d\), as in
[ConductorHalf.md](ConductorHalf.md), §3,
gives \(O_A((X_1/d)L^{-A})\) on each such interval.
The remaining sums cost \(Y Z_1\) in
coordinates, harmonic \(1/\varphi(b)\) in \(b\),
and harmonic \(1/d\) from this bound.
Hence the whole reduced principal is
arbitrarily log-small. This proves (1)'s
signed deletion at the original target.
