# A uniform-residue shoulder with the unrestricted giant quotient as source

Use the fully opened physical double remainder of [DoubleRough.md](DoubleRough.md).
Thus the prescribed even target is \(N\), \(L=\log N\),
\(S=\exp((\log L)^4)\), \(B=N/S\), \(z=\exp((\log L)^2)\),
and
\[
 x=a f g,\quad y=m c h k=N-x,\quad x\in NJ,\quad c h k\in I,
 \qquad \mu(a)\Lambda(f)\mu(c)\Lambda(h)Q_y(m)
\]
is its actual weight, with all the rough, target-unit, and
Vaughan-cutoff conditions of that note. Here
\(Q_y(m)=\sum_{d\mid m,\ d<y/B}\mu(d)\);
\(J\subset J_0\Subset(0,1)\) and
\(I\subset[\sqrt N S^2,B]\) are real intervals.

Fix dyads for \(a,f,m,c,h,k\), with exponents \(u,v,\beta\) of
the first three scales \(a,f,m\) (base \(N\)). Empty dyads are
ignored. Suppose with fixed positive reserves that
\[
 u+v>1/2,\qquad 7u+12v<4,\qquad
 u+2(u+v-1/2)<\beta<1-u.                                           \tag{1}
\]
Then the entire actual signed double contribution in this box is
\(O_A(NL^{-A})\) for every fixed \(A>0\), uniformly in the
prescribed even target and literal intervals. No small-radical
condition, primality or additional roughness of \(m\), or fixed
small integer representative of the target residue is assumed.

For example, the exponent box centered at
\[
   u=.420,\quad v=.085,\quad \beta=.460,\quad
   \log_N c=.120,\quad \log_N h=.120,\quad \log_N k=.300
\]
with a sufficiently small fixed positive width is admissible.
Its original outer products are \(a f=N^{.505+o(1)}\) and
\(m c h=N^{.700+o(1)}\) at the center, far outside both
the balanced reciprocal seam and the elementary under-hyperbola
region. The example gives a feasible exponent shape, not a lower
bound on any of these boxes.

The analytic input is [Maynard, *Primes in arithmetic progressions to
large moduli III*, Proposition 5.3](https://arxiv.org/html/2006.08250v1#S5).
The [related tagged-semiprime shoulder](../UniformResidueDoubleShoulder.md)
uses the same common-residue distribution theorem after choosing
a source group containing a suitable genuine semiprime label.
Here the actual untagged, unrestricted quotient \(m\), with its
signed short-divisor coefficient, is itself the Siegel--Walfisz
source. The extra rough label in the modulus is accounted for
without summing subpower-many error terms.

## 1. Separate the literal moving gates

Apply the physical \(y\)-mesh of [GiantReciprocalSeam.md](GiantReciprocalSeam.md)
to freeze \(T_y=y/B\) and the \(m\)-bounds from \(y/m\in I\).
For mesh width \(NL^{-F}\), a changed \(d\)-gate has
\(d\mid y\), \(d\ll S\), \(|y-Bd|\ll NL^{-F}\), and
a changed \(m\)-gate at an endpoint \(E\) of \(I\) has
\(m\mid y\), \(m\le\sqrt N\), \(|y-Em|\ll NL^{-F}\).
Counting actual multiples globally gives
\(O(NL^{1-F}+\sqrt N+S)\) exceptional integers \(y\).
Together with fixed divisor moments this pays the cut changes
and smoothing of the central cell endpoints with arbitrary log
accuracy. Thus each cell has \(Q_T(m)\) at fixed \(T\asymp S\),
a literal independent interval in \(m\), and a smooth
\(\Psi(y/N)\) with fixed derivative bounds that are log powers.

Only open the \(z\)-roughness gate on the free \(g\) by a label
\(e\mid g\) on primes at most \(z\) outside \(N\), at the
successive Bonferroni depths of DoubleRough. The positive
error occurs on actual \(e\mid x\) for a first-omitted-order
\(e\). Count these integer multiples globally before applying
any progression estimate; the factorial reciprocal tail and
Cauchy with the fixed divisor moments pay it, as in the
reciprocal seam. The label is squarefree, at most \(S^{o(1)}\),
with signed coefficient of absolute value at most one.
The actual modulus is
\[
                 q_1q_2=a(f e),\qquad q_1=a,\ q_2=f e.            \tag{2}
\]
The factor \(f\) is \(z\)-rough, so \(q_2\) recovers both
\(f\) and \(e\) **uniquely** by its \(z\)-rough and \(z\)-smooth
parts. In particular one dyad of \(q_2\), at exponent \(v+o(1)\),
carries an independent coefficient bounded by \(L\), not
\(S^{o(1)}\) choices at each modulus. Nothing is opened on
\(k\); its exact rough mask stays on the arbitrary source group.

## 2. The actual short score is Siegel--Walfisz in \(m\)

At a polynomial dyadic scale \(M\) in \(m\), put
\[
 \alpha_m=Q_T(m)1_{(m,N)=1}
\]
on the fixed allowed \(m\)-subinterval of that dyad and zero
elsewhere. For any auxiliary integer \(d_0\ge1\), modulus \(q\),
and reduced residue \(v_0\bmod q\), this coefficient satisfies
Maynard's condition (4.1), with the permitted factor
\(\tau(d_0)^{O(1)}\), uniformly in the prescribed cutoffs.

Indeed open \(d\mid m,\ d<T\). In the numerator of (4.1)
the only possible terms have \((d,qNd_0)=1\).
For each such \(d\) put \(m=d n\) and count the literal
reduced class \(n=v_0\overline d\bmod q\), with
\((n,Nd_0)=1\), in the divided interval. Let \(J_m\) denote
the original interval in \(m\). Ordinary CRT and
inclusion--exclusion give its main
\[
   \frac{|J_m|}{d q}
           \prod_{\substack{\lambda\mid Nd_0\\\lambda\nmid q}}
                         (1-1/\lambda)
\]
with floor at most \(O(\tau(N)\tau(d_0))\).
Primes dividing \(q\) already give units in the reduced
class. For the reduced mean in (4.1), with the same \(d\),
count \((n,Nd_0q)=1\) in that divided interval and divide by
\(\varphi(q)\). Its main is **identical** to the displayed
one, since \(\varphi(Nd_0q)/(Nd_0q)\) includes
\(\varphi(q)/q\). The floor there is
\(O(\tau(N)\tau(d_0)\tau(q)/\varphi(q))\).
For \(q\le L^C\) the errors after all \(d<T\) are
\(N^{o(1)}\tau(d_0)\), negligible at polynomial \(M\).
There is no requirement that \(Nd_0\) be bounded for
these elementary counts, and no use of a signed asymptotic
in the unrestricted auxiliary mask.

For larger \(q\), the absolute divisor opening bounds the
progression count by \(O(M(1+\log T)/q+T)\), and the
absolute reduced mean by \(O(M(1+\log T)/\varphi(q))\).
Taking \(C\) large for each accuracy and using
\(\varphi(q)\gg\sqrt q\) handles all such moduli.
This proves (4.1), uniformly also on every real
subinterval. Partial summation permits twisting this
coefficient by \((m/M)^{it}\) for \(|t|\le L^{C'}\);
the loss is only a fixed log power before choosing its
SW accuracy. The bound \(|\alpha_m|\le\tau(m)\) is literal.

## 3. The true residue and the signed principal term

Group the complementary source into the integer \(w=c h k\).
Its coefficient is the actual sum of \(\mu(c)\Lambda(h)\)
with all the independent Vaughan, roughness and target-unit
cuts, including the unchanged \(k\) mask. It is \(L\tau(w)^{O(1)}\);
dividing by \(L\) for the distribution input costs only one
logarithm on restoring it. On each compatible dyad its
size times the \(m\)-scale is \(\asymp N\), by the central
condition. The same holds after the ordinary product dyads.
Separate \(\Psi(m w/N)\) by Mellin inversion on the fixed
compact positive central range. The transform has log-power
\(L^1\)-norm and may be truncated to \(|t|\le L^{C'}\) with
arbitrary log accuracy by rapid decay. The physical divisor
bound and reciprocal divisor sums in the model pay the
truncation. Each resulting \(m\)-twist obeys §2; the other
twist is on the arbitrary complementary group.

In Maynard's Proposition 5.3 use \(q_1=a\) at exponent \(u\),
\(q_2=f e\) at exponent \(v+o(1)\), and the SW length of \(m\)
at exponent \(\beta\). Its assumptions are
\(Q_1Q_2=N^{1/2+\delta'}\),
\(Q_1^7Q_2^{12}<N^{4-10\epsilon'}\), and
\(N^{2\delta'+\epsilon'}Q_1<M<N^{1-\epsilon'}/Q_1\).
The fixed reserves in (1) imply them for a small fixed
\(\epsilon'>0\), since \(\delta'=u+v-1/2+o(1)\).
In the supremum over a common residue mod \(q_1\) choose
\(N\bmod q_1\); for each \(q_2\) choose the actual
\(N\bmod q_1q_2\). Both are reduced by the original target-unit
mask. No coprimality of \(a,f\) is needed by the theorem:
the modulus is the actual product (2).
The modulus multiplicities and coefficients cost only log
powers by their unique recovery in §1, \(|\mu(a)|\le1\),
and \(\Lambda(f)\le L\). This proves the total discrepancy
is \(O_A(NL^{-A})\) with the prescribed real weight.

It remains to remove the *actual principal*, not just
the centered difference. Reassemble any real Mellin
separation and fix \(y=m w\) and \(f,e\). The remaining
sum is the true \(a\)-interval of
\(\mu(a)/\varphi(a f e)\), with \(a\) \(z\)-rough and
\((a,Ny)=1\). The coprimality of \(f,e\) with \(Ny\)
is tested separately. The factor \(e\) is smooth, and
\(f=\lambda^j\) whenever \(\Lambda(f)\ne0\).
Thus for all retained \(a\)
\[
 \frac{\varphi(a)\varphi(f)\varphi(e)}{\varphi(a f e)}
     =1-\lambda^{-1}1_{\lambda\mid a}.
\]
The \(a\)-sum is therefore a linear combination of two
rough coprime \(\mu(a)/\varphi(a)\) sums, with masks
\(Ny\) and \(Ny\lambda\), divided by
\(\varphi(f)\varphi(e)\).

These sums are \(O_A(L^{-A})\) uniformly.
For a polynomial \(a\)-interval the proof of the
rough harmonic in DoubleRough applies to the coefficients
\(a\mu(a)/\varphi(a)\): after dividing out \(\zeta(s)^{-1}\),
the formerly unexcluded local parameters \(1\)
are replaced by \(\lambda/(\lambda-1)=1+O(1/\lambda)\),
whose extra absolute Euler product converges uniformly
at \(1-1/\log z>.9\). The excluded primes have exactly
the same reciprocal factors as there. The finite cutoffs
in \(a\) preserve its interval; \(a>D=N^{1/200}\) supplies
more than the needed lower limit. The \(f,e\) sums retain
their actual reciprocal \(\varphi\)-weights and cost only
log powers, and the physical \(y\)-coefficients have
\(\sum_{y\le N}L^C\tau(y)^C\ll N L^{C'}\) absolute mass.
Thus the principal also vanishes at the stated accuracy.

The proof prices the indicated actual product boxes, including
imbalanced supercritical ones. It does not give a result when
the factored modulus or the unrestricted \(m\)-source fail
(1), nor a sign for the complete double remainder.
