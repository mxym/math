# Full one-mark transfer without a quotient or near-root restriction

Use the notation of
[WholeSuperrootPrimeTransfer](WholeSuperrootPrimeTransfer.md):
\(N\) is an individual even target, \(J\Subset(0,1)\) is fixed
and nondegenerate, \(x\in NJ\), \(y=N-x\), \(L=\log N\), and
\(M_N=|J|N\mathfrak S(N)\). All physical \(x,y\) are target units.
Use the same real smooth right profile \(G\) supported in \([0,b]\)
with fixed \(b,\lambda>0,\ b+\lambda<1/2\) and \(U=N^\lambda\).
Write \(A_G,P_G,\Pi\) and \(a_G=G(0)-(1-\lambda)G'(0)\) as
in that proof.

For a fixed compactly supported, smooth real \(F\) on
\([0,\infty)\), a fixed \(\rho>0\), and a genuine mark window
\(\mathcal R\subset(N^\rho,N]\), put
\[
 B_F(x)=\sum_{\substack{x=r m,\ m>1\\
                   r\ {\rm prime},\ r\in\mathcal R}}
       (\log r) Q_F(m;x),
 \qquad
 Q_F(m;x)=\sum_{d\mid m}\mu(d)F\!\left(\frac{\log(dN/x)}L\right).
\]
When \(\rho\le1/2\) multiple actual marks on a row are kept
with their stated weights, not deduplicated. In any case
there are at most \(1/\rho+1\) marks on a given \(x\).

**Theorem.** At every sufficiently large even target, uniformly
in the actual endpoints of \(\mathcal R\),
\[
 \sum_{\substack{x\in NJ\\(x,N)=1}}B_F(x)P_G(y)
   = a_G\mathfrak S(N)\sum_{\substack{x\in NJ\\(x,N)=1}}B_F(x)
        -G(0)\sum_{\substack{x\in NJ\\(x,N)=1}}B_F(x)\Pi(y)
        +o_{F,G,J,\rho,\lambda}(M_N).                         \tag{1}
\]
In particular **no** condition \(\rho+\lambda>1\), \(\rho>1/2\),
least-factor floor, or radical restriction is required.
The earlier \(.510/.498\) scope sufficed for the positive
joint two-affine envelope; the present proof does not use
such an upper on the two-composite correlation. This permits
simultaneously wide fixed profiles with a small lower mark
gate. It does not evaluate the remaining true prime cross.

More precisely the intermediate signed expectation is
\[
 \sum_{\substack{x\in NJ\\(x,N)=1}}B_F(x)A_G(y)
   =a_G\sum_{\substack{x\in NJ\\(x,N)=1}}
                  B_F(x)\mathfrak S(Nx)+o(M_N).              \tag{2}
\]
Keeping the exact mask \(Nx\) rather than trying to remove
each common residue at the outset is useful in the tiny-factor
part of the score.

## 1. Actual product distribution on the full quotient

We need the weighted product distribution of
\(\alpha(r)\beta(m)\), where
\(\alpha(r)=(\log r)1_{r\in\mathcal R,\ r\ {\rm prime},\ (r,N)=1}\)
and \(|\beta(m)|\ll\tau(m)^C\) has \(m>1,\ (m,N)=1\).
Use a fixed power accuracy in \(q\le Q=N^{\lambda+b}\):
the error is \(O_A(NL^{-A})\) in the weighted sum over
\((q,N)=1\) at the literal residue \(N\), with any fixed
modulus divisor power. The principal is divided by
\(\varphi(q)\), and its source sum retains \((rm,q)=1\).
The same allowed spatial tests, log powers and fixed
central interval extensions as in §1 of the earlier proof
are valid.

Choose
\(0<\eta<\min(\rho,1-2(\lambda+b))/4\).
For **small actual \(m\le N^\eta\)** fix \(m\).
If \((m,q)>1\), both the congruence and its reduced
principal vanish. Otherwise the genuine prime \(r\)
lies in the reduced residue \(N\overline m\bmod q\),
and the scale is \(Y=N/m\).
The modulus ceiling \(Q\) is below \(Y^{1/2-c}\)
for a fixed \(c>0\). Use genuine maximal-prefix ordinary
Bombieri--Vinogradov at this scale; actual \(r\)-window
endpoints and the smooth spatial weight are handled by
subtraction and ordinary partial summation. To allow any
fixed divisor weighting, interpolate the usual absolute
error sum with the upper
\(\sum_{q\le Q}\tau(q)^{2C}|E_q|\ll YL^{O_C(1)}\).
This follows from the crude residue estimate
\(|E_q|\ll YL^{O(1)}/q\), since \(q<Y\);
the analogous reduced principal bound uses
\(1/\varphi(q)\ll L^{O(1)}/q\).
The difference in the principal between the true reduced
prime mass and its length is allowed by the ordinary PNT
and removal of the \(O(L)\) target or modulus prime factors.
Taking the PNT and BV accuracies sufficiently large,
the error is \(O_A(YL^{-A})\), and summation over
\(|\beta(m)|/m\) costs only fixed log powers.
A fixed Mellin phase of log-power height is likewise
possible by partial summation; it is not necessary for
separability in this fixed-\(m\) step.

For **large actual \(m>N^\eta\)** use the character proof in
[WholeSuperrootPrimeTransfer, §1](WholeSuperrootPrimeTransfer.md)
on genuine dyads \(r\asymp R,\ m\asymp B,\ RB\asymp_J N\).
The independent intervals are close enough in fixed ratio
that all products entering the spatial reconstruction
stay in a fixed compact subinterval of \((0,N)\).
We have \(N^\rho\ll R\ll N^{1-\eta}\) and
\(N^\eta\ll B\ll N^{1-\rho}\). Least-factor roughness
was not used anywhere in the primitive character estimate
on this branch. The estimates for the terms with the
primitive \(\chi\) in the \(r\)-slot are unchanged, except
that there may be an imprimitive correction to that slot
when \(r\le Q\). We give its full bound next.

An inducing conductor \(k\mid q\) always has
\((k,r)=1\) on a contributing correction, since otherwise
\(\chi(r)=0\) already. In removing \(m\)-nonunits as before,
write \(m=gw\) with \(g\mid q,\ (g,k)=1\).
The extra excluded \(r\) is an **actual prime factor of \(q\)**.
For fixed \(r,g,k\), the modulus therefore is a multiple of
\(k[r,g]\). Grouping the weighted inverse totient over
these moduli costs a log power times
\[
       \frac{\tau(k)^C\tau([r,g])^C}
            {\varphi(k)\varphi([r,g])}.
\]
The true \(r\)-factor has weight \(\log r\), and the
phase \(\chi(r)r^{it}\) has modulus at most one.
On each conductor dyad \(k\asymp K\) bound the single
remaining \(w\)-slot by the primitive large sieve and
Cauchy. With the primitive weight \(k/\varphi(k)\),
the count of characters in that dyad is \(O(K^2)\);
the factor \(1/k\) in \(1/\varphi(k)\) cancels its square
root. The correction after summing over the characters,
apart from \(\tau(g)^{O(1)}L^{O(1)}\), is at most
\[
     K^\epsilon\sqrt{B/g}\sqrt{B/g+K^2}
       \ll K^\epsilon\bigl(B/g+K\sqrt{B/g}\bigr).             \tag{3}
\]
Here \(\tau(k)^C\ll_\epsilon K^\epsilon\), with small
fixed \(\epsilon>0\). The \(w\)-support has length
\(O(B/g)\), allowing an absolute factor when its upper
length is comparable to 1, and \(g>2B\) is absent.
This works even for small \(K\); no new SW is needed.

To sum \(g\), split squarefree \(g\) (as in the original
imprimitive opening) into \(r\nmid g\) and \(g=r g'\).
In the first case \(\varphi([r,g])=(r-1)\varphi(g)\);
in the second it is \((r-1)\varphi(g')\).
The extra factor \(\tau(g)\) in the shortened sequence norm
is at most a fixed constant times \(\tau(g')\) in the second
case, and \(1/\sqrt g\le1/\sqrt{g'}\).
Thus in both cases the residual \(g\)-sums are convergent
with \(\tau(g')^{O(1)}/(\varphi(g')\sqrt{g'})\).
The \(r\)-log harmonic on its dyad is \(O(1)\) after the
factor \(1/(r-1)\). With \(K\le Q<N^{1/2}\) and
\(B\ll N^{1-\rho}\), both \(B\) and \(K\sqrt B\) in (3)
save a fixed power, even after \(K^\epsilon\).
This deals with exactly the difference between the
induced and primitive \(r\)-slots; the principal remains
the true reduced principal throughout.

The spatial reconstruction is the same common smooth
Mellin reconstruction as in the earlier §1, at fixed
height \(L^T\) before any wider tail: absolute sums over
true congruences have the crossed divisor envelope from
\(q\mid N-rm\), and on the reduced principal the extra
harmonic is \(1/\varphi(q)\). Multiple \(r\)-marks only
add a fixed divisor factor. Thus the enlarged mollified
cells and the arbitrary-log cutoff give the literal
fixed central window with all spatial tests included.
This proves the asserted product distribution.

## 2. Retain the full local factor and reassemble the source

Open the right \(A_G(y)\) using its exact moduli \(d\)
and \(dk\), for a prime power \(k\le U\) in the second
term. At every genuine pair \(x,y\) these products
are target units. After §1 the reduced principal
additionally keeps \((x,d k)=1\); this is exactly the
mask \(H=Nx\) in the one-variable short harmonic.
There is no restriction on \((d,k)\) itself.
Use \(Q_F(m;x)\)'s Fourier decomposition as before:
\[
 Q_F(m;x)={1\over2\pi}\int_{\mathbb R}\widehat F(\xi)
          e^{i\xi\log(N/x)/L}\sum_{d\mid m}\mu(d)d^{i\xi/L}
          \,d\xi .
\]
Here the coefficient in \(m\) is divisor-bounded uniformly
in \(\xi\). A smooth compact extension of \(F\) is used;
\(|\xi|\le L\) has permitted spatial seminorms and the
Schwartz tail is arbitrarily log-small against the
true and reduced positive divisor envelopes.
In the principal reassemble this **entire** Fourier
integral and the true \(r,m\)-support before estimating
the signed short-\(\mu\) model error.

At each fixed actual \(x\), apply the pointwise harmonic
calibration (3) of
[WholeSuperrootPrimeTransfer, §2](WholeSuperrootPrimeTransfer.md)
with target mask \(H=Nx\) in place of \(N\).
The argument only used that the even mask is
polynomial-sized and that the spatial \(y\)
is central relative to the scale \(N\).
For clarity the two ingredients are
\[
 \sum_{(d,H)=1}\frac{\mu(d)}{\varphi(d)}=0,\qquad
 \sum_{(d,H)=1}\frac{\mu(d)\log d}{\varphi(d)}=-\mathfrak S(H)
\]
with arbitrary-log approximation at
\(S=\exp((\log L)^4)\), and the prime-power bracket
\(\lambda L+O(\log L)\), minus its actual corrections at
\(p\mid d\). The factor from target omissions is bounded
by \(O(\log L)\) since \(H\le N^2\); when removing
\(p\mid d\) from the constant moment, use \(d=p d'\)
with \(p\le\sqrt S\), and otherwise the absolute
prime-power factor \(O(\log p/p^2)\).
The same estimates give \(a_G\mathfrak S(H)+o(1)\)
uniformly in actual \(x,y\). Keeping the exact model
means no small prime of \(x\), including a prime
shared by \(r\) and \(m\), has been dropped.

The genuine absolute source harmonic weighted by \(c(m)\)
is \(O_F(N)\). Indeed at fixed \(m\) the true
\(\sum_{r\le N/m}\log r\) is \(O(N/m)\), and the Fourier
absolute divisor sum gives
\[
 \sum_{m\le N}\frac{c(m)}m
        \prod_{p\mid m}|1-e^{i\xi\log p/L}|
          \ll (2+|\xi|)^C .
\]
This is the positive Euler estimate of the earlier §3,
including all powers of \(p\). Since the actual \(r>N^\rho\),
\(c(x)=c(rm)\le c(r)c(m)\ll c(m)\), with no separate factor
for a repeated prime necessary. Hence both the full
model's \(o(1)\) error and the local factor \(\mathfrak S(Nx)\)
are summable against the genuine \(B_F\). This proves (2).

On target units and even \(N\),
\[
   \mathfrak S(Nx)/\mathfrak S(N)=c(x)
     =\prod_{\substack{p\mid x\\p>2}}(p-1)/(p-2).
\]
If all factors of \(m\) exceed \(N^\theta\) for fixed
\(\theta>0\), then \(c(x)=1+O_{\theta,\rho}(N^{-\min(\theta,\rho)})\),
since the total number of physical factors is bounded.
If some \(p\mid m\) is \(\le N^\theta\), mark such a prime
inside the same unconditioned positive Euler sum. This
costs a factor \(O(\theta|\xi|)\) from
\(\sum_{p\le N^\theta}(\log p)/p\ll\theta L\).
After Fourier integration the absolute weighted genuine
source on this set is \(O_F(\theta N)\).
Let \(N\to\infty\) first and then \(\theta\downarrow0\).
We may consequently replace the factor \(c(x)\) by 1 in
(2) at cost \(o(M_N)\), **without** a genuine joint
sieve between the two composite legs.

Finally revert \(A_G=P_G+G(t_1(y))\Pi(y)\) up to the actual
proper-power marks \(p^j>U,\ j\ge2\), as before:
their full crossed divisor-weighted loss is power-small.
For the genuine prime opponent alone at fixed \(m\),
sieve the two affine forms \(r,N-mr\) at a small fixed
power of their parameter length \(N/m\ge N^\rho\).
The two true log weights yield \(O_{\rho,J}(M_N c(m)/m)\),
and the same Fourier Euler sum gives
\(\sum|B_F(x)|\Pi(y)\ll_{F,\rho,J}M_N\).
Thus \(G(t_1(y))=G(0)+O_J(1/L)\) is harmless on the
actual prime cross. This completes (1).

## 3. An exact affine example and the remaining sign

One use of the removed cutoff restriction is to permit
a wide profile on **both** legs. As an illustration choose
\(a=.486,\ b=.490,\ \lambda=.006,\ \rho=.518\)
and take the same smooth profile \(F=G\) supported in
\([0,b]\) and exactly \(1+t/(1-\lambda)\) on \([0,a]\).
Thus \(F(0)=1,\ a_F=0\).
For a genuine high mark \(r>N^\rho\) and \(x=r m,\ m>1\),
every actual divisor satisfies
\(t_d(x)\le\log(N/r)/L<1-\rho<a\).
The exact identity
\(\sum_{d\mid m}\mu(d)\log d=-\Lambda(m)\) gives
\[
        Q_F(m;x)=-\frac{\Lambda(m)}{(1-\lambda)L}.
\]
So the whole true high orientation \(H_F=B_F\) is nonpositive,
and it equals a genuine negative semiprime weight up to
proper powers of \(m\). The latter cost \(o(M_N)\) on the
true prime cross by the fixed-\(m\) two-affine sieve and
\(\sum_{p^j,\ j\ge2}(\log p)c(p)/p^j<\infty\), with the
factor \(1/L\). They also cost \(o(M_N)\) on the same
both-high product by the literal two-affine sieve at fixed
\(m,n\), since \(mn\le N^{2-2\rho}\) and so its parameter
has fixed power length. In the latter application use
\(\sum_{n\le N}c(n)\Lambda(n)/n\ll L\).

In particular the both-high joint sector is nonnegative
term by term for this actual wide score (even before
removing proper powers), whereas by (1) each high-to-full
orientation is the corresponding **positive** true
semiprime-versus-prime statistic up to \(o(M_N)\).
In the central windows \(J\subset[1/2,2/3]\) under
\(R_J(N)=0\), the \(.252\) rough lower and \(3.446\)
actual angular upper of the earlier §4 give a strictly
positive genuine anchored part if one trims the smaller
semiprime factor at \(N^{.481}\): indeed
\(3.446\log(519/481)<.263\), leaving more than
\((.3001-.263)M_N\).
Then \(r=x/m\gg_J N^{.519}\), so the same high mark
contains these real rows, and its weight relative to
\(\log x\) stays bounded below by a positive fixed number.
This illustration applies to the **same profile** on both legs,
unlike the good one-wide/one-short rails of the earlier transfer.

However the full joint covariance for this profile is
\(R_J(N)+o(M_N)\) by
[the joint derivative formula](JointGiantEndpointDerivative.md).
Consequently the positive high-to-full orientation
requires a compensating signed term if the target has
no binary representation. The both-high sign does not
pay that term; for such wide profiles the low-low block
has not been evaluated by the short-profile reciprocal
theorems. There is no unconditional bound on that block
or binary conclusion here.
