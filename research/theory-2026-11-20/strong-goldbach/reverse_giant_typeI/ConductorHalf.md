# Deleting the opposite divisor through every fixed sub-root level

Use [the direct double-Möbius switch](SecondTypeI.md) and its
notation \(Q,Z,S,B,J,I,L\) and \(\mathcal D_I\). Thus \(N\) is
prescribed even, \(I\subset[N^{1/2+\varepsilon},B]\) for fixed
\(\varepsilon>0\), and the actual positive integers satisfy
\[
 bj+amk=N,\quad bj\in NJ,\quad (amk,N)=1,\quad
 ak\in I,\quad am>Q,\quad b>Z(N/(mk)).
\]
Their weight is \(\mu(a)\mu(b)\log j\log k\,Q_{amk}(m)\).

**Theorem.** For any fixed \(\delta>0\), the restriction of
\(\mathcal D_I\) to \(b\le N^{1/2-\delta}\) is
\(O_{A,\varepsilon,\delta,J_0}(NL^{-A})\) for every fixed \(A>0\).
Thus \(C_I\) can be written using only \(b>N^{1/2-\delta}\)
in its direct double-signed remainder. This is an all-target
signed deletion, not an absolute bound or a sign for the
surviving sum. The constants depend on \(\delta\); no
log-thin collar at \(b=\sqrt N\) is claimed.

Unlike [the free-coordinate counts](IntegerRectangles.md),
this argument averages the opposite modulus \(b\).
Ordinary Möbius BV is used only for small inducing conductors
of the actual characters, not for the larger original modulus.

## 1. A three-coordinate box estimate

Fix \(0<\kappa<\delta\). Let \(b\asymp R\) be a modulus dyad,
restrict to \((b,N)=1\), and allow any subcollection of its moduli.
Let \(J_u,J_v,J_w\) be fixed intervals of positive integers each
contained in a fixed-ratio dyad at scale \(X,Y,Z_0\), respectively,
with all scales at least 1 and at most \(N^{O(1)}\).
For each \(b\) let \(c_b\) be any reduced class. Set
\[
 C_b=\sum_{\substack{(u,v,w)\in J_u\times J_v\times J_w\\
                       uvw\equiv c_b\bmod b}}
            \alpha(u)\,1_{(v,N)=1}\,1_{(w,N)=1},
 \qquad \alpha(u)=\mu(u)1_{(u,N)=1}.
\]
Its exact character principal is
\[
 P_b=\frac1{\varphi(b)}
   \sum_{u\in J_u,\,(u,b)=1}\alpha(u)
   \sum_{v\in J_v,\,(v,bN)=1}1
   \sum_{w\in J_w,\,(w,bN)=1}1.
                                                                  \tag{1}
\]
We show
\[
 \sum_{b\asymp R}|C_b-P_b|
 \ll_{D,\kappa} XYZ_0 L^{-D}
             +N^{\kappa/2+o(1)} R\sqrt{XYZ_0}.
                                                                  \tag{2}
\]
The positive version, taking \(\alpha=1\) and dropping the
target-unit masks on \(v,w\), also satisfies (2). The congruence
still imposes units modulo \(b\), and (1) is adjusted accordingly.

By [Cochrane–Shi, Theorem 1](https://www.math.ksu.edu/~cochrane/research/xyequvmodm.pdf)
the nonprincipal fourth moment, normalized by \(1/\varphi(b)\),
of a character sum on an arbitrary shifted interval of length
\(Y\) is \(\ll 8^{\omega(b)}\tau(b)(\log(2b))^{O(1)}(Y+1)^2\),
for arbitrary composite as well as prime \(b\). The actual
target-unit mask on \(v\) is inserted by
\[
 \sum_{v\in J_v,\,(v,N)=1}\chi(v)=
 \sum_{\substack{e\mid N\\(e,b)=1}}\mu(e)\chi(e)
        \sum_{v'\in J_v/e}\chi(v').
\]
Minkowski in the fourth norm costs at most \(\tau(N)=N^{o(1)}\);
this loss is used only in a term with fixed power reserve.
The same applies to \(w\). Thus, denoting the true sums by
\(V_b(\chi),W_b(\chi)\), Cauchy in the fourth moments gives
\[
 \sum_{b\asymp R}\frac1{\varphi(b)}
   \sum_{\chi\ne\chi_0}|V_b(\chi)W_b(\chi)|^2
             \ll N^{o(1)} RYZ_0 .
                                                                  \tag{3}
\]

Write \(U_b(\chi)=\sum_{u\in J_u}\alpha(u)\chi(u)\).
For \(X/R\le N^\kappa\), character orthogonality and the
maximum of \(O(1+X/b)\) integers per class give
\(\varphi(b)^{-1}\sum_\chi |U_b(\chi)|^2\ll X(1+X/b)\).
This and (3) give the second term of (2).
Otherwise put \(R_0=X/(R N^\kappa)>1\).

For a character induced from a primitive character \(\chi^*\)
of conductor \(q\mid b\), put \(r=b/q\). On all integers
\(\chi(u)=\chi^*(u)1_{(u,b)=1}\). Open the unit mask
at the primes of \(b\) outside \(q\):
\[
 U_b(\chi)=
 \sum_{\substack{t\mid r\\(t,q)=1}}\mu(t)\chi^*(t)
      \sum_{u'\in J_u/t}\alpha(tu')\chi^*(u').
\]
This also holds when \(q,r\) share primes, since \(\chi^*\)
enforces the unit mask at \(q\) itself. Cauchy in \(t\) loses
at most \(N^{o(1)}\). For fixed \(r,t\) the coefficient
\(\alpha(tu')\) is independent of \(q\); its squared norm
is \(O(X/t)\), interpreting terms with \(t\) larger than
the upper endpoint of \(J_u\) as empty. Use
[the primitive multiplicative large sieve, Montgomery–Vaughan, Theorem 19.16](https://personal.science.psu.edu/rcv4/571s25/montgomery-vaughanII.pdf)
at level \(q\le 2R/r\), with \(1/\varphi(b)\ll L^{O(1)}/R\):
\[
\begin{split}
 \sum_{b\asymp R}\frac1{\varphi(b)}
       \sum_{\operatorname{cond}\chi>R_0}|U_b(\chi)|^2
 &\ll N^{o(1)}\!
    \sum_{r\le 2R/R_0}\sum_{t\mid r}
       \left(\frac{XR}{r^2t}+\frac{X^2}{Rt^2}\right)\\
 &\ll N^{o(1)}(XR+X^2/R_0)
  \ll N^{\kappa+o(1)} XR .
\end{split}                                                       \tag{4}
\]
The first divisor sum is convergent after division by \(r^2\),
and \(\sum_{r\le V}\sum_{t\mid r}t^{-2}\ll V\).
If \(R_0>2R\) the left side is empty. Cauchy with (3)
proves the large-conductor contribution to (2).

## 2. Small induced conductors

For \(b\) fixed, \(1<q\le R_0\) dividing \(b\), and \(v,w\)
units modulo \(b\), let \(c=c_b\overline{vw}\bmod b\).
Primitive orthogonality, on actual units, gives
\[
 \sum_{\chi^*\ {\rm prim.}\pmod q}
   \overline{\chi^*(c)}
      \sum_{u\in J_u,\,(u,b)=1}\alpha(u)\chi^*(u)
 =
 \sum_{l\mid q}\mu(q/l)\varphi(l)
      \sum_{\substack{u\in J_u,\,(u,b)=1\\u\equiv c\bmod l}}
        \alpha(u).
                                                                  \tag{5}
\]
Open \((u,b)=1\) by \(t\mid b\). Only \((t,l)=1\)
contributes. With \(u=tu'\) the residue \(c\overline t\bmod l\)
is genuinely reduced. For squarefree \(t\), the coefficient
\(\alpha(tu')\) is \(\mu(t)\mu(u')1_{(u',Nt)=1}\),
since \(t\) is a target unit. The outside coefficient
\(\mu(t)\) of the coprime opening causes no difficulty.

For fixed coprime \(l,t\), the sum over possible \(b\)'s and
\(q\)'s of \(\varphi(l)/\varphi(b)\) is at most
\[
 \sum_{\substack{b\asymp R\\lt\mid b}}
       \frac{\varphi(l)\tau(b)}{\varphi(b)}
    \ll \frac{L^{O(1)}\tau(lt)^{O(1)}}{t}.
                                                                  \tag{6}
\]
Indeed put \(b=lt s\), use \(\tau(lt s)\le\tau(lt)\tau(s)\)
and the ordinary divisor harmonic on \(s\). This positive
majorant applies with arbitrary bounded outside \(b\)-weights
and arbitrary reduced classes in (5). The  \(v,w\) counts
are bounded absolutely by \(O(YZ_0)\).

At fixed \(t\), the actual scale is \(X/t\) and the
unit mask is \(Nt\le N^{O(1)}\). Since \(lt\le 2R\),
\[
 X/t\gg X/R>N^\kappa,\qquad
 l^2t\le 2R R_0=2X N^{-\kappa}.
                                                                  \tag{7}
\]
Apply ordinary maximal unit-masked Möbius BV from
[SecondTypeI.md](SecondTypeI.md), §1, at length \(O(X/t)\)
to \(l\le\min(R_0,2R/t)\). Its proof applies with fixed mask
\(Nt\) in place of \(N\), since it only uses the bound
\(\log(Nt)=O(L)\) and moduli coprime to this mask.
For a weight \(\tau(l)^C\), use Cauchy in the nonnegative
discrepancy \(\Delta_l\) as measure, with trivial
\(\Delta_l\ll X/(tl)+1\) for the extra divisor moment.
This gives \(O_D((X/t)L^{-D})\) with the weight too.
Equations (5)–(7) and \(\sum_t\tau(t)^{O(1)}/t^2<\infty\)
give \(O_D(XYZ_0L^{-D})\) for the small conductors.

For the positive version \(\alpha=1\), use elementary
progression floors instead. In the \(t\)-opening, the
continuous term for the class \(u\equiv c\bmod l\),
multiplied by \(\varphi(l)\), is
\[
  |J_u|\,\frac{\varphi(l)}l
      \sum_{\substack{t\mid b\\(t,l)=1}}\frac{\mu(t)}t
       = |J_u|\,\frac{\varphi(b)}b.
\]
This is independent of \(l\), so it cancels in (5) for
each \(q>1\). Each remaining floor is \(O(1)\).
Using (6), the positive low-conductor error is at most
\(YZ_0 R_0 L^{O(1)}\ll XYZ_0 L^{-D}\) by the definition
of \(R_0\). The principal (1) remains an exact integer
count in this version. This finishes (2).

## 3. Literal gates and principal

Use dyads \(a\asymp X,b\asymp R,m\asymp M,k\asymp K\)
with \(XMK\asymp N\) on nonempty packets and
\(R\ll N^{1/2-\delta}\). Open \(d\mid m\) in \(Q_y(m)\)
and put \((u,v,w)=(a,m/d,k)\) in (2). Only \(d\ll S\)
occur, and \((d,N)=1\). The literal class is
\(avk\equiv N\overline d\bmod b\), with no row when
\((d,b)>1\). All three factors are then units modulo \(b\).
Once they are target units, \(j=(N-amk)/b\) is
automatically a target unit too; there is no separate local
factor for \(j\).

For a nonempty dyad, \(M\gg S\) since \(ak\le B\).
Also \(X\gg N^\varepsilon/L^D\) from \(am>Q\) and
\(ak\ge N^{1/2+\varepsilon}\), with \(D\) the constant in
\(Q\). The actual \(b>Z(N/(mk))\) implies
\(MK\gg N^{2\delta}/(H L^{2D_1})\). Thus at least
one of \(M/d,K\) is polynomially long uniformly in \(d\).

Take a *fixed* log mesh of step \(\asymp 1/J_1\) on
\(a,m,k\), \(J_1=L^F\) for large fixed \(F\).
At each \(d\) this gives literal intervals on \(a,v,k\)
independent of \(b\), with \(O(J_1^3)\) boxes.
At fixed \(b,d\), the relevant contours are planes in
log coordinates: \(am>Q,\ ak\in I\), centrality of \(amk\),
and
\[
 mk>N/(b^2HL^{2D_1}),\qquad amk>Bd,
\]
which are precisely the \(Z\) and short-divisor gates.
The axes, including dyad endpoints, retain their literal
integer convention. A given box can be accepted for an
arbitrary subset of \(b\)'s; (2) bounds absolute errors
across all such subsets. There is no row-dependent
replacement of a character-sum interval.

For each \(d\), apply (2) with \(Y=M/d+1,\ Z_0=K+1\).
The first term summed over \(d\) and boxes is
\(O_D(NL^{-D+O(F+1)})\), since
\(\sum_{d\ll S}(M/d+1)\ll M\log(2S)\).
The second is \(N^{1-\delta+\kappa/2+o(1)}\), allowing
even \(S=N^{o(1)}\) separate \(d\)'s. Bounded box weights
of size \(O(L^2)\), and the log-power number of dyads,
are paid by fixed reserves.

For boundary cells use the **positive** box estimate,
dropping all \(N\)-unit tests, but keeping the unit
congruence at \(b\). This pays their true arithmetic
errors as just described. The corresponding principal
from the exact integer counts (1) has total, for fixed
\(b,d\), at most
\[
 \frac1{\varphi(b)}
    O\!\left(\frac{X(M/d+1)(K+1)}{J_1}\right).
                                                                  \tag{8}
\]
Indeed the union of boundary cells lies in a log strip
of width \(O(J_1^{-1})\) about a plane. Fix the other two
*integer* coordinates and count the confined coordinate.
Use the polynomially long \(a\) for each plane involving
\(a\), and either \(m/d\) or \(k\), whichever is
polynomially long, for the plane in \(mk\). A single floor
is absorbed by that coordinate's length divided by \(J_1\).
This does not approximate a short coordinate by its length.
Summing (8) over \(b,d\) costs only log powers, handled by
the choice of \(F\). The same principal upper applies
to the absolute signed model on the boundary.

On interior cells, \(\log k\log j\), with \(j=(N-amk)/b\),
varies by \(O(L^2/J_1)\) by centrality. Apply the positive
estimate to that replacement as well. We may therefore
restore the exact real cutoffs and exact log weights in the
principal, with arbitrarily log-small total error.
This argument for edges uses no Möbius cancellation on
positive actual boundary rows.

In the restored principal fix \(b,d,m,k\) with their
actual units and \(d\mid m\). Its \(a\)-weight is
\(\mu(a)1_{(a,bN)=1}\). All actual conditions on \(a\)
now form a real interval and \(\log((N-amk)/b)\)
has supremum plus variation \(O(L)\).
Uniform ordinary Mertens with coprime mask \(bN\)
bounds this signed sum by \(O_D(XL^{-D})\). For example
use the convolution and Rankin Euler estimate of
[SecondTypeI.md](SecondTypeI.md), §1: split the
convolution at \(\sqrt X\), apply classical Mertens to
its first part and Rankin to the other, using
\(X\ge N^{\varepsilon/2}\). Thus all endpoints are uniform.
The absolute remaining principal harmonic is at most
\(\sum_{b\asymp R}1/\varphi(b)\cdot K\sum_{d\ll S}(M/d+1)\)
times a fixed log power. This proves the theorem, without
a sign claim for \(b\) at or above the root.
