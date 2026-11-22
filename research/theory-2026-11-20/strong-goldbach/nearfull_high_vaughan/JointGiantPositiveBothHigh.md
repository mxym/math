# A positive, polynomially rough subset of the actual both-high block

Fix a nondegenerate central interval \(J\Subset(0,1)\)
and real exponents \(\rho,\delta>0\) satisfying
\[
      \rho>1/2,\qquad
      \log\!\left(\frac{1-\delta}{\rho}\right)>1/2.
      \tag{1}
\]
For example \((\rho,\delta)=(.518,.02)\) and
\((.55,.07)\) are allowed. Let \(N\) be any sufficiently
large even integer, \(x\in NJ\), \(y=N-x\), and
\(M_N=|J|N\mathfrak S(N)\). Let \(b>0\) be sufficiently
small and fixed after \(\rho,\delta\); write \(z=N^b\).

**Theorem.** There are
\[
                   \gg_{J,\rho,\delta} \frac{M_N}{b^2(\log N)^2}
                   \tag{2}
\]
distinct ordered actual pairs \(x+y=N\) in \(NJ\) such that
both coordinates are squarefree target units, and
\[
 \begin{gathered}
       x=r m,\qquad y=s n,\qquad r,s\text{ distinct primes},\\
       N^\rho<r,s<N^{1-\delta},\qquad
       m,n>N^\delta,\qquad P^-(m),P^-(n)>z .
 \end{gathered}                                                    \tag{3}
\]
The constants in (2) do not depend on the target or \(b\),
provided \(b\) is below a sufficiently small fixed
threshold depending on \(\rho,\delta\). The threshold on
\(N\) may depend on \(b\). The actual rank of each coordinate
is bounded by \(1+(1-\rho)/b\).

In the flat-profile setting of
[the both-high reduction](JointGiantBothHighReduction.md)
with \(F(0)=G(0)=1\) and supports contained in \([0,b]\),
the case \(\rho=.518\) lies in the literal \(H_F H_G\)
sum and gives a positive subset of weighted size
\(\gg_{J,\rho,\delta} M_N/b^2\).
The \((.55,.07)\) example even stays outside the balanced
prime-inverse and asymmetric near-root rails on both
arms simultaneously. No lower bound for the **signed**
total or for the part of the same block outside this
subset is asserted. In particular (3) does not force an
exact semiprime on either arm.

## 1. The shared bilateral ambient set

Define
\[
 V(z)=\prod_{p\le z}(1-1/p),\qquad
 V_N(z)=\prod_{\substack{p\le z\\p\nmid N}}(1-1/(p-1)),\qquad
 B_0=|J|N V(z)V_N(z).
\]
On the integer line \(x+y=N\) let
\[
 \mathcal B=\{x\in NJ:(x,N)=1,\ P^-(x)>z,\ P^-(y)>z\}.
\]
Sifting the two actual affine forms \(x,N-x\) gives
one excluded root modulo \(p\) for \(p\mid N\) and two
otherwise. At \(p=2\) there is exactly one. Thus the
ordinary sieve local factor is exactly \(V(z)V_N(z)\):
at \(p\nmid N\),
\((1-1/p)(1-1/(p-1))=1-2/p\), and at \(p\mid N\)
only \(1-1/p\) is present.

For any prescribed fixed small \(\epsilon>0\), choose \(b\)
small enough for the dimension-two upper
[fundamental lemma](https://doi.org/10.1017/CBO9780511542909.006)
at \(D=N^{.10}\) to have relative error at most \(\epsilon\).
All upper dimension constants are uniform in \(N\):
except for the smallest primes, each reciprocal local
factor is at most
\((1-1/p)^{-2}(1+O(p^{-2}))\).
For each squarefree sieve divisor \(d\), actual CRT gives
the expected root density and error at most \(2^{\omega(d)}\);
their sum to \(D\) is \(O(D L^C)\), \(L=\log N\).
Adding the target-unit restriction can only decrease the
upper count. It follows for large \(N\) that
\[
                         |\mathcal B|\le(1+2\epsilon)B_0 .
                         \tag{4}
\]
Here and below errors polynomially below \(N\) are
negligible on the scale \(B_0\). Indeed uniformly in
even \(N\),
\[
    V_N(z)/V(z)=(1+o(1))\mathfrak S(N),\qquad
    V(z)\sim e^{-\gamma}/(bL).
    \tag{5}
\]
The first assertion compares literal prime factors:
the non-target tail is \(O(1/z)\), and the target-prime
tail is \(O(L/z)\). In particular \(\mathfrak S(N)\)
is bounded below absolutely.

## 2. A genuine prime-mark marginal inside that same set

Within \(\mathcal B\), let \(\mathcal B_x\) count the rows
having \(x=rm\), with \(r>N^\rho\) a true prime,
\(m>N^\delta\), and \(P^-(m)>z\). There is at most one
such prime on a row because \(\rho>1/2\). The opposite
marginal \(\mathcal B_y\) uses \(y\) instead.

To lower-bound \(\mathcal B_x\), fix the actual \(m>N^\delta\)
with \(P^-(m)>z\), \((m,N)=1\); only
\(m\ll N^{1-\rho}\) is relevant. Use the genuine prime \(r\)
in its real interval \(r>N^\rho,\ mr\in NJ\), and sift
\(N-mr\) at the primes \(p\le z,\ p\nmid N\). No prime
\(p\le z\) divides \(m\). The sieve is on the actual
primitive residue \(r\equiv N\bar m\bmod d\) for every
squarefree \(d\) in its support. Primes \(p\le z,\ p\mid N\)
cannot divide \(N-mr\) when \(r\) is a target-unit prime.
The genuine \(r\)'s dividing \(N\) that have been excluded
cost \(O(L)\) per \(m\), power-small in the aggregate.

Use the dimension-one lower fundamental lemma, again
at \(D=N^{.10}\), with local density \(1/(p-1)\) on
\(p\le z,\ p\nmid N\) and zero at target primes. Its
dimension constant is uniform because
\((1-1/(p-1))^{-1}=(1-1/p)^{-1}(1+O(p^{-2}))\)
for \(p>2\); the prime 2 is omitted. Make its relative
error at most \(\epsilon\) by the initial choice of \(b\).
For each fixed \(m\) use ordinary maximal-prefix
[Bombieri--Vinogradov](https://doi.org/10.1112/S0025579300005313)
on **true primes** at long
scale \(X=N/m\gg_J N^\rho\).
All moduli \(d\le N^{.10}\) lie below
\(\sqrt X/L^A\) with fixed power reserve. The residue may
depend on \(m\), since this estimate is maximal over
reduced residue and interval endpoint; the density
\(\varphi(d)^{-1}\) is the actual prime principal.
Pass from prime logs to the unweighted count by real
partial summation on \(r>N^\rho\).
The absolute error for one \(m\) can be taken
\(O_A((N/m)L^{-A})\); after summing all \(m\) it retains
arbitrary log savings. No assertion of primes in a
uniform progression at an individual \(d\) is used.

Consequently \(|\mathcal B_x|\) is at least
\[
 (1-\epsilon)V_N(z)\int_{NJ}
   \sum_{\substack{N^\delta<m<v/N^\rho\\
                         (m,N)=1,\ P^-(m)>z}}
                          \frac{1}{m\log(v/m)}\,dv
                      -o(B_0).                                    \tag{6}
\]
The sum/integral follows by the real substitution
\(v=mr\) in the genuine prime principal. The strict upper
endpoint is the same as the actual lower mark gate.
Endpoint equalities are irrelevant to that integral.

To evaluate the positive inner harmonic, use the usual
integer dimension-one fundamental lemma for the
\(z\)-rough \(m\)'s at sieve level \(D_m=N^{\delta/2}\).
Choose \(b<\delta/2\) small enough for upper and lower
relative precision \(\epsilon\), uniformly for prefix
lengths \(W\ge N^\delta\). Uniform integer CRT floors
are \(O(D_m)\). Excluding primes \(p\mid N,\ p>z\)
costs at most
\(\sum_{p\mid N,p>z}\lfloor W/p\rfloor=O(W L/z)\)
uniformly; smaller target primes are already sifted.
Writing \(A(W)\) for this integer prefix count, we obtain
\[
                |A(W)-WV(z)|\le 2\epsilon WV(z)
            \quad(N^\delta\le W\le N^{1-\rho}).
\]
Partial summation for
\(f(t)=1/(t\log(v/t))\) on \([N^\delta,v/N^\rho]\)
uses \(f'\le0\) and \(t f(t)=O(1/L)\) at both endpoints.
Its relative-model error is at most
\(2\epsilon V(z)\int f(t)\,dt+O(\epsilon V(z)/L)\),
including the lower endpoint. The actual integral is
\[
 \int_{N^\delta}^{v/N^\rho}\frac{dt}{t\log(v/t)}
     =\log\!\left(\frac{\log v-\delta L}{\rho L}\right)
     =\log\!\left(\frac{1-\delta}{\rho}\right)+O_J(1/L).
\]
Thus (6), and its reflected counterpart, give
\[
 |\mathcal B_x|,\ |\mathcal B_y|
 \ \ge\left((1-\epsilon)(1-2\epsilon)
               \log\!\left(\frac{1-\delta}{\rho}\right)
                               -o(1)\right)B_0.                   \tag{7}
\]
All \(o(1)\) terms tend to zero for fixed \(b,\rho,\delta\)
uniformly in the actual even target.

## 3. The actual intersection and its positive score

Choose \(\epsilon\) first, sufficiently small that twice
the fixed coefficient of (7) exceeds \(1+2\epsilon\);
this is possible by (1). The subsequent choices of \(b\)
in §§1–2 are all finite fundamental-lemma requirements
with uniform dimension constants. Actual inclusion-exclusion
in \(\mathcal B\) now gives
\[
 |\mathcal B_x\cap\mathcal B_y|
     \ge |\mathcal B_x|+|\mathcal B_y|-|\mathcal B|
     \gg_{\rho,\delta} B_0.
\]
Both true primes are unique and distinct, since
\((x,N)=1\) implies \((x,y)=1\).
The upper bounds \(r,s<N^{1-\delta}\) follow from
\(x,y<N\) and \(m,n>N^\delta\).
Remove all actual repeated squares on either coordinate.
Since all its primes exceed \(z\), at most
\(2\sum_{p>z}\lfloor N/p^2\rfloor=O(N/z)\)
possible \(x\)'s are lost. This is \(o(B_0)\) by (5).
The remaining prime factors all exceed \(N^b\),
and \(m,n<N^{1-\rho}\), proving the rank bound and (2)–(3).

Finally if \(F,G\) are flat with value one at zero and
supported on \([0,b]\), then on every such actual row
the score at the unique high mark has only the literal
divisor \(d=1\). Every other divisor of \(m\) or \(n\)
exceeds \(z\), hence has profile argument \(>b\).
The \(d=1\) argument is in the flat region for all large
\(N\). Thus the product is exactly \((\log r)(\log s)\),
at least \(\rho^2 L^2\), and multiplying (2) by this
amount proves the claimed positive subset.
