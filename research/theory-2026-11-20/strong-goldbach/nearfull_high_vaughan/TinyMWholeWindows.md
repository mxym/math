# Whole quotient windows in the original giant-prime score

Retain the original actual two-prime score and strict \(Q_y(m)\)
from [TinyMOriginalGiant.md](TinyMOriginalGiant.md), with
\(S=\exp((\log\log N)^4)\) and \(I\subset(\sqrt N/(S L^{C_1}),N/S]\).
Take \(\operatorname{rad}(N)\le L^{B_0}\) with fixed \(B_0\).
There exists a fixed \(c_*>0\) such that, uniformly on an
independent real interval \([M_-,M_+]\) in the actual quotient
\(m=y/r\), if
\[
        V_m=1+\log(M_+/M_-)\le \ell^{c_*},
\]
the **whole original signed score on this window** is
\(o(N\mathfrak S(N))\). There is no tiny-bank hit requirement
in this conclusion. The usable window may contain many dyads,
and may be centered at subpower or polynomial \(m\) scales.
The statement does not price the full original \(m\)-range.

## 1. Actual bank hit and no-hit harmonics

In TinyMOriginalGiant an extra independent real interval on
\(m\) is harmless throughout: in Type I it intersects the
fixed-point harmonic interval, and in Type II it intersects
the smoothed \(m\)-window on the same actual moving mesh.
Thus its \(E(m)=1\) part is \(O_D(NL^{-D})\).
Choose a fixed satisfactory \(K\) for this result, and take
\(\asymp_K\log\ell\) disjoint admissible tiny families.
There is a fixed \(\kappa>0\) such that on the independent
quotient window, truncated to the original
\(m\gg S,\ m\le\sqrt N S L^{C_1}\), one has
\[
               \sum_{m:E(m)=0}\frac1m
                  \ll V_m\ell^{-\kappa}+O_D(L^{-D}).             \tag{1}
\]
This is an ordinary integer harmonic calculation, not a
statement about the distribution of prime pairs. The
inclusion–exclusion expansion of the Boolean no-hit product
has only \(\ell^{O_K(1)}\) avoidance terms. For each such
term use the Rankin unit-count floor in TinyMOriginalGiant,
§1, at \(\sigma=1-c/\ell^{\theta_+}\), and partial summation.
Since the lower endpoint is \(\gg S\), its error is smaller
than every fixed power of \(L^{-1}\), even after the
Boolean expansion. The real harmonic model is its log width
times the finite independent prime-local density. Each
disjoint family has hit probability bounded below by a
fixed positive constant from its color harmonic masses,
giving \(\ell^{-\kappa}\) after the \(\asymp\log\ell\)
families. Arbitrarily partial interval endpoints are allowed.

## 2. True prime-prime upper at a fixed \(m\)

The exceptional original prime rows not target units have
the power-small cost already noted in TinyMOriginalGiant.
Keep \((m,N)=1\) on all other rows. Define
\[
       c(m)=\prod_{\substack{p\mid m\\p>2}}\frac{p-1}{p-2}.
\]
Since \(m\) is a target unit the indices in this expression
also satisfy \(p\nmid N\). At fixed actual \(m\), the true
primes are \(r\) and \(N-mr\), both on polynomial scales
since \(m\le N^{1/2+o(1)}\). On a real \(y=mr\) cell of
length at most \(\Delta N\), enlarge to a cell of that
length for the positive upper. With
\(\Delta=\ell^{-G}\), choose a fixed sufficiently small
polynomial sieve depth and a fixed large dimension-two
sieve ratio as in the prior positive two-form upper.
For \(p\mid m\) the opposite affine form is a nonzero
constant, leaving one root. Otherwise the two roots
coincide precisely at \(p\mid N\), with the forced one
root at 2. The integer parameter \(r\) has length scale
\(\Delta N/m\ge N^{1/2-o(1)}\); the positive upper
sieve floors are absorbed per tuple. Its local density
relative to the pair of prime Mertens factors is bounded
by a fixed constant times \(\mathfrak S(N)c(m)\).
Multiplying back the two genuine prime logs gives
\[
 \sum_{\substack{y=mr\ {\rm in\ cell}\\ r,N-mr\ {\rm prime}}}
        (\log r)\log(N-mr)
            \ll \Delta N\,\mathfrak S(N)c(m)/m.                 \tag{2}
\]
Any other actual gate, including \(r\in I\), may only
decrease this positive upper. Dropping the finite
target-prime conditions on \(r\) or \(N-mr\) for this
upper needs no further prime-density assertion.

Here the variable \(c(m)\) cannot just be taken at its
pointwise maximum on a polynomial \(m\)-interval.
Instead \(\sum_{m\in[M_-,M_+]}c(m)^4/m\ll V_m\).
Indeed expand \(c(m)^4\) into a positive squarefree
divisor sum with \(p\)-coefficient \(O(1/p)\). On any
dyad the reciprocal mass of actual multiples of a divisor
\(b\) is \(O(1/b)\) (and zero if \(b\) exceeds the upper
endpoint). The resulting Euler product converges.
This proves the stated bound after summing dyads,
and likewise the lower power estimates. Together with
(1) and Cauchy it yields
\[
             \sum_{m:E(m)=0}\frac{c(m)^2}{m}
                     \ll V_m\ell^{-\kappa/2}+O_D(L^{-D}).
                                                                  \tag{3}
\]
The unit restriction can be dropped in this positive
harmonic estimate; it was retained in the affine count.

## 3. Exact short-score cutoff in each cell

In a cell freeze \(T_y=y/B\) at a value \(T_j\asymp S\).
By [de la Bretèche--Dress--Tenenbaum, equation (1.5)](https://tenenb.perso.math.cnrs.fr/PPP/Sxz.pdf),
the sharp truncated Möbius sum obeys
\(\sum_{n\le X}|\sum_{d\mid n,d\le T}\mu(d)|^2\ll X\),
uniformly in both real \(X,T>1\). Use the integer cutoff
\(\lceil T_j\rceil-1\) for the original strict inequality.
Dyadic partial summation gives
\(\sum_{m\in[M_-,M_+]}|Q_{T_j}(m)|^2/m\ll V_m\).
Apply Cauchy to (2) with (3) and this second moment.
The missed contribution with the frozen score in this
cell is at most
\[
   O\!\left(\Delta N\,\mathfrak S(N)V_m\ell^{-\kappa/4}\right)
       +O_D(\Delta N\,\mathfrak S(N)L^{-D}).
\]

For the correction from \(T_j\) to \(T_y\), the differing
labels are true divisors \(d\mid m\) in a relative
\(O(\Delta)\) collar of \(T_j\). For each such \(d\),
\(c(m)\le c(d)c(m/d)\), and the same convergent divisor
harmonic bounds the mass of multiples by \(O(V_m c(d)/d)\),
even when \(m/d\) is near 1. Also
\(c(d)\ll\log\log(3d)\ll\log\ell\) since \(d\asymp S\).
Consequently the actual collar shot through (2) costs
\[
 O\!\left(\Delta N\,\mathfrak S(N)V_m(\Delta+1/S)
                         \log\ell\right)
\]
per cell. This uses positive upper counting only for the
error, not to price the signed covered part.
Summing \(O(1+\Delta^{-1})\) cells yields a total bound
\[
  O\!\left(N\mathfrak S(N)V_m
      \left(\ell^{-\kappa/4}+\Delta\log\ell\right)\right)
       +O_D(N\mathfrak S(N)L^{-D}).
\]
Taking \(c_*=\kappa/8\) and \(G>c_*+2\) proves the theorem.
The \(V_m\) loss is genuine in this argument; covering full
logarithmic \(m\)-widths such as a fixed fraction of
\(\ell^4\), let alone a polynomial interval, does not
follow. This is cancellation only for the existing
original prime-divisor remainder on windows, not a
claim of binary positivity.
