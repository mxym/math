# Pooled true-prime windows far beyond the root

Use the literal grouped high-cut score (1) of
[NativeCofactorProduct.md](NativeCofactorProduct.md). In particular,
\(U=\exp((\log\log N)^3)\), \(z=\exp((\log\log N)^2)\),
\(W=\sqrt N/S^{C_0+10}\), \(S=\exp((\log\log N)^4)\),
and \(I=[N/S^{C_0},N/S]\). The weight is
\[
 (\log f)(\log h)H_U(A)H_U(C)Q_y(m),
 \qquad A f=x\in NJ,\quad m C h=y=N-x,\quad C h\in I,
\]
with genuine primes \(f,h>W\), \((xy,N)=1\), and \(P^-(AC)>z\).
The original strict short-divisor score \(Q_y(m)\) is unchanged.

**Theorem.** Fix \(\eta>0\). Restrict the two true prime labels to
independent real intervals with endpoints \(F_-,F_+\) and \(H_-,H_+\).
Assume
\[
 \begin{gathered}
 W\le F_-\le F_+\le N^{1-\eta},\qquad
 W\le H_-\le H_+\le N^{1-\eta},\qquad F_-H_-\ge N^{1+\eta},\\
 \min(F_+,H_+)\le N^{2/3-\eta}.                              \tag{1}
 \end{gathered}
\]
Write \(V_F=1+\log(F_+/F_-)\), \(V_H=1+\log(H_+/H_-)\), and
\(L=\log N\). For each fixed \(D>0\) there are fixed \(c,\kappa>0\)
such that, uniformly at each even \(N\) and in the endpoints,
the absolute value of the **signed score** in these windows is
\[
 O\!\left(N V_F V_H(\log L)^c L^{-\kappa/2}\right)
       +O_D(NL^{-D}).                                         \tag{2}
\]
In particular \(V_F V_H\le L^{\kappa/4}\) implies \(o(N)\). At
\(\operatorname{rad}(N)\le L^{B_0}\), with \(B_0\) fixed, the last
condition in (1) can be omitted. A pair of genuine dyads at
\(f,h\asymp N^{.60}\) qualifies, far outside the range of the
[prime reciprocal estimate near .532](PrimeInverseAveraging.md).
The new bound is not a statement about occupancy, and does not send
a saving through an entire angular band of log widths \(\asymp L\).
Bounds on overlapping regions are not added.

## 1. Signed covered part

Use the separated banks, first-success decomposition and one-prime
projected comparison of
[NativeCofactorProduct.md, §§1–2](NativeCofactorProduct.md) and
[AllEvenNative.md, §1](AllEvenNative.md). The bank labels exceed
\(S^{C_0}\) and \(U\). Freeze the literal \(m\)-gate
\(T_y\le m\le yS^{C_0}/N\) and the strict \(Q_y(m)\) cutoff on the
same relative log-fine \(y\)-mesh. As there, a changed row is a
true multiple of \(m\) or of a changing divisor of \(m\), and
fixed crossed divisor moments pay the global collar. Smooth central
packets keep the required log-power derivative norms. The independent
true prime windows can be subdivided into a log-power number of
fixed-ratio packets along with the source products.

If \(F_+\le N^{2/3-\eta}\), use the projected source \(A f\), with
\(A\) avoiding the chosen bank and \(C\) supplying one actual
tag per color. The signed cofactor has scale \(\gg_{J_0}N^{1/3+\eta}\).
At any full projected character modulus \(M\le NL^{O(1)}\) retain
the exact rough \(d\le U\) and bank/roughness labels \(e\) on
\(A/d\), as in AllEvenNative. Their sizes and numbers are
\(\exp(O(L^{.3}))\), and their positive factorial omission costs
are unchanged. The principal retains the exact masked rough
\(\sum \mu(d)/d=O_E(L^{-E})\) at this \(U\). In the nonprincipal
case use the general-modulus \(r=3\) Burgess bound
\[
 \left|\sum_{n\in K}\chi(n)\right|
      \ll_\epsilon |K|^{2/3}q^{1/9+\epsilon}
\]
for primitive conductor \(q\) (see
[Burgess's \(r=3\) paper](https://doi.org/10.1112/jlms/s2-33.2.219)
and the unrestricted form in
[Hasanalizade et al., p. 1](https://arxiv.org/pdf/2511.17778v2)).
Opening the extra imprimitive unit primes and removing complete
periods as needed gives \(O_\epsilon(X^{2/3}M^{1/9+\epsilon}\tau(M))\)
on an interval at scale \(X\). After the actual \(d,e\) openings,
the free scale is \(X\gg N^{1/3+\eta-o(1)}\), so this saves a fixed
power relative to \(X\), uniformly in real prefixes and the fixed
log-power partial-summation weights. The same estimate on the
whole integer \(f\)-interval gives the power-small off-diagonal
Gram entries; the genuine prime coefficient enters only after
this restricted Bessel step. For small-radical targets the
Iwaniec estimate in the original native proof applies instead
on any fixed positive polynomial length.

If \(H_+\le N^{2/3-\eta}\), orient the source as \(D_0 h\) with
\(D_0=mC\), \(C\) avoiding the chosen bank and \(A\) supplying its
tags. Avoidance of \(C\) is the same as avoidance of \(D_0\), since
every bank prime exceeds \(m\). The source coefficient is the
actual grouped sum of \(H_U(C)Q_T(m)\) over \(mC=D_0\) with its
frozen \(m\)-gates and rough \(C\). Its norm and clipping obey
ordinary divisor moments in \(D_0\) and the physical \(D_0\mid y\).
Do not assume \(D_0\) rough. For the full rational major split the
polylogarithmic arc denominator as \(d_0d_1\), with \((d_0,N)=1\)
and \(d_1\) supported on target primes, exactly as in
[BothLabelsOverRoot.md, §3](BothLabelsOverRoot.md).
At fixed actual \(m\), the literal residue \(D_0\equiv b\bmod d_0\)
is impossible if \((m,d_0)\nmid b\), and otherwise reduces to a
class on \(C\bmod d_0/(m,d_0)\). A nonunit resulting class is
empty since \(C\) is \(z\)-rough; expand the reduced class in
characters. The other factors involving \(m\) are constant for
this linear estimate; all resulting conductors divide \(N\) times
a polylogarithmic arc factor. Apply the preceding principal and
Burgess bounds at the true \(C\)-scale \(D_{0,\rm scale}/m\), then
sum the reciprocal \(\sum_{m\le S^{C_0}}\tau(m)/m\), not the count
of \(m\)'s. The Gram and endpoint arguments use the genuine \(h\)
prime in this orientation. This also works with Iwaniec if the
radical is small.

In either orientation the minor comparison uses the genuine
polynomial prime source argument at each determinant endpoint:
its gcd divides a nonzero determinant of size \(O(Y)\) on the
tag scale \(u\asymp Y=N^{o(1)}\); complete chosen-bank avoidance
rules out the zero determinant. This argument does not require
the bank-avoiding cofactor to have square-root size or to be
rough at the tag scale. Square incidences of the bank primes
are first paid by actual divisibility of \(x\) or \(y\).
The extracted opposite factor keeps its literal prime and
\(Q_T\) weights, short masks and reciprocal hit allocation.
Its squared norm is \(O((N/Y)L^{O(1)})\) by genuine divisor
multiplicity, with no cardinality loss from \(m\). The original
phase, log-weight and Mellin separations, and the high tag moment
comparison now give \(O_D(NL^{-D})\) for the signed covered sum
after the log-power packet costs. The chosen source direction
is fixed for the pair of windows.

## 2. Positive bound for the actual missed part

For each actual \(A,C,m\), target units and compatibility force
\((A,mC)=1\). The exact equation for \(f,h\) is one integer
progression, with steps \(mC\) in \(f\) and \(-A\) in \(h\).
Its parameter length on the compact central interval is at
scale \(T\asymp_{J_0}N/(A m C)\). At fixed \(m\) enlarge to
the independent actual cofactor envelopes
\[
       c_0N/F_+\le A\le c_1N/F_-,
 \qquad c_0N/(mH_+)\le C\le c_1N/(mH_-)
\]
with fixed \(0<c_0<c_1\) from the compact support. Their
lower endpoints are polynomial and their log widths are
\(O_{J_0}(V_F),O_{J_0}(V_H)\). Throughout this enlargement
\(A mC\le c_1^2 N^2/(F_-H_-)\), so \(T\gg N^\eta\).
For the positive upper it is now legitimate to use the entire
central parameter interval.

Apply the dimension-two universal upper sieve on the actual
two affine forms, as in [the original high-cut proof, §5](Proof.md),
with support \(d\le N^{\eta/4}\) and prime depth \(N^{\eta/1000}\)
(or smaller fixed depths at the same ratio). True \(f,h>W\)
exceed the depth. A prime dividing a base coefficient leaves
one affine form constant and nonzero and the other with one
root, by target units and the base gcd. Otherwise both roots
exist and coincide exactly at \(p\mid N\). Thus the root count
is 1 at primes of \(N A mC\), 2 elsewhere, including the
forced value 1 at 2. At each squarefree \(d\) the interval error
is \(O(2^{\omega(d)})\); their total \(N^{\eta/4+o(1)}\) is
absorbed **per base tuple**. The fundamental lemma and Mertens
give \(O(T(\log L)^{O(1)}L^{-2})\), since the missing-root
inflation at primes of the polynomial-sized \(N A mC\) is at
most a fixed power of \(\log L\). Both genuine prime logs
therefore leave the uniform positive bound
\[
                  O(N(\log L)^{O(1)}/(A m C)).                 \tag{3}
\]
There is no reciprocal spectral or other nonzero-mode error
in this step.

In (3) preserve the actual failure indicator and the absolute
**grouped** weight \(|H_U(A)H_U(C)|\). On either independent
cofactor interval, with lower endpoint \(X_0\) and log width
\(V-1\), partial summation on true multiples gives
\[
 \sum_{n\in K}\frac{|H_U(n)|^2}{n}
 \le \sum_{d,e\le U}\sum_{\substack{n\in K\\[d,e]\mid n}}\frac1n
 \ll V(\log(2U))^3+U^2/X_0.
\]
Here \([d,e]=g d_1e_1\) at \(g=(d,e)\), and the repeated-label
floor in each harmonic is \(O(1/X_0)\). This opens the weight
only to estimate its independent second moment, not inside
the prime-lattice upper.

On these same independent intervals the harmonic mass of
the true failure indicator is
\(O(V_F V_H L^{-\kappa})+O_E(L^{-E})\) for some fixed
\(\kappa>0\). Indeed the Boolean product expands into log-power
many products of separable avoidance masks. On each interval
the harmonic for an avoidance mask equals its log width times
the exact prime-local density, with arbitrary-log error by
the factorial integer Bonferroni opening: each such true
divisor contributes a floor \(O(1/X_0)\), and the size and
number of labels are subpower. In the model each disjoint
family has success probability bounded below by a positive
constant because each color has reciprocal mass bounded above
and away from zero. The \(\asymp\log L\) families give the
fixed \(\kappa\). This is an integer harmonic comparison,
not independence of prime pairs.

Cauchy now bounds the weighted failed harmonic by
\(V_F V_H(\log L)^{O(1)}L^{-\kappa/2}+O_E(L^{-E})\).
Sum (3) over \(m\) with
\(|Q_y(m)|\le \tau(m)\) and
\(\sum_{m\le S^{C_0}}\tau(m)/m\ll(\log S)^2\). Fix the covered
precision before choosing the color count and thus \(\kappa\);
only then take the pooled-width conclusion. This proves (2).
Two full angular widths would cost up to \(L^2\) in this
positive missed bound, which its fixed bank saving does not
pay. No global overhalf sign follows.
