# A positive native sextic correlation with actual over-root three-prime tags

Fix an individual large even \(N\), \(L=\log N\), a nondegenerate
\(J\Subset(1/3,2/3)\), and the actual pairing \(x+y=N,\ x\in NJ\),
\((x,N)=1\). Set \(M=|J|N\mathfrak S(N)\). Keep **exactly** the sharp
[sextic score](../sextic_true_tag_rebate/Proof.md)
\[
 F(t)=44(1/2-t)_+^4-112(1/2-t)_+^6,\qquad
 V(n)=\mu^2(n)\log n\sum_{j\mid n}\mu(j)F(\log j/\log n),\qquad
 H=V-\Pi ,
\]
where \(\Pi(n)=1_{n\ {\rm prime}}\log n\). Thus \(F'(0)=-1\) and
\(F''(0)=-78\).

Use three disjoint genuine prime banks, with half-open
\(\log_N p\) intervals
\[
       (.02999,.03000],\qquad (.07800,.07801],\qquad (.39240,.39241].
\]
Write \(\mathcal D\) for the products \(d=a b c\) of precisely one
actual prime in each respective bank. Define
\[
             Z(n)=\mu^2(n)\log n\sum_{\substack{d\mid n\\d\in\mathcal D}}1 .
\]
The marks retain their literal multiplicity. Each selected divisor
is genuinely above the square root, since
\(.50039<\log_N d\le .50042\); its complementary actual integer
has target-log angle in \([.49958,.49961]+O_J(1/L)\) and is not
assumed prime or rough.
Every actual nonzero source row is composite.

**Proposition.** Uniformly through individual even targets,
\[
 \langle Z,H\rangle
  =78\,\left(\int_{NJ}\frac{\log x}{\log(N-x)}\,dx\right)
     \sum_{\substack{d\in\mathcal D\\(d,N)=1}}
                  W_{N,d}\,C_{N,d}
     +o(N),                                                        \tag{1}
\]
where the two explicit positive factors are
\[
 \begin{split}
 W_{N,d}&=\frac1d\prod_{p\nmid Nd}
                   \left(1-\frac1{p(p-1)}\right),\\
 C_{N,d}&=\gamma_E+\sum_{p\mid Nd}\frac{\log p}{p-1}
      +\sum_{p\nmid Nd}\log p
          \left(\frac1{p(p-1)}-\frac1{p[p(p-1)-1]}\right).
 \end{split}                                                       \tag{2}
\]
In particular \(\langle Z,H\rangle\gg M\). The reflected orientation
has the same assertion on its reflected interval. This is a signed
fixed-target result for the **native** \(H\), with its own genuine
prime atom subtracted. It is not an estimate for the compensated
\(S\)-by-\(S\) residual or for an exact two-prime receiver.

## 1. The two genuine moduli and the literal prime progression

Write \(\mu^2(n)=\sum_{s^2\mid n}\mu(s)\) on either arm. Fix
\(\epsilon_s=.00001\). Discard \(s>N^{\epsilon_s}\) on either
true arm at a power saving, even before the signed sums: the central
number of multiples of some \(s^2\) with \(N^{\epsilon_s}<s\le\sqrt N\)
is \(O(N^{1-\epsilon_s}+\sqrt N)\), and any physical row has total
weight bounded by \(N^{o(1)}\) in the displayed expansions.
On the source let \(q=[d,s^2]\). On the receiving raw \(V\) arm
let \(r=[j,t^2]\), where \(t\le N^{\epsilon_s}\). The original
target-unit condition forces \((qr,N)=1\) and \((q,r)=1\).
For these physical labels \(q\le N^{.50044}\), \(r\le N^{.50002}\);
also all three prime factors of \(d\) exceed the source square
label \(s\). Thus \(q=d s^2\) on the retained physical expansion.
The sum of the absolute coefficients within each grouped
integer \(q\) or \(r\) is bounded by a fixed divisor power
times a fixed power of \(L\).

To apply the genuine prime estimate to \(\langle Z,\Pi\rangle\),
keep the exact factored progression \(q_1q_2q_3=q\) with
\(q_1=c s^2,\ q_2=a,\ q_3=b\). The residue is the literal reduced
\(N\), and its reduction modulo \(q_1q_2\) does not depend on \(q_3\).
For each real prime prefix scale \(Y\asymp_J N\), use the
[primary Maynard III, Theorem 1.2](https://ora.ox.ac.uk/objects/uuid%3Ada3b7279-d413-4ab1-962e-afa5d67507c2/files/s6w924c97m)
at the fixed ceilings
\[
       (Q_1,Q_2,Q_3)=(Y^{.39245},Y^{.03005},Y^{.07805}),
                  \qquad \delta=.00055 .
\]
They contain the genuine slots with fixed power slack even when
\(Y\ne N\). Their product is \(Y^{1/2+\delta}\);
the stated two rails for \(Q_2\) are
\(.022<.03005<.04615\), and those for \(Q_3\) are
\(.07655<.07805<.07977\). In particular neither a changing
small representative for \(N\), nor a theorem for arbitrary
unfactored over-root \(q\), is used.

The theorem's absolute progression errors tolerate the fixed
divisor weights here. One way to see this is Cauchy interpolation
between its arbitrary-log absolute error and
\(\sum_{q_1,q_2,q_3}\tau(q_1q_2q_3)^K |E_{q_1q_2q_3}|
\ll Y(\log Y)^{O_K(1)}\) for any fixed \(K\), from the elementary
progression upper \(O(Y(\log Y)^C/q)\) and the corresponding
\(1/\varphi(q)\) upper. Factorization multiplicities are divisor
bounded. Use actual common prefixes and partial summation for
\(\log y\) on the prime arm and \(\log(N-y)\) on the other; the
ordinary PNT gives arbitrarily high log accuracy for the principal
prime mass. A genuine prime \(y\mid N\) can be removed at
\(N^{o(1)}\) total cost before using the unit condition.
Consequently, with error \(o(N)\), the exact prime cross is
\[
 \langle Z,\Pi\rangle
    =\int_{NJ}\log x\,dx\
      \sum_{\substack{d\in\mathcal D,\ s\le N^{\epsilon_s}\\(ds,N)=1}}
          \frac{\mu(s)}{\varphi([d,s^2])}+o(N).                    \tag{3}
\]

## 2. The raw \(V\) correlation at actual grouped moduli

The corresponding nonprime correlation \(\langle Z,V\rangle\)
has the genuine compatible progression main for \(q,r\), including
the factor \(\varphi(N)/N\) from target units. Here are the full
range and cutoff details. One can first smooth the physical
endpoints on log-fine strips of length \(N L^{-B}\) and subdivide
the remaining spatial interval by a smooth partition on that
mesh. Discarded actual strips are \(O(NL^{-B/2+O(1)})\) by Cauchy
and the ordinary moments of fixed divisor powers on \(x,y\).
The model strip has the same bound, using the divisor harmonics.
Freeze only the argument denominator \(\log y\) of \(F\) on each
cell, with error \(O(L^{-B})\) per term by its Lipschitz bound.
The derivative norms of the spatial weights are log powers.
Thus the remaining divisor coefficients are independent on their
grouped \(q,r\) intervals. The outer \(\log x,\log y\) stay true;
they can be included in the smooth spatial factor. There is no
angular taper in \(F\), nor a replacement of its own root by a
fixed global half. Restoring all frozen model denominators uses
the same absolute divisor harmonic and log-fine margin. These
reductions cost \(o(N)\) by choosing \(B\) sufficiently large.

For clarity, power saving on each grouped dyad follows by the
[actual reciprocal proof](../nearfull_high_vaughan/JointGiantActualMarkBlock.md),
now with arbitrary independent divisor-bounded coefficients on the
grouped moduli. Open target units by \(u\mid(x,N)\), and cut
\(u>N^{.00001}\), at a power saving in both the literal divisor
count and its reciprocal model as in the
[all-divisor slab](ArbitraryDivisorSlab.md). At fixed \(u\), write
\(X=N/u\); shifting \(x=u q m\) leaves \(m\equiv X\overline q\bmod r\)
and preserves the literal normalized spatial weight.
On physical dyads \(Q,R\), ordinary progression floors suffice
when \(g=\log_X(QR)<.99\). Otherwise use
[Bettin--Chandee, Theorem 1](https://arxiv.org/pdf/1502.00769)
on each signed nonzero Poisson-frequency dyad, after truncating
frequencies at \(X^\eta(1+QR/X)\) for tiny fixed \(\eta>0\).
Smooth rapid decay removes the rest. The Fourier factor separates
by Mellin in the compact normalized ratio of frequency to the
two grouped moduli: its multiplicative transform is log-bounded,
with arbitrary decay when the normalized frequency is large, and
the three separated twists preserve the three \(L^2\) norms.
The modulus coefficients have norms \(Q^{1/2}N^{o(1)}\),
\(R^{1/2}N^{o(1)}\). With \(m_0=\log_X\max(Q,R)\), one has
\(g\le1.002,\ m_0\le .501\). The exponents for the nonzero terms
relative to \(X\), after the Poisson prefactor and before tiny
frequency/epsilon losses, are bounded by
\[
 \begin{cases}
 .7g+.25m_0-.85,\quad .875g+.125m_0-1,&g\ge1,\\
 .5-.65g+.25m_0,\quad .5-.625g+.125m_0,&.99\le g<1 .
 \end{cases}
\]
All four are \(<-.018\) here. No extra power for expanded square
labels is needed: they were grouped by their **actual** \(q\) and
\(r\) before using these norms. Summing the log mesh and the
\(N^{o(1)}\) possible target divisors preserves power saving.
The CRT zero mode has denominator \(qr\);
\(\sum_{u\mid N}\mu(u)/u=\varphi(N)/N\) restores its target density.

It follows, putting \(B=Nq\) in the inner model, that
\[
 \langle Z,V\rangle
  =\frac{\varphi(N)}N\int_{NJ}\log x\,\log y\
       \sum_{\substack{d\in\mathcal D,\ s\le N^{\epsilon_s}\\(ds,N)=1}}
       \frac{\mu(s)}q
       \sum_{\substack{j,t\ge1\\(jt,B)=1}}
           \frac{\mu(j)\mu(t)}{[j,t^2]}F\!\left(\frac{\log j}{\log y}\right)
       \,dx+o(N),
       \qquad y=N-x .                                               \tag{4}
\]
Here the model \(t\)-cut has been extended to infinity: for \(t\)
squarefree the absolute \(j\)-harmonic of \((j,t)/j\) over
\(j\le N^{.5}\) is \(O(\tau(t)L)\), and \(t^{-2}\) gives a power
saving in the tail. The exact coprime \(B=Nq\) on both receiver
labels is indispensable for the next term.

## 3. The second moment and its sign after all square adjustments

At fixed \(B\ll N^2\) define the signed harmonic Dirichlet series
\[
 \mathcal A_B(z)=
  \sum_{(jt,B)=1}\frac{\mu(j)\mu(t)}{[j,t^2]j^z}
  =\frac{\mathcal K_B(z)}{\zeta(1+z)} \qquad(\Re z>0).
\]
At \(p\nmid B\) the actual local factor before removing \(\zeta^{-1}\)
is \(1-p^{-2}-(p^{-1}-p^{-2})p^{-z}\), because the \(j,t\) overlap
was a single \(p^2\) modulus. At \(p\mid B\) the factor is \(1\).
The exact values are therefore
\[
    \mathcal K_B(0)=\frac B{\varphi(B)},\qquad
    \frac{\mathcal K_B'(0)}{\mathcal K_B(0)}
       =-\sum_{p\mid B}\frac{\log p}{p-1}
        -\sum_{p\nmid B}\frac{\log p}{p(p-1)}.
\]
Thus the zeroth, first, and second log moments of \(\mathcal A_B\),
respectively, are \(0\), \(-B/\varphi(B)\), and
\(-2(B/\varphi(B))D_B\), where
\[
                 D_B=\gamma_E+\sum_{p\mid B}\frac{\log p}{p-1}
                            +\sum_{p\nmid B}\frac{\log p}{p(p-1)}.
\]

We justify their use for the actual \(F\). Factoring
\(\zeta^{-1}\) expresses the coefficient of \(j^{-z}\) as a
convolution with \(\mu(j)/j\). The coefficients of
\(\mathcal K_B\) have absolute harmonic norm
\(O((\log L)^C)\) already at \(\Re z=-1/\log L\), uniformly
in \(B\ll N^2\): the unrestricted local corrections are
\(O(p^{-2+1/\log L})\), and the inverted missing factors at
\(p\mid B\) are handled by splitting at \(p=L^2\).
For the upper range use \(\omega(B)=O(L)\), and below it use
\(p^{1/\log L}\le e^2\) and the ordinary prime harmonic.
Rankin therefore cuts this convolution at
\(T=\exp((\log L)^4)\) with arbitrary-log saving, including the
fixed first two log moments. In the \(\mu(j)/j\) variable the
ordinary signed Mertens tail from \(T\), by partial summation
against the fixed Lipschitz profile and its log derivatives,
is also arbitrary-log small. The same signed tail pays
the truncated zeroth, first and second moments. Taylor on
the two remaining subpower labels costs
\(O((\log L)^C/L^2)\) after the outer factor \(\log y\).
Consequently the exact inner profile in (4) has expansion
\[
 \log y \sum_{(jt,B)=1}\frac{\mu(j)\mu(t)}{[j,t^2]}
                  F\!\left(\frac{\log j}{\log y}\right)
    =\frac B{\varphi(B)}
      \left(1+\frac{78 D_B}{\log y}\right)
         +O\!\left((\log L)^C/L^2\right),                            \tag{5}
\]
uniformly in the real central \(y\) and allowed \(B\).
The leading term gives precisely the same
\(1/\varphi(q)\) as in (3), since \((N,q)=1\);
this cancels the true prime cross. The error in (5) is \(o(N)\)
in (4): the absolute \(s\)-harmonic
\(\sum_s 1/[d,s^2]\ll1/d\) for literal squarefree \(d\) of rank
three, and \(\sum_{d\in\mathcal D}1/d\ll1\) by the three true
prime harmonics. Thus the extra \(\log x\) costs only one \(L\).

For the remaining moment extend \(s\) to infinity at power
saving. For example
\([d,s^2]=d\,s^2/(d,s)\) for squarefree \(d,s\), and Rankin's
argument with \(s^{1/4}\) in the summable harmonic
\(\sum_s(d,s)/s^2\) absorbs both the totient and \(D_B\)
logarithms. For \(D_B\) the same prime-divisor split gives
\(O(1+\log\log(3B))\) on the whole model, also for the extension.
The unrestricted sum of \(\mu(s)/\varphi([d,s^2])\)
has at \(p\mid d\) the factor \(1-1/p\) beyond \(1/\varphi(d)\);
at \(p\nmid Nd\) it has \(1-1/[p(p-1)]\), and primes of \(N\) are
omitted. This is \(W_{N,d}\). At each \(p\nmid Nd\), including \(p\)
in \(s\) changes \(D_{N[d,s^2]}\) by \(\log p/p\). Its normalized
signed harmonic inclusion weight is
\(-1/[p(p-1)-1]\). At \(p\mid d\) there is no such change.
Absolute convergence justifies this first-moment calculation,
giving exactly \(W_{N,d}C_{N,d}\). Substituting into (5) proves (1).

All summands in \(C_{N,d}-\gamma_E\) are nonnegative since
\(p\nmid Nd\) implies \(p\ge3\). The product in \(W_{N,d}\)
is bounded below by a positive absolute constant, and the
three prime harmonics of the actual fixed bands have positive
limits. Removing their primes dividing \(N\) changes them by
\(o(1)\). Finally
\(\mathfrak S(N)\ll 1+\sum_{p\mid N}\log p/(p-1)\):
for \(A=\sum_{p\mid N}\log p/(p-1)\), apply the ordinary Mertens
product up to \(e^{1+A}\) to the singular-series factors,
and bound the logarithm of the remaining target factors by
\(O(A/(1+A))\). This makes the strict lower in (1) uniform at
scale \(M\). It comes from the second signed harmonic, not an
asserted positive first moment or a parity model for the prime
cofactor. The score on the \(Z\)-arm is not the compensated
Goldbach score; no increment is added to a compensated comparison.
