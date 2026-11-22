# A true weighted positive block of the exact sextic residual

Keep the original fixed even target \(N\), genuine unit pairing
\(x+y=N,\ x\in NJ,\ (x,N)=1\), \(L=\log N\), and
\(M=|J|N\mathfrak S(N)\). Use **exactly** the score
\(S=G_b+W\) in [the full medium cohort](FullMediumCohort.md):
\(H\) is the original sharp sextic, \(b=.003\), and
\(W\) is the actual negative medium cohort on the stated 729 cells.
In particular \(R_J\ge .257M+\langle S,S\rangle+o(M)\).

Let \(\mathcal E\) consist of the original ordered rows on which
**both** coordinates are squarefree of exact rank 2 or 3, and
each of their true prime factors exceeds \(N^{.150}\).
There is no parity selection between the two ranks. Define
\[
 C_{\rm other}
     =\sum_{\substack{x+y=N,\ x\in NJ,\ (x,N)=1\\
                       (x,y)\notin\mathcal E}}S(x)S(y).
\]
Then
\[
 \sum_{(x,y)\in\mathcal E}S(x)S(y)>.470M+o(M),\qquad
          R_J\ge .727M+C_{\rm other}+o(M).                       \tag{1}
\]
The positive block is removed exactly once, on the same physical
score and row set. This is not an unconditional sign of the
remaining covariance; it gives no sign for \(C_{\rm other}\) and
does not imply the existence of a binary prime pair or of a
rank-two/rank-two pair.

## 1. One genuine common rough ambient set

Put \(a=.150,\ z=N^a,\ \theta=.499,\ D=N^\theta\).
Let \(\mathcal B\) be the actual ordered rows with both least
factors \(>z\), including the target units. To upper-bound its
size one may omit target units. The two forbidden affine roots
coincide at \(p\mid N\), including 2, and are distinct otherwise.
Write \(\nu_N(p)=1\) for \(p\mid N\), and 2 otherwise.
The [literal rank-joint proof, §1](../exact_rank_joint/Proof.md)
gives the standard Selberg square with coefficient support
\(d\le D,\ d\mid\prod_{p\le z}p\); its bound is
\[
 |\mathcal B|\le |J|N
 \left(\sum_{\substack{d\le D\\d\mid\prod_{p\le z}p}}
            \prod_{p\mid d}\frac{\nu_N(p)}{p-\nu_N(p)}\right)^{-1}
                     +O(D^2L^{10}).                             \tag{2}
\]
Indeed the actual tested modulus is the squarefree
\([d,e]\); its CRT error contains at most
\(2^{\omega([d,e])}\) exact floors. The Selberg coefficient
bound \(|\lambda_d|\le3^{\omega(d)}\) gives the displayed
total floor by \(6^{\omega(d)}\le\tau_6(d)\).
It is power-small on \(M/L^2\) since \(D^2=N^{.998}\).

For the denominator in (2), normalize its unrestricted
positive Euler product to a probability distribution. For
\(p\le z\) the event \(p\mid d\) is then independent with
probability \(\nu_N(p)/p\). This is a model **only** for
the positive Selberg denominator, not for prime factors
of \(x,y\). The normalized sum \(X_N=(\log d)/\log z\)
converges in law, uniformly through the individual even targets,
to the positive law with Laplace transform
\[
             \mathcal L(s)=
       \exp\left(2\int_0^1\frac{e^{-st}-1}{t}\,dt\right).
\]
In fact after expanding the logarithm of the finite product,
the quadratic error tends to zero for each fixed real \(s\),
by \(\sum_p(\log p)^2/p^2<\infty\).
The differences at \(p\mid N\) cost at most a constant
times \((\log z)^{-1}\sum_{p\mid N}(\log p)/p=o(1)\)
uniformly: primes \(p\le L^2\) cost \(O(\log L)\) in the
numerator by the prime log harmonic, and larger ones cost
at most \(L/L^2\). The remaining linear sum gives the integral
by the ordinary prime log harmonic; its integrand extends
continuously after dividing by \(t\) at zero. The same proof
works for characteristic functions, giving weak convergence.

This limiting law has density \(e^{-2\gamma_E}\rho_2(u)\)
on \(u>0\). To verify the exact normalization, differentiate
the transform:
\(-\mathcal L'(s)=2\mathcal L(s)(1-e^{-s})/s\).
Thus \(u\,d\mu(u)\) for the limiting law \(\mu\) is the
convolution of \(2\,d\mu\) with the uniform **density**
\(1_{[0,1]}dt\). This gives a density away from zero;
\(\mathcal L(s)\to0\) excludes any atom at zero. On \(0<u\le1\)
the density is a constant times \(u\), by the integral equation.
As \(s\to+\infty\), \(\mathcal L(s)\sim e^{-2\gamma_E}s^{-2}\),
so that constant is \(e^{-2\gamma_E}\).
The density is continuous, and with \(\rho_2(u)=u\) on
\([0,1]\), its continuation satisfies
\[
       \frac{\rho_2(u)}u
           =1-2\int_1^u\frac{\rho_2(t-1)}{t^2}\,dt\quad(u\ge1).
                                                                    \tag{3}
\]
In particular \(\rho_2(u)/u\) is nonnegative and decreasing.
The unrestricted Euler product normalizes (2) exactly by
\(\prod_{p\le z}(1-\nu_N(p)/p)^{-1}\).
The inverse product is
\((1+o(1))\,e^{-2\gamma_E}\mathfrak S(N)/(a^2L^2)\)
by Mertens and the two actual roots. Primes \(p\mid N\)
above \(z\) affect the normalized product only by
\(1+o(1)\), since their reciprocal sum is
\(O(L/z)\). Therefore (2) gives
\[
             |\mathcal B|\le
           \left(\frac1{a^2\int_0^{\theta/a}\rho_2(u)\,du}
                        +o(1)\right)\frac{M}{L^2}.               \tag{4}
\]
No prime ranks of actual rows have entered this upper.

## 2. Both genuine source marginals

For an individual integer \(n\) in the central region, let
\(E_t(n)\), \(0\le t\le1\), be the indicator that it is
squarefree of exact rank 2 or 3, all factors exceed \(z\),
and \(H(n)/\log n>t\). Define \(m_t\) to be its ordinary
angular mass, normalized by \(\sum \log n\,E_t(n)\)
divided by the genuine spatial length. We will only use lower
bounds for \(m_t\) from finite boxes **strictly** inside the
amplitude event.

For each such fixed finite-box source \(E\) the actual
opposing rough count on the same central \(J\) has lower
\[
 \#\{x\in NJ:(x,N)=1,\ x\in E,\ P^-(N-x)>z\}
 \ \ge\
      \left(k m(E)+o(1)\right)M/L^2,\qquad
 k=\frac2\theta\log(\theta/a-1).                                  \tag{5}
\]
This is true below-root product BV and the lower dimension-one
linear sieve at level \(D=N^\theta\) and threshold \(N^a\):
on each of the bounded-rank actual prime-product cells choose
one genuine prime slot and group the rest in the independent
divisor-bounded coefficient, as in
[the physical product-source marginals in the rank-joint proof](../exact_rank_joint/Proof.md).
The literal residue is \(N\bmod d\); the reduced mean keeps
the source and target units on \(Nx\).
At primes outside \(Nx\) the sieve density is \(1/(p-1)\),
and at excluded primes there is no root. Because the source
factors are polynomially large, their omission from the
local product costs \(1+o(1)\), uniformly on these fixed
cells. The prime product main mass is \(|J|N\,m(E)/L\).
The lower coefficient at \(\theta/a\in(3,4)\) is
\(e^{-\gamma_E} f_{\rm lower}(\theta/a)/a
=(2/\theta)\log(\theta/a-1)\), with the genuine singular
series and \(1/L\). Actual large squares on either stipulated
rough product are power-small; no unspecified prime
indicator is supplied on the rough receiver. The exact same
argument holds for the other coordinate on \(1-J\), with
the same \(m(E)\) and spatial length. In both orientations the
count belongs to the same ambient \(\mathcal B\).

The two positive ranks in the present profile have a strict
true score sign. Rank two gives \(1-F(t_1)\) in normalized
own-log angles, at least \(1-F(.15)>.545\) in the limit.
For rank three with a giant, the other two angles \(u,v\)
give \(1-F(u)-F(v)+F(u+v)\). The sextic is convex on
\([.15,.5]\), so this is minimized at \(u=v=.15\);
the value is exactly \(.1544535\). With no giant,
put \(s_i=1-2u_i\in[0,.7]\); they sum to 1 and
\(F(u_i)=s_i^4(11-7s_i^2)/4\). The ratio to \(s_i\)
is increasing on that interval and is \(<.65\) at \(.7\),
so the rank-three score is at least \(.35\).
These pointwise inequalities have slack for the true
own-log changes. All such positive rows have \(Q=0\);
the .003 cut and the medium \(W\) also do not change them.
In particular \(S=H\) on each arm of \(\mathcal E\).

## 3. Weighted actual intersection, and removal only once

For each \(j=1,\ldots,200\) let \(t_j=j/200\).
The checker uses a lower \(\underline m_j\) from genuine,
finitely many ordinary angular boxes inside \(E_{t_j}\).
The mesh is \(1/1000\). The ordered angle density with an
outer log weight is \(1/\prod u_i\), since sorting cancels
the \(1/r!\) factorial. In rank 2 use the smaller angle
cell in \([.15,.5]\), score lower \(1-F(u_{\rm low})\),
and lower density obtained by enlarging both denominator
angles to their individual upper endpoints.
For rank 3 in smallest/smaller cells of lower endpoints
\(u,v\), require the whole box to be ordered
\(u_1\le u_2\le u_3=1-u_1-u_2\).
Writing \(\psi(t)=F(t)-F(1-t)\), the score is
\(1-\sum_i\psi(u_i)\) and \(\psi\) is decreasing. Use the
lower endpoints \(u,v,1-u-v-2/1000\) for its lower.
For the density enlarge the three denominator angles
to their respective upper endpoints. Only boxes whose
score lower is **strictly** above the chosen amplitude
are counted. The actual own-log and target-log angles
differ by \(O_J(1/L)\), so for fixed boxes and strict
amplitude gaps the genuine \(E_{t_j}\) event is retained;
equivalently use small interior fences and then let their
widths go to zero in the true ordinary marginals.
All genuine squares on this support are power-small.

For each fixed pair of amplitude thresholds, (4) and (5)
are applied to actual subsets of the same \(\mathcal B\).
Inclusion--exclusion gives an actual intersection lower
\[
 \#\{(x,y)\in\mathcal E:E_{t_j}(x)E_{t_\ell}(y)=1\}
 \ge\left(
    \left[k(\underline m_j+\underline m_\ell)-C_{\mathcal B}
          \right]_++o(1)\right)M/L^2,\quad
       C_{\mathcal B}=\frac1{a^2\int_0^{\theta/a}\rho_2(u)\,du}.
\]
On each genuine row, sum the marked amplitude indicators
with widths \(1/200\) on each arm: each such sum is at most
the original positive weight divided by its own \(\log n\).
Thus the sum over the 200-by-200 ordered threshold grid
is a lower for the **actual** weighted intersection in (1),
after multiplying by \(L^2(1+O_J(1/L))\).
There are only finitely many fixed-box comparisons;
their errors are taken after this fixed grid, not over a
moving family of sieve levels or angles.

The [rational checker](check_rough_positive_credit.py)
computes a lower integral in (4) by (3), using \(1/30000\)
tiles. With \(f(u)=\rho_2(u)/u\), the integrand of its
decrement on \([u_i,u_{i+1}]\) is
\(2(t-1)f(t-1)/t^2\); the extrema of its elementary factors
and the earlier interval endpoints of decreasing \(f\)
give rigorous upper and lower recursions. Integrate
\(u f(u)\) by the lower right-endpoint \(f\) value with
exact \(\int u\,du\). It yields \(C_{\mathcal B}<15.612\).
The same checker computes \(k\) from the rational lower
series for the logarithm, and uses 350 rank-two and
25,025 rank-three ordinary boxes. The resulting outward
lower for the weighted block is
\[
    \frac1{200^2}\sum_{j,\ell}
          [k(\underline m_j+\underline m_\ell)
                   -C_{\mathcal B}]_+ \ >\ .470 .
\]
Here the actual reflected summations were used in both
marginals; only the ordinary one-integer cell integrals
are numerical. Finally \(\langle S,S\rangle\) is exactly
the block sum on \(\mathcal E\) plus \(C_{\rm other}\).
Add the block's proved lower to the same existing .257
coefficient, without adding or changing any overlap or
prime term. This proves (1).
