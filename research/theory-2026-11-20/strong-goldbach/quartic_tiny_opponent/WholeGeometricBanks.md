# Full signed geometric-bank crosses for the compensated quartic

Use the same central fixed interval \(J\Subset(1/3,2/3)\), even target
\(N\), target units \((x,N)=1\), \(x+y=N\), \(L=\log N\), and
\(M=|J|N\mathfrak S(N)\) as in [the original small-factor cross](Proof.md).
Keep literally the same quartic score \(H\) and compensated score
\(\widetilde H=H+R+W_1+W_2\), including the actual cuts and weights of
the three compensating banks. Put
\[
 b_0=.004/k,\qquad b_1=.018/k,\qquad
 I_0=(.012,.076],\qquad I_1=(.019,.058].
\]
Write \(\mathcal G(I,c)\) for the central squarefree \(y\) with
\(P^-(y)>N^c\) and at least one **actual** prime factor \(p\mid y\)
with \(\log p/L\in I\). There is no sign condition in this definition.

**Theorem.** For every sufficiently large fixed integer \(k\), uniformly
as the even target grows, the two actual signed sums of
\(\widetilde H(x)\widetilde H(y)\) on
\[
 \begin{array}{lll}
 \mathcal D_0:&P^-(x)\le N^{b_0},& y\in\mathcal G(I_0,b_0),\\
 \mathcal D_1:&N^{b_0}<P^-(x)\le N^{b_1},&y\in\mathcal G(I_1,b_1)
 \end{array}
\]
are greater than \(14 b_0 M\) and \(9.3(b_1-b_0)M\), respectively.
The two contributions sum to \(>.186M/k\) in this orientation.
The same assertion holds on the reflection, and all four regions are
disjoint. These regions include the old negative-source regions.
The new bounds **replace** the old bounds on that union; they are not
additional credit to the old subregions. No sign is claimed for the
complement, including the small-factor rows on which the opposite
geometric hit fails.

## 1. An actual ordinary signed geometric mass

Set \(f(t)=P(t)1_{t<1/2}\) for \(t\ge0\), where
\[
 P(t)=1-t-11t^2+24t^3-12t^4,
 \qquad P'(t)=-1-22t+72t^2-48t^3 .
\]
Let \(V_f\) denote the divisor profile before subtracting \(\Pi\).
The asymptotic calculation below is unchanged for own-log versus
target-log angles, by the [absolute paired and angular estimates
for this detector](../halfzero_detector/Proof.md). We justify the
one-variable limiting calculation as well.

Fix an interval \(I=(A,B]\) with \(0<A<B<1/2\). For a fixed
\(0<\eta<A\), impose squarefreeness and \(P^-(n)>N^\eta\).
The exact ordinary mean of \(V_f\) on this support, divided by the
length \(|J|N\) of the spatial interval, tends to the usual angular
integral at total angle 1. In fact the rank is at most \(1/\eta\).
Label the actual distinct factors as ordered slots and divide by
the corresponding factorial. For each angle profile, partition into
fixed boxes and use the prime number theorem on the last factor in
the actual product interval and reciprocal prime harmonics on the
other factors. The last slot contributes the factor \(1/u\) in the
angular measure at its remaining angle \(u\): the weighted
\(\log n\) count in a spatial interval has density
\(\log n/\log p_{\rm last}=1/u+o(1)\). This also applies with the
Boolean no-hit restriction on the genuine factor slots and with a
specified subset carrying the Möbius sign. Boundaries of the angular
boxes and the fixed half-open bank can be refined using these same
positive prime harmonics. The genuine product spatial interval stays
macroscopic during the fixed-box limit, with its normalized angle
\(\log n/L=1+O_J(L^{-1})\). Repeated primes are power-small after
the floor is fixed. The uniform omission of actual primes dividing
\(N\) is also power-small, by at most \(O(L)\) such labels
of size \(>N^\eta\), or directly by the corresponding union of
divisibility classes. No mean is taken over targets.

To let \(\eta\downarrow0\) in the ordinary mean, one only needs the
one-variable version of the detector's absolute Fourier bound.
In its notation, for the genuine positive weight
\(W_\xi(n)=\prod_{p\mid n}|1-e^{i\xi\log p/L}|\), the corrected
[Henriot theorem](https://doi.org/10.1017/S0305004114000280)
on the single primitive form \(n\) gives
\[
 \sum_{n\asymp_J N} W_\xi(n)
  \ll_J \frac NL(2+|\xi|)^c
\]
for a fixed \(4/\pi<c<2\), with the uniform growth and prime harmonic
bounds in the detector proof. If a genuine \(p\le N^\eta\) divides
\(n\), substitute \(n=pm\), extract its factor once, and put value 1
at every positive \(p\)-power in the remaining weight. The same
long-interval bound then has the extra factor
\(O_J(|1-e^{i\xi\log p/L}|/p)\). This also bounds the squarefree
restricted sum. Summing the actual marked prime harmonic by
equation (4) of the detector proof and integrating
\(\widehat f(\xi)=O((2+|\xi|)^{-3})\) proves that the ordinary
absolute weight of the excluded tiny factors is \(O_J(\eta^\gamma N)\)
for one fixed \(\gamma>0\). The same argument works with bounded
spatial Fourier dilation for the own-log variant. In particular
the constant is independent of the floor to which we apply it later.

Here is an exact evaluation of the limiting ordinary angular
quantity. All measures below are on the nonnegative real line;
\(\exp_*\) denotes the convolution exponential and \(\delta_0\)
the unit point mass. Write
\[
 \nu_\eta(dt)=1_{t\ge\eta}\frac{dt}{t},\qquad
 \nu_I(dt)=1_{t\in I}\frac{dt}{t},\qquad
 \sigma=\exp_*(\nu_I),\quad \tau=\exp_*(-\nu_I).
\]
The two independent groups of labels are the divisor's true labels,
with sign \(-1\) for each, and its complement's true labels, with
sign \(+1\) for each. At the angular limit for the full support the
two convolution measures are
\[
 D_\eta=\exp_*(-\nu_\eta),\qquad U_\eta=\exp_*(\nu_\eta).
\]
On the literal *no-hit* support they become
\(D_\eta*\sigma\) and \(U_\eta*\tau\): this is just
\(\exp_*(\mp(\nu_\eta-\nu_I))\) on the two sides. The factorials
are those in the preceding **ordinary prime-product** limit; no
probabilistic assumption on complementary integers is used.

The exact densities on \(t>0\) of \(D_\eta\) and \(U_\eta\) are
\(\eta^{-1}\rho'(t/\eta)\) and \(\eta^{-1}\omega(t/\eta)\), where
\(\rho\) is Dickman's and \(\omega\) Buchstab's function, and both
measures have the additional atom \(\delta_0\). For instance after
scaling to \(\eta=1\), differentiating the Laplace transform
\(\exp(\pm\int_1^\infty e^{-st}dt/t)\) gives the respective
density equations
\(t A_\pm(t)=\pm\int_{[0,t-1]}\exp_*(\pm\nu_1)(dv)\) for \(t>1\),
with zero density below 1. These give the usual initial intervals
and delay equations. We use \(\omega(t)\to e^{-\gamma_E}\),
\(\int_0^\infty\rho(t)dt=e^{\gamma_E}\), and the boundedness of
\(\omega\); see the [Hildebrand--Tenenbaum delay-equation
paper](https://tenenb.perso.math.cnrs.fr/PPP/Diff-diff_eqns.pdf)
and their [Dickman transform, (2.14)--(2.15)](https://www.numdam.org/item/JTNB_1993__5_2_411_0.pdf).
In particular \(t|\rho'(t)|\le1\) and tends to zero by the Dickman
delay equation.

For \(a\ge0\) put \(g_a(u)=(f(a+u)-f(a))/u\), with its continuous
value \(f'(a)\) at \(u=0\). Since \(D_\eta*U_\eta=\delta_0\),
\[
   \big(f(a+\cdot)D_\eta\big)*U_\eta
       = f(a)\delta_0+\big(u g_a(u)D_\eta(du)\big)*U_\eta .
\]
At any fixed \(r>0\), the density of its last term tends to
\(-f'(a)\). Indeed its part from the continuous density of
\(U_\eta\) is
\[
 \int_0^{r/\eta} v\rho'(v)g_a(\eta v)
                         \omega(r/\eta-v)\,dv ,
\]
which tends to \(e^{-\gamma_E} f'(a)\int_0^\infty v\rho'(v)dv
=-f'(a)\) by dominated convergence. The atom of \(U_\eta\) gives
\((r/\eta)\rho'(r/\eta)g_a(r)\), which tends to zero. Both
contributions are uniformly bounded, by the sup norm of \(f'\)
and the displayed Dickman bounds. These observations justify
integrating the density at \(r=1-a-b\) against
\(\sigma(da)\tau(db)\): their total variations are finite and there
is no atom at \(a+b=1\), since their only possible atom is at zero.
The term \(f(a)\delta_0\) has to be retained separately. It gives
a genuine continuous boundary density at total 1, not zero.

Thus the true ordinary no-hit limit for \(V_f\), without the
tiny floor, is
\[
 -\int_{a+b<1} f'(a)\,d\sigma(a)d\tau(b)
        + \big[(f\sigma)*\tau\big]_{\rm dens}(1).                \tag{1}
\]
At positive arguments the boundary convolution is the density
coming from the convolution series. At 1 at least two band labels
are required, so every contributing term has a continuous density,
and the absolute uniform majorant in §2 justifies its evaluation.
The same calculation with \(\nu_I=0\) gives the whole ordinary
mean \(-f'(0)=1\). On an actual hit no prime integer occurs in
the central interval, so \(H=V_f\) there. The actual hit mean for
\(H\) is therefore 1 minus (1). This subtraction precedes
compensation and is not a claim about the two-arm pair distribution.

## 2. Exact negative source masses, including all positive rows

Put \(v=\log(B/A)\), \(w=B-A\), and \(m_j=(B^j-A^j)/j\).
The untruncated first term in (1) is
\(-\mathbb E f'(X)\), where \(X\) has probability measure
\(e^{-v}\sigma\); the total signed mass of \(\tau\) is \(e^{-v}\).
Since \(X\) is the sum of a Poisson number of band labels, its
first three moments are \(w,w^2+m_2,w^3+3wm_2+m_3\).
Consequently the polynomial substitute \(-\mathbb E P'(X)\)
equals \(1+T\), where
\[
           T=22w-72(w^2+m_2)+48(w^3+3wm_2+m_3).
\]
The cutoff error in a **lower** bound for \(-\mathbb E f'(X)\)
can only come from \(X>1\). Indeed \(P'(t)=-7s+6s^3\) for
\(s=1-2t\), so \(P'\ge0\) on \([1/2,1]\). Also
\(|f'|\le7\) and \(0\le f\le1\).
Let \(r\) be the smallest integer for which \(rB\ge1\).
Three valid positive upper errors, for any \(V\ge v\), are
\[
 \begin{split}
 E_1&=\sum_{j\ge r}(1+22Bj+72(Bj)^2+48(Bj)^3)\frac{V^j}{j!},\\
 E_2&=7\sum_{j\ge r}\frac{(2V)^j}{j!},\\
 E_3&=\frac2A\sum_{j\ge r}\frac{(2V)^{j-1}}{j!}.
 \end{split}                                                     \tag{2}
\]
Here \(E_1\) bounds the bad cutoff error, dropping \(e^{-v}\le1\).
For \(E_2\), the removed region \(a+b\ge1\) requires at least
\(r\) band labels, with \(\sigma*|\tau|\le\exp_*(2\nu_I)\).
For the boundary density use
\(\|\nu_I^{*j}\|_\infty\le A^{-1}v^{j-1}\) and the same
exponential majorant, which gives \(E_3\) and also its absolute
uniform density convergence around 1. For that local statement
one may first take a fixed neighborhood of 1 small enough not to
contain any argument reachable with \(r-1\) labels. Both banks
below have \((r-1)B<1\). Thus the true ordinary hit mass for
\(H\) is at most \(-T+E_1+E_2+E_3\) in units \(|J|N\).

On these banks \(R=0\) since the hit angle is \(\le .076\).
The entire ordinary positive corrections \(W_1+W_2\) have
normalized upper mass \(.146748616+.077025550\) by
[the original compensated proof](../halfzero_detector/CompensatedDebit.md).
Using these full positive masses (not the smaller least-label
overlaps) respects every possible geometric hit. The
[exact rational checker](check_whole_geometric_banks.py) takes
\((V,r)=(1.85,14)\) and \((1.125,18)\), respectively, and bounds
each series in (2) by its first term times a rational geometric
factor. It gives \(T-E_1-E_2-E_3-.223774166>.660\) and
\(>.430\), respectively. Thus
\[
 \limsup_{N\to\infty}
  \frac{1}{M}\,\mathfrak S(N)
      \sum_{\substack{y\in N(1-J),\,(y,N)=1\\
             y\in\mathcal G(I_i,b_i)}} \widetilde H(y)
   \le -c_i+O_J(b_i^\gamma),
    \qquad (c_0,c_1)=(.660,.430).                                  \tag{3}
\]
The additional floor loss in (3) is at most the genuine ordinary
absolute tiny-factor loss from §1, since
\(|\widetilde H|\le|H|\) on these composite rows. It is harmless
after taking \(k\) large. Every positive row in the geometric
bank is included in (3).

## 3. Transfer on the original actual pair, and scope

For \(i=0,1\) use the genuine signed source
\(Z_i(y)=\widetilde H(y)1_{y\in\mathcal G(I_i,b_i)}\).
The source hypotheses of [the small-factor cross, §§1--3](Proof.md)
hold unchanged for this signed source: the genuine selected short
prime is assigned weight one over its actual number of occurrences;
on each actual finite-rank multiplicative box the profile and the
two exact tag-bank corrections have the same separated realization
as before. The short prime remains genuine and satisfies the same
Siegel--Walfisz bound; applying Fouvry's Corollary 1 for \(I_0\)
and (C.1) for \(I_1\) makes no sign assumption on the grouped
coefficient. Alternatively apply that argument separately to the
positive and negative parts of \(Z_i\). In all **absolute** errors
use \(|Z_i|\le|H|\) on actual composite rows. In particular the
fixed-depth tail uses the same two-affine Fourier estimate with
\(O_J((3e/100)^k M)\) error and fixed \(\gamma>0\) for the true
small-factor error \(O_J((b e^{-k/100})^\gamma M)\), not constants
depending on the rank of \(Z_i\).

With \(M_{Z_i}=\mathfrak S(N)\sum_{y\in N(1-J),(y,N)=1} Z_i(y)\)
the exact signed version of that transfer is therefore
\[
 \sum_{P^-(x)\le N^b}\widetilde H(x) Z_i(y)
    = \{-22b+o_{k\to\infty}(b)\}M_{Z_i}
       +o_{k\to\infty}(bM)+o_N(M).                              \tag{4}
\]
Here \(b=b_i\), or \(b=b_0\) for the **same unchanged** source
\(Z_1\). The target limit is first at fixed \(k\).
The small-factor arm remains uncorrected, with actual least prime
\(\le N^{.005}\). The source has \(|M_{Z_i}|=O_J(M)\) by the
same one-variable Fourier estimate, so the coefficient errors
remain of the displayed order. Applying (4) and (3) at \(b_0\)
proves the base claim. For the annular claim subtract (4) at
\(b_0\) from that at \(b_1\) with the same \(Z_1\).
The margins \(22\cdot.660>14\) and \(22\cdot.430>9.3\)
give the stated strict constants. Disjointness follows from the
literal least-factor inequalities: the two annular arms both
have least factor \(>N^{b_0}\), and every base or annular
region has only one side at or below its own upper least-factor
cut. This does not estimate either the geometric no-hit complement
or the remainder with both least factors above \(N^{b_1}\).
