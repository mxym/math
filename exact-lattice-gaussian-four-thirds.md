# Sharp four-thirds exact Gaussian conversion on every fixed lattice

Let \(\Lambda\subset\mathbb R^d\) be a fixed full-rank lattice and
\(\Gamma=\Lambda^*\) its Euclidean dual. Write
\(g_t(x)=t^{-d}\exp(-\pi\|x\|^2/t^2)\), and let \(D_{\Lambda,s}\)
have mass proportional to \(\exp(-\pi\|u\|^2/s^2)\) at \(u\in\Lambda\).
One observation has law \(\theta+g_t\) with unknown \(\theta\in\Lambda\).
The observer must use a single Markov kernel, not given \(\theta\), to
return exactly \(\theta+D_{\Lambda,s}\) for all \(\theta\in\Lambda\).

**Theorem.** For every fixed full-rank \(\Lambda\), there are finite
\(C_\Lambda,T_\Lambda>0\) such that the exact conversion exists whenever
\(t\ge T_\Lambda\) and
\[
                         s^2\ge \frac43t^2+C_\Lambda .                 \tag{1}
\]
Together with the [all-lattice obstruction](exact-gaussian-four-thirds-obstruction.md),
this shows that the infimum feasible squared output width is
\(\frac43t^2+O_\Lambda(1)\) on **every fixed lattice**. Both constants
may depend on the lattice and its dimension. This is an abstract
existence comparison; it does not decide feasibility at the exact
endpoint or the optimal additive constant, and it makes no claim about
efficient sampling, finite center sets, lattice quotients, or protocols.

The earlier [line](exact-gaussian-four-thirds.md) and
[triangular](exact-triangular-gaussian-four-thirds.md) constructions
give special cases by treating low shells separately. The new ingredient
is a periodic weight that works for arbitrary geometry: the squared
norm of a shortest representative of a class in \(\Gamma/2\Gamma\).
This differs from approximate randomized rounding of a Gaussian
[Peikert, Theorem 3.1 and §4.1](https://web.eecs.umich.edu/~cpeikert/pubs/pargauss.pdf)
and from the earlier [shape-dependent sufficient ratio](exact-lattice-gaussian-gap.md).
The privacy-loss formulas for an individual pair of translates in
[Su et al., §4.5](https://arxiv.org/html/2610.02414v1#S4.SS5) do not
address one exact kernel working simultaneously at all lattice centers.

## 1. A periodic weight and a boundary point

For \(j\in\Gamma\), put
\[
           \mu_j=\min_{w\in\Gamma}\|j-2w\|^2 .
\]
There are only \(2^d\) possible classes, so \(M=\max_j\mu_j<\infty\).
We have \(\mu_j\le\|j\|^2\) and
\(\mu_i\le\mu_j+\mu_{i-j}\): choose shortest representatives of
the latter classes and choose the sign of one to make the cross
inner product nonpositive, which is allowed modulo \(2\Gamma\). It
follows that
\[
    B_{ij}(j):=\|i-j\|^2+\mu_j-\mu_i\ge0.
\]
More generally let \(B_{ij}(x)=\|i-x\|^2-\|j-x\|^2+\mu_j-\mu_i\).
The closed weighted cell where \(j\) is a minimizer of
\(\|i-x\|^2-\mu_i\) is convex, because each \(B_{ij}(x)\) is
affine in \(x\). It contains \(j\), by the preceding inequality.
If \(r=j-2w\) is a shortest representative, it also contains \(2w\):
the weighted score there is zero for \(j\), and nonnegative for
every \(i\) by the definition of \(\mu_i\).

Let \(\mathcal V\) be the Euclidean Voronoi cell at zero of \(\Gamma\).
Fix a finite symmetric set \(F\subset\Gamma\setminus\{0\}\) of defining
normals for \(\mathcal V\), enlarged by the signs of a lattice basis.
Such a set exists: the basis inequalities already bound a compact
polytope, and sufficiently long lattice vectors cannot contribute on it.
Then
\[
                  4\mathcal V=\{x:x\cdot v\le2\|v\|^2
                                             \ \text{for all }v\in F\}.
\]
Call \(j\ne0\) low if it is in the interior of \(4\mathcal V\); there
are finitely many such \(j\). For each low \(j\) choose a shortest
representative \(r\) of its class with \(r\ne j\). This is possible
since if \(j\) itself is shortest we may use \(-j\). Write \(j-r=2w\),
so \(w\ne0\). The point \(2w\) is not in the interior of \(4\mathcal V\):
the valid Voronoi inequality from \(w\) is an equality there.
The segment from \(j\) to \(2w\) therefore hits a boundary point
\(\alpha_j^0\), which lies in the weighted cell of \(j\). Choose
\(v_j\in F\) active at that point and put \(h_j=\alpha_j^0-j\).
Then
\[
                 \alpha_j^0\cdot v_j=2\|v_j\|^2,\qquad
                 h_j\cdot v_j>0,\qquad
                 \|h_j\|^2\le\mu_j.                                   \tag{2}
\]
For every remaining nonzero \(j\) (the high set), put
\(\alpha_j^0=j\), \(h_j=0\), and choose \(v_j\in F\) maximizing
\(\Delta_j^0=2j\cdot v_j-4\|v_j\|^2\). Then \(\Delta_j^0\ge0\);
these maxima tend to infinity as \(\|j\|\to\infty\) because \(F\)
includes a signed basis. Define \(\Delta_j^0=0\) on the low set.
Make all choices in opposing pairs, so the choices of vectors change
sign under \(j\mapsto-j\).

We will use one elementary bound at a weighted minimizer. If \(u\)
minimizes \(\|i-x\|^2-\mu_i\) and \(v\in\Gamma\), comparison with
\(u\pm2v\), which have exactly the same weight, gives
\[
                         |(u-x)\cdot v|\le\|v\|^2 .                    \tag{3}
\]

## 2. Gaussian-null corrections and their weighted matrix

Put \(D=s^2-t^2>0\), \(A=s^2/D=4-\delta\), and
\(\omega=(1-1/A)D\). We work with \(D\ge1\) and \(0<\delta\le\delta_0\),
where \(\delta_0\) will depend only on the lattice. Let
\(\varepsilon,\kappa>0\) be small fixed constants, to be specified below.
Set
\[
 \alpha_j=\alpha_j^0-\varepsilon\delta h_j,\quad
 \zeta_j=\alpha_j-A v_j,\quad q_j=\|\alpha_j-j\|^2,\quad
 \phi_j=(1-\kappa\delta)\mu_j,\quad
 \Delta_j=(A-1)(2\alpha_j\cdot v_j-A\|v_j\|^2).
\]
For high \(j\), \(\Delta_j=(A-1)(\Delta_j^0+\delta\|v_j\|^2)\).
For low \(j\), \(\Delta_j=(A-1)\delta(\|v_j\|^2-2\varepsilon h_j\cdot v_j)\),
which is nonnegative when \(\varepsilon\) is sufficiently small. We
will choose \(\kappa<\varepsilon\), and by (2) and small \(\delta_0\)
we then have \(0\le q_j\le\phi_j\) for all \(j\).

Define
\[
 U_j(x)=e^{2\pi i\alpha_j\cdot x}
                 -e^{-\pi D\Delta_j}e^{2\pi i\zeta_j\cdot x}.
\]
We have \(\|U_j\|_\infty\le2\). For \(u\in\Lambda\), these functions
have zero integral against \(g_{\sqrt\omega}(x-u/A)\): the phases
differ by \(e^{2\pi i v_j\cdot u}=1\), and the difference of the two
Gaussian damping exponents is
\(\omega(\|\alpha_j\|^2-\|\zeta_j\|^2)=D\Delta_j\).
For a coefficient vector \(c\), the nonzero lattice Fourier coefficients
of \(g_{\sqrt D}(1+\sum_j c_j U_j)\) vanish if
\[
 T c=f,\qquad
 T_{ij}=e^{-\pi D\|i-\alpha_j\|^2}
        -e^{-\pi D(\|i-\zeta_j\|^2+\Delta_j)},\qquad
 f_i=-e^{-\pi D\|i\|^2}.
 \tag{4}
\]
Both row and column indices in this system are the nonzero points
of \(\Gamma\). Write \(c_j=e^{-\pi D(\phi_j-q_j)}z_j\), and multiply
row \(i\) by \(e^{\pi D\phi_i}\). The new matrix \(W\) is the
primary exponential minus the companion exponential, with exponents
in units of \(\pi D\) equal to
\[
 \begin{split}
 P_{ij}&=\|i-\alpha_j\|^2-q_j+\phi_j-\phi_i,\\
 Q_{ij}&=\|i-\zeta_j\|^2-q_j+\phi_j-\phi_i+\Delta_j .
 \end{split}                                                         \tag{5}
\]
In particular \(P_{jj}=0\) for all \(j\).

## 3. The positive contact gaps

We prove that for choices depending only on the fixed lattice, the
column-sum estimate
\[
                \|W-I\|_{\ell^1\to\ell^1}
                     \le K_\Lambda e^{-c_\Lambda D\delta}
          \qquad(D\delta\ge1,\ 0<\delta\le\delta_0)                     \tag{6}
\]
holds. We use squared distances throughout.

**Low primary terms.** At \(\delta=0\),
\(P_{ij}=B_{ij}(\alpha_j^0)\ge0\). At an equality, the derivative
with respect to \(\delta\) is
\[
            2\varepsilon(i-j)\cdot h_j+\kappa(\mu_i-\mu_j)
                     =\varepsilon B_{ij}(j)+\kappa(\mu_i-\mu_j).
 \tag{7}
\]
This uses the affine dependence of \(B_{ij}\) along \(j+h_j\).
If \(i\ne j\) and \(B_{ij}(j)=0\), the second term is
\(\kappa\|i-j\|^2>0\). Otherwise the first term is strictly positive.
For fixed \(\varepsilon>0\), choosing \(\kappa>0\) sufficiently small
makes the derivative positive at all non-diagonal primary contacts.
There are only finitely many contacts, since the low columns are
finite and the \(\mu_i\) are bounded.

**Low companion terms.** At zero, \(Q_{ij}=B_{i+4v_j,j}(\alpha_j^0)\ge0\)
by periodicity of the weights. At equality put
\(\rho=i+4v_j-\alpha_j^0\). The derivative is
\[
   3\|v_j\|^2-2\rho\cdot v_j
       +\varepsilon\big(2\rho\cdot h_j+2\|h_j\|^2-6h_j\cdot v_j\big)
       +\kappa(\mu_i-\mu_j).
 \tag{8}
\]
The first two terms have sum at least \(\|v_j\|^2>0\) by (3)
applied to the minimizing point \(i+4v_j\) at \(\alpha_j^0\).
First choose \(\varepsilon>0\) small enough for these finitely many
contacts and for \(\Delta_j\ge0\); then choose \(\kappa\) small enough
for (7), (8), and \(\kappa<\varepsilon\). This establishes strict
positivity of the derivatives at all relevant low contacts, including
companion contacts on the diagonal.

For either of the two low exponent families, sufficiently large
\(\|i\|\) gives a lower bound \(c\|i\|^2\), uniform over small \(\delta\),
since all low frequencies, weights and \(q_j\) are bounded and
\(\Delta_j\ge0\). In the remaining finite set, any positive value at
zero stays bounded away from zero, and the contact derivatives give a
lower bound \(c\delta\) for small \(\delta>0\). In the primary family
exclude \(i=j\). Summation bounds these low column contributions
by \(K e^{-cD\delta}\), since a fixed lattice Gaussian tail with
\(\|i\|\) bounded away from zero is exponentially small in \(D\).

**High primary terms.** Here \(q_j=0\) and \(\alpha_j=j\). If \(i\ne j\),
\[
         P_{ij}=(1-\kappa\delta)B_{ij}(j)
                       +\kappa\delta\|i-j\|^2
                \ge\kappa\delta\|i-j\|^2 .
\]
The sum over \(i\ne j\) is uniformly exponentially small in \(D\delta\).

**High companion terms.** Let \(v=v_j\) and \(r=i-j+4v\in\Gamma\).
For large \(\|r\|\), the square \(\|r-\delta v\|^2\), minus at most
\(M\) from the weights, gives a lower bound \(c\|r\|^2\) independently
of \(j\), because \(v\) ranges over a fixed finite set. For bounded
\(\|r\|\), a sufficiently large \(\Delta_j^0\) gives \(Q_{ij}\ge1\)
uniformly by \(\Delta_j\ge(A-1)\Delta_j^0\). Only finitely many
\(j\) have bounded \(\Delta_j^0\). In these remaining cases, at zero
\[
               Q_{ij}=\|r\|^2+\mu_j-\mu_i+3\Delta_j^0\ge0 .
\]
Indeed \(\mu_i=\mu_{i+4v}\), so the first three terms are nonnegative
by the \(j\)-centered weighted inequality. An equality requires
\(\Delta_j^0=0\) and \(i+4v\) a weighted minimizer at \(j\).
Then the derivative is \(3\|v\|^2-2r\cdot v+\kappa(\mu_i-\mu_j)\),
at least \(\|v\|^2\) by (3) and \(\mu_i-\mu_j=\|r\|^2\).
Consequently \(Q_{ij}\) is bounded below by \(c\delta\) in the
finite part for small \(\delta>0\); together with the uniform Gaussian
tail this proves the companion column estimate. All the sums use the
fact that \(\sum_{r\ne0}e^{-a\|r\|^2}\le K_\Gamma e^{-b_\Gamma a}\)
for \(a\) bounded away from zero, by taking out half of the
shortest-vector exponential. This completes (6).

## 4. Exactness, positivity, and the stated range

The rescaled right-hand side \(f_i'=e^{\pi D\phi_i}f_i\) satisfies
\(\|f'\|_1\le K_\Lambda e^{-c_\Lambda D\delta}\), since
\[
             \|i\|^2-\phi_i
             =(1-\kappa\delta)(\|i\|^2-\mu_i)+\kappa\delta\|i\|^2
             \ge\kappa\delta\|i\|^2.
\]
Choose \(L_\Lambda\) large enough that for \(D\delta\ge L_\Lambda\)
the Neumann inverse in (6) has norm at most two and the solution
\(z=W^{-1}f'\) satisfies \(2\|z\|_1<1\). As \(q_j\le\phi_j\),
the solution \(c\) of (4) then has \(2\|c\|_1<1\). The real
matrix and opposing-pair symmetry give \(c_{-j}=c_j\) real.
Hence \(p_0=g_{\sqrt D}(1+\sum_jc_j U_j)\) is real and strictly positive,
with a constant-times-Gaussian envelope. Its \(\Lambda\)-periodization
is continuous and constant, by (4) and Fourier uniqueness. Set
\(p=p_0/\int p_0\) and \(V=\operatorname{covol}(\Lambda)\); then
\(\sum_{u\in\Lambda}Vp(u-x)=1\), so \(K(u\mid x)=Vp(u-x)\)
defines a Markov kernel.

Completing squares gives
\(g_t(u-x)g_{\sqrt D}(x)=g_s(u)g_{\sqrt\omega}(x-u/A)\).
By the zero integrals of \(U_j\) and absolute convergence,
\((g_t*p_0)(u)=g_s(u)\) for \(u\in\Lambda\).
The masses of the kernel output at center zero are therefore
proportional to \(\exp(-\pi\|u\|^2/s^2)\); they sum to one.
Lattice equivariance proves the same law after every unknown center
translation. There is no limiting approximation in this conclusion.

Taking \(s^2=\frac43t^2+C_\Lambda\) gives
\(D\delta=3s^2-4t^2=3C_\Lambda\); choose \(3C_\Lambda\ge L_\Lambda\).
For large \(t\) we have \(D\ge1\) and \(\delta\le\delta_0\).
For any larger \(s\), first add independent continuous Gaussian noise
to reach input width \(\widetilde t\) with
\(\widetilde t^2=\frac34(s^2-C_\Lambda)\ge t^2\), then apply the
equality case at that width. The companion verifier checks periodic
weights, exact Voronoi segment contacts and first derivative signs
in fixed rational Gram examples. The uniform lattice-tail argument
and the Neumann inverse above are an analytic proof, not extrapolated
from those examples.
