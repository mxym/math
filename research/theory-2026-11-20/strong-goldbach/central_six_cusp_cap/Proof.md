# A \(0.436\) central cap for the adverse six-factor part of the same cusp

Let \(N=2x\) be even, \(L=\log x\), and \(J=xJ_0\) for
a fixed nonempty interval \(J_0\subset[1,4/3]\).
This ensures \(J\subset[N/2,2N/3]\), in the central range of the
[genuine angular prime upper](../AngularPrimeDomination.md).
Write \(P=N-y\), and define the same \(F(y)\) as in the
[direct true cusp proof](../true_even_cusp_rank_tail/Proof.md),
with \(K(y)=-L F(y)/2\) on even squarefree \(y\).
Then unconditionally
\[
 \limsup_{\substack{N\to\infty\\N\ \mathrm{even}}}
 \frac{1}{|J|\mathfrak S(N)}
        \sum_{\substack{y\in J,\ P=N-y\ {\rm prime}\\
                         y\ {\rm squarefree},\ \omega(y)=6}}
                    \log P\,(-K(y))_+ < .436 .             \tag{1}
\]
In particular in the normalization of the full \(F\)-sum used
in that central binary identity the positive six-factor cost
is \(<.872\,|J|\mathfrak S(N)\) in limsup. Imposing the actual
\(x^{1/\ell}\)-rough gate from that identity only decreases the
positive part bounded here. The combined low-even signed
bound is still unproved: notably the polynomial-size
semiprime contribution \(2\log P^-(y)\) is not bounded by
(1), and ranks above six are not included.

## 1. Same sign and same reference

For a homogeneous degree-one angular score \(B(t)\) on \(k\)
prime lengths write
\[
 I_k(B)=\frac{1}{k!}\int_{\substack{t_i>0\\\sum_i t_i=1}}
             B(t)\frac{dt_1\cdots dt_{k-1}}{\prod_i t_i}.
\]
Here the last coordinate is eliminated by \(\sum t_i=1\).
For the six-factor kernel
\[
 K(t)=\sum_{A\subseteq[6]}(-1)^{|A|}
                    \min\!\left(0,\sum_{i\in A}t_i
                                        -\tfrac12\sum_i t_i\right)
\]
one has \(K(y)=L K((\log p_i)/L)\) on the six distinct actual
factors of \(y\). This is the **same** symmetric linear
kernel, not one of the higher-degree or other cutoff scores.
In [SixPrimeNegativeSector, equation (6)](../SixPrimeNegativeSector.md),
the exact signed reference is
\[
 -I_6(K)=\frac{\pi^4\log2}{120}-\frac{\pi^2\zeta(3)}8
                                    +\frac{15\zeta(5)}{16}
                                    <.051800 .             \tag{2}
\]
We use the existing rational bound there. Since the positive
and negative parts are integrable (pair subsets across the
smallest coordinate to bound \(|K|\) by a constant times its
length),
\[
                  I_6((-K)_+)=I_6(K_+)-I_6(K).            \tag{3}
\]
The signed value in (2) is **only** an ordinary angular
integral; it is not an asymptotic of any signed actual
prime correlation. We will apply a genuine sieve upper to
the nonnegative angular weight \((-K)_+\) only.

The earlier full-interval bound uses \(I_6(K_+)\le .1\)
and angular upper factor 4. Here an exact finite upper
certificate gives
\[
                           I_6(K_+)<.063658.              \tag{4}
\]
Together with the audited \(200/53\) sieve factor on the
fixed central source, (2)--(4) sharpen the earlier numerical
bound in this narrower range.

## 2. Positive tent and finite ratio-box upper

Let \(a\le b\le c\le d\le e\le f\) be the six ordered lengths
and \(u=(a+b+c+d+e-f)/2\). The largest-factor peel of
[OneSidedLargestFactor](../OneSidedLargestFactor.md) gives
\(K/2\) as the five indicated differences of the hinge
\(u_+\). The first two form the nonnegative tent
\[
 {\cal T}_{a,b}(v)
        =\max\{0,\min(v,a,b,a+b-v)\}
        =\mathbf 1_{[0,a]}*\mathbf 1_{[0,b]}(v).
\]
All two-fold shifts among \(c,d,e\) vanish, because
\(u\le(a+b+c+d)/2\le c+d\); equality has zero value. Thus
\(K/2={\cal T}_{a,b}(u)-{\cal T}_{a,b}(u-c)
     -{\cal T}_{a,b}(u-d)-{\cal T}_{a,b}(u-e)\), and in
particular
\[
                         K_+\le2{\cal T}_{a,b}(u).          \tag{5}
\]
This uses the established exact six-factor formula rather
than bounding the absolute value of individual hinge
terms.

Use the descending ratio coordinates of
[SixPrimeNegativeSector, §2](../SixPrimeNegativeSector.md).
Set the unnormalized largest length to 1 and successive
ratios to \((r,D,C,B,A)\), all uniform coordinates of
integration on \([0,1]\). For each fixed \((D,C,B,A)\)
put
\[
 d=D,\quad c=DC,\quad b=DCB,\quad a=DCBA,\quad
 H=1+d+c+b+a .
\]
The unnormalized six lengths are
\((1,r,rd,rc,rb,ra)\). The simplex normalization has
Jacobian \((1+rH)^{-6}\); it cancels the product of the
normalized prime denominators, except the extra
\(1/(1+rH)\) from homogeneity of \(K\).
In log-ratio coordinates the reciprocal Jacobian is
\(\prod_i 1/U_i=1/(ra)\), since the successive ratios
multiply to the smallest unnormalized length.
Consequently (5) gives the following upper after
integrating the first ratio. Put \(v=(H-1/r)/2\);
then \(dr=2(H-2v)^{-2}dv\), and
\[
 \int_0^1\frac{K_+(1,r,rd,rc,rb,ra)}{ra(1+rH)}\,dr
    \le \frac{2}{a}\int_0^{a+b}
        \frac{{\cal T}_{a,b}(v)}{(H-2v)(H-v)}\,dv .
\tag{6}
\]
There is no harm in extending the \(v\)-interval to the
tent support: the denominators are positive there, with
\(H-2(a+b)=1+d+c-a-b\ge1\).
Null boundary cases \(a=0,b=0\) are treated by the upper
formula below, which has no such division.

By the exact convolution defining the tent, (6) becomes
\[
  2b\int_{[0,1]^2}
      \frac{d\xi\,d\zeta}
     {\{1+d+c+a(1-2\xi)+b(1-2\zeta)\}
      \{1+d+c+a(1-\xi)+b(1-\zeta)\}}.                     \tag{7}
\]
Call the two braces \(D_1,D_2\).
For fixed ratios the integrand before multiplying by \(2b\)
is convex in each \(\xi,\zeta\): it is the function
\(1/[(H-2v)(H-v)]\) of \(v=a\xi+b\zeta\), which is
increasing convex on the relevant interval. Use a
composite chord upper in each coordinate on a grid
\(h=4\). Its weights are \(1/(2h)\) at the two endpoints
and \(1/h\) at the other nodes; the tensor product is
an upper bound by successive one-dimensional convexity.

At each of these nodes partition the four outer ratios
\((D,C,B,A)\) into cubes of side \(1/n\), \(n=32\).
To integrate on a cube, bound \(D_1,D_2\) below by their
true individual minima on the cube, and integrate the
positive numerator \(b=DCB\) **exactly**, by its
product of midpoints. Both minima have closed endpoint
rules, so no interval dependency is ignored:
\[
 D_1=1+D\big(1+C\{1+B[(1-2\zeta)+A(1-2\xi)]\}\big).
\]
Choose the \(A\)-endpoint minimizing the innermost linear
term, then the \(B\)-endpoint according to the sign of
that term, then \(C\), then \(D\) according to the
successive signs. This is exact because each outer
multiplier is nonnegative and the chosen inner endpoint
is independent of the actual outer values. For \(D_2\)
all the corresponding coefficients are nonnegative,
so every lower endpoint minimizes it. In particular
none of these divisions can encounter a zero denominator.
The cube integral upper is its volume \(n^{-4}\) times
the exact numerator average divided by the two lower
denominators, with the tensor chord weights inserted.

The [integer checker](check.py) accumulates all these
nonnegative rational terms with upward rounding to
multiples of \(10^{-14}\) *before* multiplying by the
outer cube volume. It returns the integer numerator
\(6674950756087897698\) over \(10^{14}\cdot32^4\), which is
less than \(63658/10^6\). The operations certify a
deterministic upper for (7), not a sample or a numerical
estimate of the sign of the remaining cells. This proves
(4).

## 3. Actual prime normalization and remaining budget

Use the [angular domination inequality (1)](../AngularPrimeDomination.md)
on the nonnegative \(L(-K)_+\) weight, with a fixed positive
least-factor angular cutoff \(\kappa\), then take the
central interval \(J\) by smoothing its upper endpoints
inside that theorem's central range. The weight on
factor angles is continuous on the cutoff simplex,
and any repeated-label or prime-power errors on the
source are handled by that theorem. Its ordinary angular
mean can be computed by the fixed-box PNT there: for the
source interval \(I=[N/3,2N/3]\) it is normalized by
\(|I|\) and tends to
\((|J|/|I|) I_6((-K)_+\mathbf 1_{\min t_i\ge\kappa})\). The logs \(L\), \(\log N\),
and \(\log P\) differ by \(O(1)\) on this central range
and the normalizations agree to \(1+o(1)\).
In taking the central restriction, the two interval
endpoints are ordinary upper approximations of a bounded
independent position weight; their contribution tends
to zero by the ordinary length factor in the same
comparison. Equivalently, the proof of the angular
inequality applies to these shorter positive position
windows with the same majorant constant.

Remove the least-factor cutoff by the actual fixed-six
face estimate in equation (7) of
[SixPrimeNegativeSector](../SixPrimeNegativeSector.md).
Its error is
\(O(|J|\mathfrak S(N)\kappa(1+\log(1/\kappa))^4)\) in
limsup for this fixed \(J_0\) (the whole-interval error
there suffices). This also covers imposing the
moving rough cutoff of the direct cusp proof. Thus
(2)--(4) yield, for the actual genuine prime count in (1),
\[
 \frac{200}{53} I_6((-K)_+)
 <\frac{200}{53}(.063658+.051800)
 =\frac{57729}{132500}<.436 .
\]
We use the published, checked central \(200/53\) factor,
not the stronger preprint value mentioned in that source.
The \(0.436\) claim is central only. The new geometric bound
(4) also improves the earlier \(0.608\) *full-interval*
constant to \(4(.063658+.051800)=.461832<.462\) in its own
\(N\mathfrak S(N)\) normalization: use its unchanged
factor-4 arithmetic comparison and its actual face estimate,
not the central \(200/53\) bound outside the stated scope.
No change to a different parity score is asserted here.
Even in the present central problem this pays only one
adverse sector. No uniform low-even total below the
direct reference, or binary Goldbach proof, follows.
