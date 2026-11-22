# A prime-neutral quartic–quadratic comparison forces true rank three or four

Let \(N=2x\to\infty\) through the even integers, \(L=\log x\), and fix
an interval \(J_0\subset[1,4/3]\) of positive length. Put \(J=xJ_0\),
\(P=N-y\), and \(M=|J|\mathfrak S(N)\), where \(\mathfrak S(N)\) is
the ordinary Goldbach singular series, normalized to have mean 2
over even integers. In every sum the prime \(P\) is genuine.
For squarefree \(y>1\), define the literal own-root scores
\[
 A_j(y)=\sum_{d\mid y}\mu(d)
            \left(1-\frac{2\log d}{\log y}\right)_+^j,\qquad
 B(y)=A_4(y)-A_2(y).
\]

**Theorem.** There is a fixed \(\eta>0\) such that, uniformly in
sufficiently large even \(N\),
\[
 \sum_{\substack{y\in J,\ P=N-y\ {\rm prime}\\
       y\ {\rm squarefree},\ 3\le\omega(y)\le4,\ P^-(y)>x^\eta}}
     (\log P)(\log y)\,B(y)>.010\,M.                                    \tag{1}
\]
The two scores \(B(y)\) on ranks three and four are nonnegative.
In particular every such target has
\(\gg_{J_0} x\mathfrak S(N)/(\log x)^2\) representations by a
genuine prime and the product of **exactly three or four distinct
polynomially large primes**. Prime or semiprime partners do not
count in this lower bound.

This is not a lower bound on either exact rank individually, a
binary Goldbach result, or a credit against a different marked
score. In particular giant-prime triprimes and rank-four rows can
contribute to (1). Compare the earlier
[quadratic low-degree comparison](https://github.com/mxym/math/blob/main/research/theory-2026-11-20/strong-goldbach/QuadraticLowDegreeReduction.md)
on ranks two and three plus a binary-prime term, and the
[actual cubic low-rank comparison](../cubic_lowrank_gate/Proof.md)
on ranks two to four plus that prime term. The present difference
cancels the prime weight **identically** and uses a smaller
one-sided semiprime charge, then prices all higher ranks on the
same true prime source. Classical Chen counts partners with *at
most* two factors. The [tagged Chen switch](../chen_p2_cofactor/Proof.md)
also suggests a different route to an exact three-or-four union:
in its scope, requiring two distinct short prime labels rather
than one places two compulsory factors outside the rough
prime-or-semiprime cofactor. This leaves literal prescribed
tag banks, unlike (1); no priority or novelty assertion about
the unweighted rank union is made. The new numerical result
here is for the **unmarked** quartic-minus-quadratic weight.

## 1. A common true-pointwise calibration and tightness

Write \(\ell=\log L,\ w=1/\ell,\ W=x^w\). For each \(j=2,4\),
\[
 \sum_{\substack{y\in J,\ P\ {\rm prime}\\
            y\ {\rm squarefree},\ P^-(y)>W}}
       (\log P)(\log y)A_j(y)=2jM+o(M),                               \tag{2}
\]
uniformly in \(N\). The same sums of absolute weights on
\(\omega(y)>K\) are \(O(M\,V^{-K})\) for a fixed \(V>1\),
uniform in \(K\) and all sufficiently large \(N\).

Here are the needed calibration and tail checks; in particular
(2) does not transfer a cubic reference to another kernel. In
the score first replace \(\log y\) by \(L\). On the central
interval this changes each summand of the divisor sum by
\(O_j(1/L)\), using its global Lipschitz bound on a fixed compact
logarithmic interval. On squarefree \(W\)-rough values use
[Pollack, Theorem 1.1](https://www.pollack-math.net/brunmultiplicative4.pdf)
with the multiplicative weight \(f(p)=2\,1_{p>W}\), \(f(p^a)=0\)
for \(a\ge2\). The actual prime opponent \(P>x/2\) lies in
the sifted set obtained by excluding the single nonzero class
\(N\bmod r\) at every prime \(r\le x^{.001}\) not dividing \(N\).
The contribution of this forbidden-class bank is
\[
 \exp\left(-\sum_{\substack{r\le x^{.001}\\r\nmid N}}\frac1r\right)
           \ll \frac{\mathfrak S(N)}{L}.
\]
Indeed the missing target-prime harmonics cost a bounded
multiple of \(\prod_{r\mid N,r>2}(r-1)/(r-2)\), and the prime
2 contributes a bounded factor. The other Euler factor for
this \(f\) is \(O(w^{-2})\). Pollack's interval length condition
holds since \(J\) has fixed relative length; its growth
constants here are absolute. It follows that the log-normalization
replacement costs \(O(M w^{-2}/L)\), including the exterior log.

For \(F_j(v)=(1-2v)_+^j\) on \(v\ge0\), choose a fixed
smooth compact \(\psi\) equal to 1 on \([-1,1]\) and zero
off \((-2,2)\), \(0\le\psi\le1\). Put \(U=\ell^{-1/4}\) and
replace \(F_j\) by \(F_j(v)(1-\psi((v-1/2)/U))\), denoted \(F_{j,U}\).
Its positive-log support lies below \(1/2-U\); near zero its
value and derivative remain \(1\) and \(-2j\).

For the signed arithmetic sum with this shorter support,
one can first remove the squarefree gate, retaining the literal
\(W\)-rough gate, at \(o(M)\) cost. The count of such nonsquarefree
\(y\) is \(O(x/W+\sqrt x)\) by counting multiples of
prime squares \(r^2\), \(r>W\). Fixed divisor moments and Cauchy
pay the divisor weights and the two logs with a saving of
every inverse log. The true primes \(P\mid N\) in the central
interval likewise cost \(x^{o(1)}\) times log powers (there are
\(O(1)\)); omit these before imposing target units.
If a prime-progressions statement uses \(\Lambda\) instead of
true \(\Pi(n)=(\log n)1_{n\ {\rm prime}}\), its proper powers on
this interval are at most \(O(\sqrt x L)\), and the same divisor
moments or the pointwise fixed divisor-power bound \(x^{o(1)}\)
give \(o(M)\).

Open the actual \(W\)-rough condition using the upper and lower
fundamental-lemma weights of level \(x^{U/2}\) on primes at
most \(W\) not dividing \(N\). Every retained divisor \(d\) of
the score is \(W\)-rough and every presieve divisor \(e\) is
\(W\)-smooth; the actual modulus is the coprime product \(de\).
Here \(d\le x^{1/2-U}\), so \(de\le x^{1/2-U/2}\), with a
greater-than-polylogarithmic margin. Their splitting is unique;
using a divisor-bounded multiplicity would also be harmless.
Ordinary weighted Bombieri–Vinogradov for the actual reduced
class \(N\bmod de\) applies to the two endpoints of the
reflected central window. Apply it first to either signed
short sum with a single sieve weight, and also to the
difference of the two sieve weights with \(|\mu(d)F_{j,U}|\);
the latter is a genuine nonnegative bound for the sifting error.
The relative fundamental-lemma discrepancy of their main terms
is \(\exp(-c(U/w)\log(U/w))\), while the absolute \(d\)-harmonic
is \(O(1/w)\). With the external log this costs \(o(M)\).

For clarity, the resulting model is
\[
 L|J|\, V_N(W)
 \sum_{\substack{P^-(d)>W\\(d,N)=1}}
      \frac{\mu(d)F_{j,U}(\log d/L)}{\phi(d)},\qquad
 V_N(W)=\prod_{\substack{r\le W\\r\nmid N}}\left(1-\frac1{r-1}\right)
 =(1+o(1))\frac{e^{-\gamma}\mathfrak S(N)}{wL}.                       \tag{3}
\]
The usual Mertens comparison for this last product is uniform;
the omission of any target primes above \(W\) changes it by \(1+o(1)\).
The support, supremum norm and total variation used in the
harmonic replacement are uniform in \(U\); even the
\(O(1/U)\) cutoff derivative is multiplied by \(O(U^j)\).
The alternating harmonic in (3) equals \(2j e^\gamma w+o(w)\).
One direct justification, also used for the
[revised rough cusp](../revised_cusp_true_mixed_rank_bank/Proof.md),
is to replace each \(W\)-rough prime harmonic by the
Stieltjes measure \(1_{v>w}\,dv/v\); the uniform PNT cumulative
error above \(W\), times the positive factorial-convolution
majorant \(O(w^{-C})\), saves every log power. Repeated labels,
\(\phi\) versus the reciprocal, and target-prime omissions
have harmonics \(O(L/W)\) multiplied by such a majorant.
The cumulative alternating convolution, including its atom at
zero, is \(\rho(v/w)\) with \(\rho\) Dickman's function.
This follows by Laplace transform:
\(\int_0^\infty e^{-sv}\rho(v)\,dv=\exp(-E_1(s))/s\),
where \(E_1(s)=\int_1^\infty e^{-su}\,du/u\). The delay equation
\(v\rho'(v)=-\rho(v-1)\), \(\rho=1\) on \([0,1]\), proves
this transform; \(\int \rho=e^\gamma\) follows at \(s=0\).
Dickman's factorial tail and the fixed slope at zero now give
\(-\int F'_{j,U}(v)\rho(v/w)dv=2j e^\gamma w+O(w^2)\).

It remains to restore the exact mathematical half and control
rank tails. On squarefree \(y\), a compact real log-test \(h\)
has the exact Fourier factor
\(\prod_{r\mid y}(1-\exp(it\log r/L))\); use Fourier inversion
before taking its absolute value. The shoulder
\(h(v)=F_j(v)\psi((v-1/2)/U)\) is supported in a width \(O(U)\)
and has transform
\[
       |\widehat h(t)|\ll_j U^{j+1}\min(1,|Ut|^{-j-1}).
\]
This follows from rescaling and the bounded variation of the
\(j\)-th derivative, including its one-sided jump. Extend the
full \(F_j\) smoothly and compactly on negative arguments,
unchanged for all \(v\ge0\); its transform has decay
\(O_j((1+|t|)^{-j-1})\). Apply Pollack as above to
\(p\mapsto V|1-\exp(it\log p/L)|\), zero on higher prime powers.
For \(1\le |t|\le L\) the additional Euler factor is
\(O_V((1+|t|)^{4V/\pi})\): use harmonic PNT partial summation
and the bounded primitive of the mean-zero part of
\(2|\sin(u/2)|\), of mean \(4/\pi\).
For \(L\le|t|\le L^3\), omitting primes with
\(\log p\le(C\log L)^4\) costs \(\ell^{O_V(1)}\); the remaining
PNT error is bounded uniformly after the \(L^2\) variation
loss. That range has Euler factor
\(O_V(L^{4V/\pi}\ell^{O_V(1)})\).
Beyond \(L^3\) use \(O_V(L^{2V})\). At \(|t|\le1\) the
Euler factor is bounded by the log-prime harmonic.
Thus with \(V=1\) the actual shoulder has absolute weighted
mass \(O(M U^{j-4/\pi})+o(M)=o(M)\); with \(V=6/5\)
the full absolute weighted integral is \(O(M)\) after
inserting \(V^{\omega(y)}\), since \(4V/\pi<2\).
This proves (2) and the stated exponential tail. The own-log
replacements for the rank tail itself can also insert \(V^\omega\)
in the Pollack estimate of the preceding Lipschitz error,
costing only \(O(M w^{-2V}/L)\) before \(V^{-K}\).

On primes \(y\), \(A_4(y)=A_2(y)=1\) exactly. Subtract (2)
to obtain the prime-neutral actual composite identity
\[
 \sum_{\substack{y\in J,\ P\ {\rm prime}\\
        y\ {\rm squarefree},\ P^-(y)>W,\ \omega(y)\ge2}}
       (\log P)(\log y)B(y)=4M+o(M).                                 \tag{4}
\]

## 2. Angular signs and the one-sided shape budget

For a simplex profile \(b\) at rank \(k\) put
\[
 I_k(b)=\frac1{k!}\int_{\substack{u_i>0\\\sum_i u_i=1}}
                       \frac{b(\mathbf u)}{\prod_i u_i}
                                      \,du_1\cdots du_{k-1}.
\]
This reference uses the angular PNT normalization of the
[actual 3.446 prime upper](../angular_prime_first_composite/Proof.md).
We will apply that upper only to nonnegative profiles. At
each fixed rank, multiplying by the physical \(\log P\log y\)
changes its \(L^2\) normalization by \(1+O(1/L)\).
In the cited wider central interval \(I\), the spatial
profile supported on \(J\) has ordinary reference
\((|J|/|I|)I_k(b)\), by ordinary product-prime PNT in
fixed angular boxes (fix all but the last prime, then use
the prime harmonic and the last-prime PNT).
Thus its \(X_N=|I|\mathfrak S(N)\) reference is exactly
\(M I_k(b)\) after this spatial localization.
Its initially compact angular range can exhaust fixed ranks:
for a fixed \(k\), the scores are
\(O_k(\min_i u_i)\) by pairing across the true least prime.
Fix every true prime label except the largest \(q\).
For the two affine forms \(q,N-Dq\), \(D\) the product of
the fixed labels, a standard two-form upper sieve yields
\(\ll_k x\mathfrak S(N)/(D L^2)\) for each product \(D\).
All \(q\) used here satisfy \(q\gg x^{1/k}\), and a fixed
small-power sieve floor sums with a power reserve since
\(D\ll x^{1-1/k}\). Target nonunits are excluded as in §1.
The slope local factor is bounded uniformly on \(W\)-rough
labels, where \(\prod_{r\mid D}(r-1)/(r-2)=1+o(1)\).
The integral of the marked least angle \(u<\xi\) is then
\(\ll_k\int_0^\xi(1+\log(1/u))^{k-2}\,du=o_\xi(1)\):
the other fixed prime harmonics start at that least label.
The same bound for the actual arithmetic sum follows by
geometric bins and PNT partial summation, starting at \(W\).
This pays the tiny-angle faces and permits smooth upper
envelopes of the nonnegative piecewise-polynomial profiles.
Use the true exponential rank tail of §1 **after** the
fixed-rank estimates. No growing-rank sieve uniformity
is required.

On rank two, using \(s=1-2u_{\min}\), one has
\(B=s^2(1-s^2)\) and \(I_2(B)=2\int_0^1s^2\,ds=2/3\).
For rank three with all labels \(<1/2\), only singles are
nonempty short divisors, and \(B\) is the sum of
\(s_i^2(1-s_i^2)\), \(s_i=1-2u_i\). If there is a giant,
only subsets of the other two labels \(a,b\) contribute.
The ratio of the two finite differences \(A_4/A_2\) then
equals \(6\mathbb E[(1-2(S+T))^2]\) where \(S,T\) are independent
uniforms on \([0,a],[0,b]\). Jensen and \(a+b\le1/2\)
give ratio at least \(3/2\). For even ranks, complementary
subsets show \(A_j\) equals half the full polynomial
difference when \(j=2,4\); hence rank four has \(B=192\prod u_i\)
and rank even \(\ge6\) is zero.

On rank five, \(A_2\le0\) and \(-I_5(A_2)<.142816\) by the
exact sign and Euler integral in
[Quadratic Upper and Switching Scope](https://github.com/mxym/math/blob/main/research/theory-2026-11-20/strong-goldbach/QuadraticUpperAndSwitchingScope.md)
(the displayed \(Q\) there is \(A_2/4\) at total angle one).
The fifth derivative of \(v_+^4\) is \(24\delta_0\); the
five-fold difference representation gives \(A_4\ge0\)
on rank five. On rank seven, the same representation uses
the second derivative at the midpoint of a convolution
of seven interval indicators. This convolution is symmetric
and unimodal about its midpoint (convolution preserves
symmetric unimodality, by the layer-cake formula), so its
second derivative there is nonpositive. Thus \(A_4\le0\)
on rank seven. Together these facts reduce the unwanted
one-sided model to
\[
 \frac23 +.142816+ I_5(A_4)
      + I_7((-A_2)_+) + I_9((-A_2)_+)
      +\sum_{\substack{k\ge11\\ k\ {\rm odd}}}I_k((-A_2)_+)
      +\sum_{\substack{k\ge9\\ k\ {\rm odd}}}I_k(|A_4|).                 \tag{5}
\]

## 3. Positive tent bounds for the seventh and ninth ranks

We give a deterministic upper on each of the two angular terms
in the middle of (5). Work in the fully ordered sector and
take the second-largest unnormalized label to be 1 and the
largest to be \(q\ge1\). The smaller ordered labels are
\(a\le b\le c\), followed by the ordered list
\({\cal R}=(d,\ldots,1)\) of length \(k-4\). Let
\(h=b+c+\sum_{r\in{\cal R}}r\).
For any \(s>0\) write \(\Delta_s f(t)=f(t)-f(t-s)\).
Taking the \(q\)-bit and complementing the other \(k-1\)
bits, the unnormalized homogeneous score is
\[
    -16\Delta_{\cal R}
       (\mathbf1_{[0,a]}*\mathbf1_{[0,b]}*\mathbf1_{[0,c]})
                               ((h+a-q)/2).                          \tag{6}
\]
Indeed the complete polynomial difference of \(t^2\)
on the other \(k-1\) labels is zero, so the \(q\)-bit produces
\(-2\) times their hinge difference. Apply the third
derivative of \(t_+^2\), \(2\delta_0\), and multiply by 4
for the use of \((\sum u_i-2u_d)_+^2\). This accounts for
both sign and factor in (6).

The descending adjacent ratios of the labels below 1
are independent box variables on \([0,1]\). Keeping the
ratio \(a/b\) and the \(k-3\) other ratios, the ordered
sum-one angular measure is \(dq\) times their product
Lebesgue measure divided by \(q a\). To verify the
projective Jacobian, first fix the second-largest
label to 1; changing to sum one cancels the exact
power of the total against the product reciprocal
denominator. In these unnormalized raw labels, the
adjacent-ratio triangular Jacobian is the product of all
intermediate lengths, cancelling all except \(a\) in
the remaining denominator. The homogeneous score
contributes the extra divisor \((q+h+a)^2\).

Write the convolution in (6) as an integral over
\(t\in[0,a]\) of the tent \(T_{b,c}=\mathbf1_{[0,b]}*
\mathbf1_{[0,c]}\). Drop all odd shift allocations and
integrate only their positive upper. In each such term
put \(R=q+2t-a\), \(z=(h-R)/2\). Then \(R\ge1-b\),
\(q\ge\max(1,R-b)\), and \(q+h+a\ge R+h\).
The \(t\)-integral now costs at most \(a\) and cancels
the angular \(1/a\), leaving a unit integral in the
ratio \(a/b\). Also \(dq=2|dz|\) and \(R+h=2(h-z)\).
For an even subset \(S\subset{\cal R}\), integrate the
tent by \(z=\sum_{r\in S}r+b\xi+c\zeta\), with
\(0\le\xi,\zeta\le1\), so its measure is \(bc\,d\xi d\zeta\).
We obtain the exact upper
\[
 I_k((-A_2)_+)\le
 8\sum_{|S|\ {\rm even}}\int_{[0,1]^{k-3}}\int_{[0,1]^2}
       \frac{bc\,1_{z\le(h-1+b)/2}}
               {\max(1,h-2z-b)(h-z)^2}\,
                   d\xi\,d\zeta\,d\mathbf r.                         \tag{7}
\]
All denominators on the support are positive; in particular
\(h-z\ge(h+1-b)/2\). There is no boundary-divergent
\(1/\min u_i\) in (7).

For the reproducible integer upper of (7), partition the
outer \(d=k-3\) ratio cube into equal boxes of side \(1/n\)
and the inner \(\xi,\zeta\) square into squares of side \(1/m\)
with even \(m\). In a given outer box write
\[
 D=\sum_{r\notin S}r-\sum_{r\in S}r,\qquad
 h-z=b(1-\xi)+c(1-\zeta)+\sum_{r\notin S}r.
\]
The exact extrema of \(D\) follow by the nested recursion
of its signed partial-ratio products; at each step the
current affine term has a slope of known sign, so choose
its appropriate endpoint. Lower-bound the first denominator
using
\(\max(1,-2b\xi+c(1-2\zeta)+D)\) with the adverse box
endpoints and \(D_{\min}\). Lower-bound the second by the
larger of the positive endpoint lower and the support lower
\((h+1-b)/2=(1+c+\sum{\cal R})/2\).
The support condition is
\(2(1-\xi)b+(1-2\zeta)c+D\ge1\). For its upper set use
the upper \(b\), the endpoint of \(c\) dictated by the
entire \(\zeta\)-cell sign, and \(D_{\max}\).
In each inner square the exact allowed fraction is the
area of \(A u+B v\le C\) in \([0,1]^2\), \(A,B\ge0\);
its triangular/trapezoidal formula is elementary.
Pull the resulting independent upper coefficient outside
and integrate \(bc\) on each outer box **exactly**,
using the first moment of its last ratio and second
moments of all earlier ratios. Every term is nonnegative.

The companion [integer checker](check_peel.cpp) uses integer
endpoint numerators with denominator \(n^d\). It rounds the
allowed fraction and reciprocal up separately to multiples
of \(2^{-38}\), and rounds their product up, also before
accumulation. For \((d,n,m)=(4,24,12),(6,14,8)\) it verifies
respectively
\[
               I_7((-A_2)_+)<.01661,\qquad
               I_9((-A_2)_+)<.01824.                                \tag{8}
\]

## 4. All remaining higher ranks and the strict arithmetic conclusion

Use \(J(t)=\int_0^\infty e^{-v}|\sin(tv/2)|\,dv/v\),
\(a(t)=\arctan(t/2)\), and
\(R_r(z)=\sum_{k\ge r,\ k\ {\rm odd}}z^k/k!\).
The Fourier formula for \(A_2/4\) is equation (4) of the
[quadratic low-degree note](https://github.com/mxym/math/blob/main/research/theory-2026-11-20/strong-goldbach/QuadraticLowDegreeReduction.md).
Its signed radial sine series starting at odd \(k=11\) is
nonnegative (first sign positive, \(2a(t)\le\pi\), alternating
decreasing magnitudes). The negative part is therefore at
most half the absolute envelope. The radial \(\Gamma(2)=1\)
and the absolute Fourier prefactor give
\[
       \sum_{\substack{k\ge11\\ k\ {\rm odd}}} I_k((-A_2)_+)
                         \le \frac4\pi\int_0^\infty
                                    \frac{R_{11}(2J(t))}{t^3}\,dt.
                                                                    \tag{9}
\]
For \(A_4\) at odd \(k\ge5\), the same centered-difference
Fourier expression has homogeneous prefactor
\(2^4 4!/\pi=384/\pi\), exponent \(t^{-5}\), and signed
factor \((-1)^{(k-5)/2}\prod_{i=1}^k 2\sin(tu_i/2)\).
This follows by applying the fifth distributional derivative
\(24\delta_0\) of \(v_+^4\). In radial integration the
factor is \(\Gamma(4)=6\), giving
\[
 \begin{split}
 I_5(A_4)&=\frac{64}{\pi}\int_0^\infty
                              \frac{(2a(t))^5}{5!\,t^5}\,dt,\\
 \sum_{\substack{k\ge9\\ k\ {\rm odd}}}I_k(|A_4|)
     &\le \frac{64}{\pi}\int_0^\infty\frac{R_9(2J(t))}{t^5}\,dt .
 \end{split}                                                        \tag{10}
\]
The absolute Euler expansions in (9)–(10) justify the
signed exchanges: the same convergent bounds dominate
their integrals.

The positive cosine expansion used in the quadratic note
gives the exact useful bound
\[
 J(t)\le\min(t/2,\pi^{-1}\log(1+t^2)+C),\quad
 C\le\frac4\pi\left\{\sum_{n=2}^{10}\frac{\log n}{4n^2-1}
       +\frac{\log 10+1}{10(4-1/121)}\right\}<.31.
\]
For \(t\le1/2\), use \(R_r(t)\le2t^r/r!\).
For \(t\ge2^{24}\), the upper for \(R_r(2J(t))\) is
\(e^{2J(t)}/2\le t^{4/3}\); here \(e^{2C+2/(\pi t^2)}<2\).
Between these endpoints use monotone right-cell bounds
on these explicitly increasing envelopes (not on \(J\)
itself) and the exact \(t^{-j}\) integrals. The same argument
for the first line of (10) uses monotonicity of \(a(t)\)
and its bounds \(2a(t)\le\min(t,\pi)\) at the exterior
endpoints. The companion [rational checker](check_tail.py)
replays the logarithm/atan series and all intervals:
\[
  I_5(A_4)<.2918,\qquad
  \text{bound in (9)}<.0201,\qquad
  \text{last bound in (10)}<.00163.
\]
The exact accumulated enclosures are used in its final
comparison. With (8) and the same 3.446 fixed-target prime
upper on every positive part, the entire unwanted weighted
sum (ranks two and \(\ge5\)) is \(<3.988 M\) in normalized
limsup. In particular no weighted average in \(N\) or
bound for a signed angular model is substituted for a
true arithmetic upper.

Subtract from (4). Then remove the true rank-three/four
rows with least prime \(\le x^\eta\), using the fixed-rank
tiny-angle estimate in §2, whose constant is fixed and
whose right side tends to zero with \(\eta\).
Choose fixed \(\eta>0\) after the absolute margin and
before letting \(N\) grow. The surviving actual
nonnegative rank-three/four sum exceeds \(.010M\)
uniformly for every sufficiently large even target,
as asserted. Since \(0\le B(y)\le32\) on these two
ranks and both logarithms are \(O(L)\), (1) implies
the stated unweighted count.
