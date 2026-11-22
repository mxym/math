# A complete growing-macro-rank projection of the true smoothed score

Keep the [actual smoothed all-small completion](../smoothed_gap_two_macro/Proof.md):
\(N=2x\) even, \(L=\log x\), \(\ell=\log L\), \(J=xJ_0\) with
fixed nonempty \(J_0\subset[1,3/2]\), and \(P=N-y\) a true prime.
Use the same fixed smooth probability of gap \(g\in[U,2U]\) with
survival function \(\psi(t/U)\), but change the parameters to
\[
       \epsilon=U=\ell^{-1/4},\qquad
       w=U^3,\qquad W=x^w,\qquad C_y=y/x^{1-\epsilon},\qquad
       K=\lfloor .07\log\ell\rfloor.                     \tag{1}
\]
On a true squarefree \(W\)-rough \(y\) write \(S_y\) for its
complete actual factor supported below \(C_y\), and \(B_y=y/S_y\)
for its macro part; all factor labels are actual primes.
Write \(\overline H(y)\) for the actual averaged score in
equation (2) of the linked proof, with (1).

Define \(Z(y)=0\) unless \(y\) is squarefree, \(W\)-rough and
\(S_y=1\); on that physical no-small class put
\[
 Z(y)=
   \sum_{\substack{d\mid y\\d<\sqrt y}}
      \big(1-\psi((\log\sqrt y-\log d)/(UL))\big)
                           (1+\mu(y/d))\log d\ \ge0.     \tag{2}
\]
Thus (2) contains exactly the averaged safe terms of the
no-small score, not independent model mass.

**Theorem.** Uniformly in the even target,
\[
 \sum_{\substack{y\in J,\ P=N-y\ {\rm prime}\\
           y\ {\rm squarefree},\ P^-(y)>W,\ \omega(B_y)\le K}}
       \log P\,|\overline H(y)-Z(y)|
        \ll_{\psi,J_0} x\mathfrak S(N)\ell^{-.03}.          \tag{3}
\]
In particular the entire small-containing class **within these
macro ranks**, including arbitrary counts of actual small factors,
is negligible in absolute whole-row score. On the no-small
class only the explicit nonnegative safe weights (2) are left.
The same statement holds for any fixed maximum macro rank by
restriction of the nonnegative left side. No claim is made
on the true macro ranks \(K<\omega(B_y)\le1/\epsilon+o(1)\),
or that the lower envelope supplied by (2) is a known
positive surplus over the reference.

The calibration on the new parameters is
\[
 \sum_{\substack{y\in J\\P=N-y\ {\rm prime}}}
      \log P\,\overline H(y)
  =\mathcal G_J(N)+|J|\mathfrak S(N)
        \left(\int Q_\epsilon(\tfrac12-g)\,d\nu(g)-1\right)
        +O_{\psi,J_0}(x\mathfrak S(N)U).                 \tag{4}
\]
Here \(Q_\epsilon\) and \(d\nu\) have exactly their linked
definitions, and \(\mathcal G_J\) is the true ordered prime-pair
weight. The reference \(\tfrac12-g\) is retained. The proof of
that theorem's calibration applies verbatim: the actual
fundamental-lemma ratio \(g/(2w)\gg U^{-2}\) now has more room,
the harmonic \(O(w/\epsilon^2+\epsilon^{-3}/L)\) is \(O(U)\),
and none of its other estimates restrict \(\epsilon/U\) or
require approximate evaluation of \(Q_\epsilon\) at \(1/2\).
Proper prime powers, non-squarefree rough \(y\), and \(P\mid N\)
retain their negligible weighted costs by the same argument.
In particular (4) is not imported from the prior sharp
reference.

## 1. Physical factor splits

The exact safe and raw kernels used below are for the **entire**
score, not a mixture with chosen positive receivers. Uniformly in
all ranks, (3)'s heavy-cloud rows \(S_y>x^{.05}\) contribute
\(O_A(x\mathfrak S(N)\ell^{-A})\): the upper
\(|\overline H(y)|\ll L2^{\omega(y)}\) follows from its
raw/safe pair formulas, and \(Z=0\) when \(S_y>1\).
Use the argument for equation (7) of the linked proof on the
same fixed-slope affine forms \(Y,N-Y\), with weight 2 at
**all** permitted primes \(r>W\), additionally multiplied by
\(r^{a/(\epsilon L)}\) at each \(r^a\) for \(r\le1.5x^\epsilon\).
The \(N\)-unit mask stays on both legs. The same fixed
Henriot class works uniformly in the rank, the same
discriminant/root factors give \(\mathfrak S(N)/L^2\),
and the Euler factors cost at most \(O(w^{-C})\)
with absolute fixed \(C\). The tilt supplies
\(e^{-.05/\epsilon}\) on the event, proving the claim
without any polynomial lower bound on an individual
macro size in these heavy rows.

Henceforth \(S=S_y\), \(s=\log S/L\le.05\), \(k=\omega(S)\),
\(T=\log y/L=1+O(L^{-1})\), and \(m=\omega(B_y)\le K\).
A zero-macro row is then impossible. A complementary
divisor pair is represented once by an unordered split
\(\{M,M'\}\) of the actual squarefree macro part \(B_y\).
Orient each split in any fixed way and run over all
\(A\mid S\), with \(M A\) the oriented representative
and \(M'S/A\) the other side. The distinct positive
macro products uniquely determine the chosen orientation;
in the sole empty-side split use the side of macro product 1.
Put
\[
 u=\log M/L,\quad a=\log A/L,\quad z=u+a-T/2,\quad
 \alpha=\mu(M),\quad \beta=\mu(M'),\quad
 \sigma=\mu(S),\quad \eta=\alpha\beta\sigma=\mu(y).
\]
After taking out the signed factor \(\mu(A)\) and \(L\),
the full raw and the two possible safe kernels are exactly
\[
 \begin{split}
 R(a)&=\alpha T+(\beta\sigma-\alpha)(u+a),\\
 B_-(a)&=(1+\eta\alpha)u+(\eta\alpha-1)a,\\
 B_+(a)&=\sigma\{(1+\eta\beta)(T-s-u)
                               +(\eta\beta-1)(s-a)\}.
 \end{split}                                               \tag{5}
\]
For example the raw term is
\(\mu(M A)\log(M'S/A)+\mu(M'S/A)\log(M A)\).
The safe term is
\(\mu(S_d)((1+\mu(y)\mu(M_d))\log d-2\log S_d)\)
at the actual shorter divisor, giving \(B_-\) if \(z<0\)
and \(B_+\) if \(z>0\).
Therefore with \(\Psi(z)=\psi(z/U)\) and
\(F(z)=(1-\Psi(z))1_{z>0}\), the complete orbit in this
macro split is the sum over \(A\mid S\) of
\[
 L\mu(A)\big\{
 B_-(a)+(R(a)-B_-(a))\Psi(z)
                    +(B_+(a)-B_-(a))F(z)
                        \big\}.                         \tag{6}
\]
All three coefficient functions are affine in \(a\);
their other coefficients are bounded on the actual product
ranges. Formula (6) includes both signed safe tails.

If \(k=0\), subtracting (2) leaves only the raw term
\(L R(0)\Psi(u-T/2)\) in each split. Its absolute angular
integral is \(O_\psi(U)\). If \(k\ge2\), the baseline
\(B_-\) cancels exactly in the subset sum, and each step
term of (6) has a nonempty difference, even if one slot
has been opened for \(a\). The other safe tail also cancels
since it is affine. In either case the residual has
support \(u\in[T/2-s-2U,T/2+2U]\).
If \(k=1\), let \(s=\log r/L\) for its sole genuine small label.
Both far safe tails of the two-term subset difference are
\(O(s)\) after division by \(L\) (there only the affine
coefficient is differenced). On the interval
\[
                         T/2-s-2U\le u\le T/2+2U,
\]
use the pointwise derivative of (6) with respect to \(a\);
it gives \(O_\psi(s/U)\) inside the interval, since \(s\le
\epsilon+O(L^{-1})=U+O(L^{-1})\) and the kernels are smooth.
In summary the full normalized two-term score is bounded
by \(O_\psi(s)+O_\psi(s/U)1_{\rm active}\).
The first part costs \(O(s)\) even if one macro side is
empty; the other requires both sides to be nonempty.

For an empty macro side (hence \(M=1\) up to orientation)
the actual shorter side is always in \(S\), since \(s\le .05\).
Thus in the empty split there is no residual when \(k=0\)
or \(k\ge2\); in particular the genuine prime \(y\) has
zero score here. For \(k=1\) its \(O(s)\) term is included
in the preceding bound.

For \(k\ge2\) the nonnegative harmonic sum over \(S\) of
the absolute angular integrals of the residual is
\(O_\psi(U)\), uniformly in the fixed macro labels and
\(\alpha,\beta,\sigma\), in the following precise sense.
Replace \(T\) numerically by 1 after naming the actual
small primes; costs are discussed below. Bound each
bounded linear coefficient in (6) by a fixed constant
and apply the [finite-difference \(L^1\) estimates](../smoothed_gap_two_macro/Proof.md#3-absolute-bound-for-the-complete-smoothed-finite-differences)
to its resulting complete differences, with small labels
\(W<r\le1.5x^\epsilon\) and the parameters (1).
In that proof the upper frequency bands of \(f=\Psi,F\)
have \(L^1\) norm \(O_{\psi,j_0}(U2^{-j_0 j})\); the
positive Euler factor is \(O((1+\epsilon 2^j/U)^2)
=O((1+2^j)^2)\). Its low-step bound uses the least label
once, with \(u_r\)-weighted harmonic mass \(O(U)\);
those above exponent \(U\) have only \(O(L^{-1})\) extra
width, or are bounded by the same \(O(U)\) integral.
The opened logarithmic slot for \(a\) costs
\(\sum u_r/r=O(U)\). Thus the total is \(O_\psi(U)\);
it has no hidden rank-dependent constant on the small
side. Bound the sign choices by a finite sum over all
\(\alpha,\beta,\sigma=\pm1\) if they vary with the fixed macro
labels. For \(k=1\) the active interval of width \(O(U)\)
multiplies \(O(s/U)\), and its \(s\)-harmonic mass is
\(O(\epsilon)=O(U)\). For \(k=0\) use the explicit raw integral.
These are all bounds on the complete same-row orbit,
with the angular integral appearing only in the **upper**
argument below.

## 2. True prime counting with a growing but explicit range

Whenever an active split occurs, both macro products have
logarithmic exponent at least \(.44\) for large \(x\), by
\(s\le .05\), the active interval and \(T=1+O(L^{-1})\).
Pick the largest genuine macro prime \(p\) on the first side
and the largest genuine \(q\) on the second. Then
\[
              p,q\ge x^\kappa,\qquad \kappa=.4/K.
\]
Actual inequalities involving the other labels, including
the largest tests, may subsequently be relaxed only for
a positive upper. Fix \(S,p\) and the other \(m-2\) macro
labels and their allocation, and let \(H\) be their product.
The genuine \(q\) and \(N-Hq\) lie on the two affine forms,
with \(q\asymp x/H\), \(H\le1.5x^{1-\kappa}\), and
\((H,N)=1\) after removing \(P\mid N\).
For the nonactive \(O(s)\) term when \(k=1\), pick only
the largest macro prime \(q\) of \(y\), which also exceeds
\(x^\kappa\), fix all other labels, and use the same bound.
No prior analytic theorem is invoked for these true forms.

Apply the [elementary true two-form Selberg upper](../wide_gap_safe_bank_packet/Proof.md)
with both forms sieved to \(z_0=x^{\kappa/50}\) and
square weight cutoff \(R=x^{\kappa/10}\).
Both actual primes exceed \(z_0\). The full positive
Selberg normalization keeps a fixed fraction by Markov:
the expected logarithm of its squarefree product is
at most \(2\sum_{r\le z_0}\log r/r\le .05\kappa L\)
for large \(x\). These estimates are uniform for the
growing \(K\) because \(z_0\to\infty\) exponentially
faster than any log power. The CRT-floor argument still
gives \(R^6=x^{.6\kappa}\), and the local factor adjustment
for slope primes \(r\mid H\), all \(>W\), costs \(1+o(1)\).
The target factors, including the parity at 2, are as in
the linked bound. Thus the actual count at each \(H\) is
\[
   \ll\kappa^{-2}\frac{(x/H)\mathfrak S(N)}{L^2}
                                             +x^{.6\kappa}. \tag{7}
\]
This uniform estimate is valid even when some of the
fixed macro factors happen to lie below \(z_0\), since they
only affect slope-prime roots and all are greater than \(W\).

Summed floors have power-scale reserve even for this
growing \(K\). A fixed actual \(H\) can be written in the
different counted ways by choosing the small subset,
the partition of other macro prime factors, and the
distinguished \(p\) if present. The resulting multiplicity,
including the absolute per-row orientation bound
\(O(2^k)\) at the fixed split, is at most a **fixed** power
of \(\tau(H)\). This follows by direct subset choices on
the squarefree factors of \(H\): at most \(2^{\omega(H)}\)
choices in each subset stage and \(\omega(H)\) choices
of a prime. In the baseline single-\(q\) bound a possible
extra macro-split multiplicity is at most \(2^{\omega(H)+1}\);
again the exponent is absolute. Hence all the floors
including the two logs are
\[
   O\left(x^{.6\kappa}L^2
           \sum_{H\le1.5x^{1-\kappa}}\tau(H)^C\right)
       \ll x^{1-.4\kappa}L^{C'} ,
\]
with **fixed** \(C,C'\). This is negligible relative to
\(x\mathfrak S(N)\ell^{-.03}\) since \(K=O(\log\ell)\).
The bound counts only tuples satisfying the true \(H\)
range; its restrictions are relaxed after removing floors.

For the main of (7), once the other macro factors are
fixed the variable \(p\)'s \(\log p/L\) is a translate of
\(u\). Its reciprocal-prime measure is \(d(\log p/L)/(\log p/L)\),
which is bounded by \(\kappa^{-1}\,du\) on its actual range.
The PNT makes this passage to angular integrals with
arbitrary-log errors after the relevant sums; explicitly
its uniform Stieltjes error starting at \(x^\kappa\) is
\(O(e^{-c\sqrt{\kappa L}})\), and each absolute complete
kernel has sup and total variation \(O_\psi(2^k/U)\).
The latter bound comes directly from (6) before taking
absolute values, by its fixed smooth coefficients.
The \(k=1\) indicator interval is a fixed-prefix use of
the same prime harmonic estimate.
Replacing \(T\) by 1 numerically changes the raw/difference
kernels by \(O_\psi(2^k/(UL))\), without changing the
physical identity of small labels. They remain in the
same enlarged active support after this replacement.
For the \(k=1\) Lipschitz bound one can simply enlarge
the indicated active interval by \(O(L^{-1})\); its
width remains \(O(U)\), and the baseline is unchanged in
size. All harmonic errors, including the \(T\)-replacement,
are summable: \(2^k/S\) has total \(O((\epsilon/w)^2)=
O(U^{-4})\), the fixed macro harmonics below have at most
a fixed power of \(\ell\), and \(1/(UL)\) suffices.
No independent distribution of the two actual primality
events in (7) is assumed.

It remains to state the macro harmonic cost explicitly.
Let \(H_\epsilon=\sum_{x^\epsilon\le r\le 2x,\ r\ {\rm prime}}1/r
\le .251\log\ell\) eventually. For \(j=m-2\) fixed macro
labels in an active split, the unordered set has harmonic
at most \(H_\epsilon^j/j!\) (discarding actual product
constraints only for this upper). There are at most
\(2^j\) allocations of those labels. The two distinguished
prime variables were already counted in (7) and the
angular harmonic. The nonactive \(s\)-term fixes \(j=m-1\)
remaining macro labels; each of the possible macro
splits costs at most \(2^{m}=2^{j+1}\) regardless of the count.
Thus both are bounded by a fixed constant times
\[
                    \sum_{j=0}^{K}\frac{(2H_\epsilon)^j}{j!}.
\tag{8}
\]
There is no ordered-tuple factor \(j!\) to reinsert.

Combining the \(O_\psi(U)\) angular and baseline bounds,
the two weighted logs, and (7)--(8), the main upper in (3)
is at most
\[
 \ll_\psi x\mathfrak S(N)\,
        \kappa^{-3} U
                       \sum_{j=0}^{K}\frac{(2H_\epsilon)^j}{j!}.
\]
With \(K\le .07\log\ell\), the exponent of its largest
summand is at most \(.21\log\ell\) for large \(x\):
use \(j!\ge (j/e)^j\), \(2H_\epsilon\le.502\log\ell\),
monotonicity of \(j(1+\log(.502\log\ell/j))\) here, and
\(\log(.502/.07)<2\). The additional \(K+1\) and
\(\kappa^{-3}\) are fixed powers of \(\log\ell\).
Since \(U=\ell^{-.25}\), this gives (3), including the
light/heavy cloud split and all the errors.

## 3. What is left on this same reference

For example (3)--(4) imply the identity up to
\(O_{\psi,J_0}(x\mathfrak S(N)\ell^{-.03})\),
\[
 \mathcal G_J(N)=
        \sum_{\substack{P=N-y\ {\rm prime},\, y\in J\\
                       \omega(B_y)\le K}}\log P\,Z(y)
       +\sum_{\substack{P=N-y\ {\rm prime},\, y\in J,\;
                         y\ {\rm squarefree},\ P^-(y)>W\\
                        \omega(B_y)>K}}\log P\,\overline H(y)
       -|J|\mathfrak S(N)
                   \left(\int Q_\epsilon(\tfrac12-g)\,d\nu(g)-1\right).
\]
The ranks above \(K\) are **genuine** macro ranks with a growing
available range, not a finite harmonic truncation of the proof.
In particular their signed contribution is not estimated by
(8). The displayed positive safe partial sum is a true factor
observable, not an independent amount that can be added to the
old fixed-payer or other gap ledgers. Neither the remaining
high-rank signed term nor a sufficiently large strict surplus
of the positive part over this same reference has been proved.
Thus this is a projection on the actual prime leg, not a
proof of binary Goldbach.
