# Ramified binary search: an irreducible random rank factor

At modulus two the public random matrix in a dyadic ring can retain
a random kernel of bounded but nonvanishing size as the ring degree
grows. In the continuous spherical observation model this produces
an exact random factor in the optimal statistical success, even though
the *quotient by the public kernel* has the usual Gaussian transition.
The work concerns only a specified observation experiment and
arbitrary-time statistical limits. It is not a cryptographic solver,
a practical parameter study, or a classification of general Ring-LWE.

## 1. Statement

Let \(d\to\infty\) through powers of two and put
\[
 R_d=\mathbb F_2[x]/((x+1)^d)=\mathbb F_2[x]/(x^d+1).
\]
Use the power-basis coefficient grid \(R_d=\mathbb F_2^d\)
and its half-shift embedding in \(\mathbb T^d\).
Take fixed integers \(m>n\ge1\), a uniform hidden element
\(S\in R_d^n\), and an \(m\times n\) public matrix \(A\)
with independent uniform entries in \(R_d\).
For the \(i\)-th row observe \(B_i=(A_iS)/2+E_i\bmod1\),
where errors and all their coefficient coordinates are
independent, with circle density
\[
 f_b(t)=\sum_{k\in\mathbb Z}b^{k^2}e^{2\pi i k t},\qquad b=b_d\in(0,1).
\]
In the scalar case this is the continuous spherical codifferent
torus experiment at modulus two, with \(b=e^{-\pi d s^2}\)
for canonical width \(s\).

Set \(g_b=(f_b(t)+f_b(t+1/2))/2=f_{b^4}(2t)\),
\(l_b=\log(f_b/g_b)\),
\(C(b)=\mathbb E_{f_b}l_b\), and \(V(b)=\operatorname{Var}_{f_b}l_b\).
Write \(P_{\rm opt}(A)\) for optimal exact-label success
conditional on the matrix, \(P_{\rm class}(A)\) for optimal
success for the class of the label modulo \(\ker A\), and
\(K_d(A)=\log_2|\ker A|\) for the additive kernel of
\(A:R_d^n\to R_d^m\). None of these optima is time-restricted.
All other logarithms in this note are natural.

**Theorem.** Suppose \(b_d\to b_*\in(0,1)\) and
\[
       z_d=\frac{dm C(b_d)-dn\log2}{\sqrt{dm V(b_d)}}
                 \longrightarrow z\in[-\infty,\infty].
       \tag{1}
\]
Then
\[
 \begin{split}
 P_{\rm class}(A)&\longrightarrow\Phi(z)
                       &&\text{in }L^1(A),\\
 \mathbb E_A\left|P_{\rm opt}(A)-2^{-K_d(A)}\Phi(z)\right|
      &\longrightarrow0 .
 \end{split} \tag{2}
\]
Moreover \(K_d(A)\) converges in distribution to
\[
       K_\infty\stackrel{d}{=}\sum_{j=0}^{n-1}G_{m-j},
       \qquad
       \Pr(G_a=r)=(1-2^{-a})\,2^{-ar}\quad(r\ge0),
       \tag{3}
\]
with independent \(G_a\). In particular
\[
 P_{\rm opt}(A)\Longrightarrow 2^{-K_\infty}\Phi(z),\qquad
 \mathbb E_A P_{\rm opt}(A)\longrightarrow
       \frac{1-2^{-(m-n+1)}}{1-2^{-(m+1)}}\,\Phi(z).
       \tag{4}
\]
The kernel factor is genuinely random for \(z>-\infty\).
It persists even on the side where class success tends to 1.
This concerns \(q=2\) and fixed \(m>n\), not higher powers
of two, growing matrix shape, or the quantum hardness
error families.

## 2. Repeated root ideals and two scalar capacities

For \(0\le r\le d\), set \(J_r=(x+1)^r R_d\).
These are all ideals, \(\dim_{\mathbb F_2} J_r=d-r\).
With the binary coefficient dot product,
\[
                         J_r^\perp=J_{d-r}.
 \tag{5}
\]
Indeed the dot product is the constant coefficient of
\(a(x)b(x^{-1})\) modulo \(x^d-1\); the involution
sends \(x+1\) to the unit multiple \(x^{-1}(x+1)\).
The displayed spaces are orthogonal by \((x+1)^d=0\),
and their dimensions sum to \(d\).

For \(1\le k\le d\), take \(D\) the least power of two
at least \(k\), \(L=d/D\). Every word of \(J_{d-k}\)
consists of \(L\) repeats of a base word of length \(D\),
and the allowed base words form the dimension-\(k\)
ideal \((x+1)^{D-k}\) of the length-\(D\) ring.
Indeed, in characteristic two
\[
       (x+1)^{d-D}=(x^D+1)^{L-1}
                         =1+x^D+\cdots+x^{(L-1)D}.
\]
Multiply each base polynomial of degree less than \(D\)
by this expression. This maps the stated base ideal
injectively into \(J_{d-k}\), so dimension gives equality.
If \(k\le d/2\), one can also choose \(D=d/2\);
in particular all these words repeat two halves.
This is the elementary repeated-root identity used in
the proof (see classical repeated-root code work below).

For the memoryless scalar channel whose uniform input is
a bit \(U\) and whose output is \(U/2+E\),
write \(C_{\mathrm{rep}}(b)\) for the information about
one bit in two conditionally independent outputs,
and \(C_{\mathrm{par}}(b)\) for the information about the
parity of two independent uniform bits in their respective
outputs. Then
\[
                   C_{\rm par}(b)<C(b)<C_{\rm rep}(b).
 \tag{6}
\]
Strictness of the right inequality follows from
\(I(U;Y_2\mid Y_1)>0\): every posterior after one output
assigns positive mass to both labels, and the two
conditional distributions for the second output differ.
For the left inequality, the scalar posterior sign is
\(\eta(y)=(f_b(y)-f_b(y-1/2))/(f_b(y)+f_b(y-1/2))\),
uniformly bounded by a number less than one, and
the parity posterior sign is the product of two independent
such signs. For a uniform bit, mutual information is the
expectation of \(\frac12[(1+u)\log(1+u)+(1-u)\log(1-u)]\)
of its posterior sign; this is strictly increasing in
\(|u|\) away from zero. The scalar sign is nonzero with
positive probability because the first Fourier coefficient
of \(f_b\) is nonzero. Hence (6).
By continuity of these scalar quantities the gaps are
uniformly positive for \(b\) in a compact neighborhood
of \(b_*\).

For a general subgroup H in this coefficient grid let
\(p=f_b^{\otimes d}\), \(g_H\) its uniform half-shift
average, and \(D_H=D(p\Vert g_H)\).
This is also \(I(X;Y)\) for uniform input \(X\in H\);
the output law is \(g_H\), and translation preserves the
conditional noise entropy.
For \(H=J_r\), write \(k=d-r\). We claim
\[
 \begin{cases}
 D_{J_r}\ge d C(b)-r C_{\mathrm{par}}(b),
                                       &0\le r\le d/2,\\
 D_{J_r}\ge k C_{\mathrm{rep}}(b),       &d/2\le r<d .
 \end{cases}
 \tag{7}
\]
For the second bound the primal ideal repeats two halves.
Choose \(k\) independent coordinate projections of its base
dimension-\(k\) linear subspace. Their uniform bit values are
independent. Observing just their two corresponding outputs
gives \(k C_{\mathrm{rep}}(b)\) information and discarding other
outputs cannot increase it.

For the first bound use a full uniform grid input \(X\) and
let \(W\) be a full-rank \(r\)-bit syndrome with kernel \(J_r\).
By (5), its check rows repeat two halves, so
\(W=H_0(X^{(1)}+X^{(2)})\) with \(H_0\) of row rank \(r\).
Conditional output laws for all syndrome values are translations
of \(g_{J_r}\), and \(g_{R_d}\) is invariant under those
translations. Hence \(D(g_{J_r}\Vert g_{R_d})=I(W;Y)\).
Revealing the nonpivot coordinates of the uniform parity
vector \(X^{(1)}+X^{(2)}\) can only increase this information.
Those parity bits are independent of the syndrome, since the
pivot variables are uniform and \(H_0\) is invertible on their
\(r\) coordinates. The nonpivot pairs of noisy outputs now
carry no additional syndrome information, and observing the
pivot pairs gives exactly \(r C_{\mathrm{par}}(b)\).
Therefore \(I(W;Y)\le rC_{\rm par}(b)\).
The subgroup averaging identity
\(D_{J_r}=D(p\Vert g_{R_d})-D(g_{J_r}\Vert g_{R_d})\)
proves the first bound. One can verify the identity directly:
both \(\log g_{J_r}\) and \(\log g_{R_d}\) are invariant
under shifts by \(J_r\), hence have the same integrals against
\(p\) as against \(g_{J_r}\).

## 3. Elimination of competing classes

For actual residuals let \(T_r=\sum_{i\le m}\log
(p(E_i)/g_{J_r}(E_i))\).
The full ideal is \(r=0\), with \(T_0\) a sum of \(dm\)
independent scalar \(l_{b_d}\)'s of mean \(dm C(b_d)\)
and variance \(dm V(b_d)\). On a compact \(b\)-interval
these scalar increments are bounded and their variances
are bounded away from zero, since a constant \(l_b\)
would force \(f_b=g_b\). The triangular-array CLT implies
that for a cutoff \(\gamma_d=d^{1/4}\),
\[
            \Pr(T_0>nd\log2\pm\gamma_d)\longrightarrow\Phi(z).
 \tag{8}
\]
At infinite \(z\) the corresponding conclusion follows
from concentration or tightness of the standardized sum.

For each \(v\in R_d^n\) let its generated ideal be
\(J(v)=\sum_j R_d v_j\). For \(v\ne0\) it is a nonzero
\(J_r\). Conditional on the true label and residuals, the
likelihood ratio of the translated label differs only by
the shifts \(A_i v\); denote this ratio \(L_v\).
For fixed \(v\), the shifts \(A_i v\) are iid uniform
in \(J(v)\) over the matrix because every fiber of the
row map has equal cardinality. Thus \(\mathbb E_A L_v=e^{-T_r}\)
at fixed residuals. There are at most \(2^{nk}\) differences
of this type, \(k=d-r\). We analyze them in three ranges,
using \(a_d=\lfloor d/(C_1\log d)\rfloor\) for a sufficiently
large absolute-in-\(d\) constant \(C_1\) (depending on the
compact interval and \(m,n\)).

**Near the full ideal, \(0\le r\le a_d\).** Under a uniform
full grid prior, the output law conditioned on \(X\in J_r\)
has ratio \(g_{J_r}/g_{R_d}\). Expansion of the conditional
syndrome indicator in binary characters gives at each output
\[
      \frac{g_{J_r}(y)}{g_{R_d}(y)}
            =\sum_{w\in J_r^\perp}\prod_{j:w_j=1}\eta(y_j).
 \tag{9}
\]
Indeed the prior probability of \(X\in J_r\) is \(2^{-r}\);
the conditional posterior of the full input is a product,
and the character average over the dual gives the indicator.
For \(r\ge1\) the dual is a repetition of \(L\) blocks with
\(L\ge d/(2r)\), by (5) and the least dyadic \(D\) rule.
If \(\rho=\sup|\eta|<1\), uniformly on the compact width interval,
the sum excluding the zero word is bounded in absolute value
by \((1+\rho^L)^D-1\). Taking \(C_1\) sufficiently large makes
this \(O(d^{-4})\) uniformly for all \(r\le a_d\).
Consequently \(T_r=T_0+o(1)\) uniformly in the observed residuals
and these \(r\), since \(m\) is fixed.
On \(T_0>nd\log2+\gamma_d\) their summed expected likelihood
ratios (even including identical-signal differences) are at most
\(e^{-\gamma_d+o(1)}\sum_{r\ge0}2^{-nr}=o(1)\).

**Middle ideals, \(r,k>a_d\).** In the finite window (1) the
difference \(mC(b_d)-n\log2\) is \(O(d^{-1/2})\); for positive
infinite \(z\) it is eventually nonnegative.
Use (6)–(7). If \(r\le d/2\), the mean excess of \(T_r\)
above \(nk\log2\) is at least
\[
 k(mC(b_d)-n\log2)+m r(C(b_d)-C_{\rm par}(b_d)).
\]
If \(k\le d/2\), the lower bound on excess is
\(k(mC(b_d)-n\log2)+m k(C_{\rm rep}(b_d)-C(b_d))\).
In both cases it exceeds a positive constant times \(d/\log d\)
for all sufficiently large \(d\).
The coordinate changes of each log density ratio in the
sum \(T_r\) are uniformly bounded: changing one coordinate
multiplies both the product density and its subgroup average
by a factor between \(c\) and \(c^{-1}\), for fixed \(c>0\)
from the positive lower and upper bounds on the scalar density.
There are \(dm\) independent raw error coordinates.
By the bounded-differences inequality the chance that a
middle \(T_r\) is below \(nk\log2+\gamma_d\) is bounded by
\(\exp(-c'd/(\log d)^2)\), uniformly in \(r\).
A union over \(r\) is \(o(1)\). On the event all bounds hold,
their summed conditional expected likelihood ratios
are at most \(d e^{-\gamma_d}=o(1)\).

**Near the zero ideal, \(1\le k\le a_d\).** Here retain only
differences with \(A v\ne0\), because identical-signal labels
are in the true class. Let \(\kappa<1\) be a uniform upper
bound on the Hellinger affinity of \(f_b(t)\) and
\(f_b(t-1/2)\) on the compact width range.
For a fixed shift vector, the expectation under the true
noise of \(L_v^{1/2}\) is the product of scalar affinities,
bounded by \(\kappa\) to the total binary Hamming weight
of all the shifted rows.
For shifts over the matrix and a fixed \(v\) of the given
ideal type, all shift tuples are uniform over \(J_r^m\).
Using the repeated pattern, the sum of such weights over
nonzero tuples is at most \((1+\kappa^L)^{mD}-1\),
where \(L\ge d/(2k)\). Thus, for this \(r\),
\[
 \sum_{v:J(v)=J_r}\mathbb E_{A,E}
      [1_{\{Av\ne0\}} L_v^{1/2}]
     \le 2^{(n-m)k}\bigl((1+\kappa^L)^{mD}-1\bigr).
 \tag{10}
\]
The factor is at most 1. With \(C_1\) large enough,
the sum of (10) over these \(k\)'s is \(o(1)\).
This excludes zero shift tuples *before* the bound;
retaining them would falsely imply no public kernel effect.

For a uniform hidden label and fixed matrix, the posterior
probability of the true class equals
\[
 \frac{|\ker A|}{|\ker A|+\sum_{v:Av\ne0} L_v}.
\]
Its loss from 1 is at most
\(\min(1,\sum_{v:Av\ne0}L_v)\).
On the good residual event from the first two ranges,
their expected contribution is \(o(1)\) by the
conditional matrix bounds. In the third range
\(\min(1,\sum L_v)\le \sum L_v^{1/2}\), so the
expected loss there is \(o(1)\) unconditionally by (10).
The largest class posterior is at least the posterior collision
probability. Averaging gives
\[
          \mathbb E_A P_{\rm class}(A)
              \ \ge\ \Pr(T_0>nd\log2+\gamma_d)-o(1)
 \tag{11}
\]
for finite \(z\) and positive infinite \(z\).
For negative infinite \(z\) the lower bound 0 suffices.
This is a posterior probability proof, not a proposal to
compute or enumerate hidden labels.

## 4. Kernel size and the conditional upper bound

Under fixed \(A\), all labels in one coset of \(\ker A\)
have precisely the same conditional response distribution.
Hence \(P_{\rm opt}(A)=2^{-K_d(A)}P_{\rm class}(A)\).
Using \(g_{R_d}\) as reference error makes the response law
independent of the uniform class, with reference correct
class probability \(2^{K_d(A)-dn}\).
The log likelihood from reference to actual law is \(T_0\).
For each \(A\), change of measure therefore gives
\[
 P_{\rm class}(A)\le
 \Pr(T_0>dn\log2-K_d(A)\log2-\gamma_d)+e^{-\gamma_d}.
 \tag{12}
\]

We show the tightness and exact law in (3).
Couple the random matrix over \(R_d\) to an iid additive-Haar
matrix over \(\mathbb F_2[[t]]\), via \(t=x+1\) and truncation
modulo \(t^d\). For an \(a\)-row first column over this
power series ring its minimum entry valuation is \(G_a\),
since the chance all its entries lie in \(t^r\) is \(2^{-ar}\).
An invertible row change makes the primitive part of that
column the first basis vector; all remaining columns remain
independent Haar conditional on the first column and row
change. Every maximal minor that does not use the first row
is zero, whereas every one using it is, up to sign, \(t^{G_a}\)
times a maximal minor of the lower block.
That lower block is again an independent additive-Haar
matrix with one fewer row and column. Induction proves
full column rank over the fraction field almost surely,
and gives (3) for the valuation of the ideal of maximal minors.
Equivalently this is the sum of the nonnegative Smith
exponents \(v_1,\ldots,v_n\) over the power series ring:
in Smith form the ideal is generated by their diagonal
product, and invertible row and column changes preserve
the maximal-minor ideal. Modulo \(t^d\) the exponent
of the kernel order is \(\sum_j\min(d,v_j)\).
Thus \(K_d\to K_\infty\) almost surely under this coupling.
This is the same kind of local-field matrix computation as
[Evans's square determinant problem](https://www.sciencedirect.com/science/article/pii/S0304414902001874);
the rectangular maximal-minor valuation is all that is
needed here.

By tightness of \(K_d\), (8) and (12) give a stochastic upper
bound tending to \(\Phi(z)\) in probability. For example first
restrict \(K_d\) to a fixed bounded range, use (8), and then
let that range grow. The lower bound (11) on the mean, and
boundedness of probabilities, squeeze \(P_{\rm class}(A)\)
in \(L^1\) (and do so immediately at either endpoint).
This proves (2). Finally the expectation of \(2^{-G_a}\)
is \((1-2^{-a})/(1-2^{-a-1})\); multiplying these
independent factors telescopes to (4).

## 5. Prior scope

The algebra in (5) and the block repetitions belongs to the
classical repeated-root cyclic code setting; compare
[Castagnoli–Massey–Schoeller–von Seemann](https://www.isiweb.ee.ethz.ch/archive/massey_pub/pdf/BI433.pdf)
and the [ramified ideal noise calculations](ramified-ideal-tv-windows.md)
in this repository. The latter describe standalone Gaussian
mixing, not the optimum for this learning experiment.
The present use of both parity and repetition information,
the exclusion of nonzero identical-signal differences from
(10), and the finite kernel factor in (2) are specific to the
random-coefficient search problem. The
[fixed odd-modulus threshold](ring-lwe-fixed-odd-modulus-threshold.md)
does not give this phenomenon because of its different prime
decomposition as the dyadic degree grows. The
[standard continuous observation model](https://web.eecs.umich.edu/~cpeikert/pubs/ideal-lwe.pdf)
is used here with a specific ramified modulus and known product
error, not a conclusion about its hardness reductions or
a general algorithm. The finite checker corroborates the
binary ideal identities and small rectangular valuation
arithmetic on synthetic rings.
