# A calibrated completion of two small factors removes every negative rank-four value

This is a correction of the **uncapped** arithmetic proxy in
[the hyperbolic evaluation](../hyperbolic_composite_proxy/Proof.md).
It adds the missing two-prime cofactor terms and pays their
actual progression mean by a separate term supported first at
an arbitrarily prescribed higher rank. It does not assume
independence of true prime factors in a common-index column.
The resulting signed proxy still tracks the true tagged prime
columns, but now is nonnegative on every squarefree integer
of rank at most four.

Use \(N=2x,\ Y=\sqrt{x},\ L=\log x,\ \ell=\log L,\ z=\exp(L/\ell^2)\),
\(R=x^{.505},\ R_z(y)=1_{\{P^-(y)>z\}}\), and \(y\in[x,3x/2]\)
as in the hyperbolic calculation.
Fix an odd integer \(m\ge3\), then fix \(0<\epsilon<.04/m\).
All parameters are chosen before \(x\) tends to infinity;
nothing below is uniform in growing \(m\).
Put \(C_y=y/x^{1-\epsilon}\),
\[
 K(y)=R_z(y)\sum_{\substack{a\mid y\\a>R}}\mu(a)\log(y/a),\qquad
 S(b)=\sum_{\substack{a\mid b\\a>R}}\log(b/a).
\]
The previous exact proxy was
\[
 R_\epsilon(y)=K(y)+R_z(y)\sum_{\substack{c\mid y\\c<C_y}}
                                    \mu_2(c) S(y/c),
 \quad \mu_2=\mu*\mu .
\]

Let \(\mathcal P_y\) be the set of products \(pq\) of **two distinct**
genuine primes with \(z<p<q<C_y\) and \(pq\ge C_y\).
Let \(\mathcal H\) be the set of products of \(m\) genuine primes,
one in each of \(m\) fixed disjoint nonempty multiplicative
exponent intervals in \((.4\epsilon,.8\epsilon)\).
For example take the \(j\)-th exponent interval
\((.4\epsilon+.35(j-1)\epsilon/m,\,
   .4\epsilon+.35(j-1)\epsilon/m+.1\epsilon/m)\)
for \(1\le j\le m\).
Every prime in \(\mathcal H\) exceeds \(z\) for large \(x\),
and every such product exceeds \(C_y\); the factorization
ordering in these disjoint bands is unique.

Define the two actual scores
\[
 A_+(y)=4R_z(y)\sum_{\substack{c\mid y\\c\in\mathcal P_y}} S(y/c),
 \qquad
 A_-(y)=2^m R_z(y)\sum_{\substack{c\mid y\\c\in\mathcal H}} S(y/c).
                                                                    \tag{1}
\]
The signs \(+4\) and \(-2^m\) are precisely
\(\mu_2(pq)\) and \(\mu_2(p_1\cdots p_m)\) on squarefree cofactors;
the latter sign is negative because \(m\) is odd.
Here neither score is a formal Euler mean substituted
for its arithmetic values.

There is an explicit nonnegative function \(\lambda(y)\) defined below,
independent of the modulus, residue, slope, or target, so that
\[
       R^\ast(y)=R_\epsilon(y)+A_+(y)-\lambda(y)A_-(y)              \tag{2}
\]
has the following properties.

**Theorem.**
1. For every fixed \(\delta,A>0\), uniformly for
\(Q\le x^{(2/3)(1-m\epsilon)-\delta}\), each reduced class
\(j\bmod Q\) and every \(J\subseteq[x,3x/2]\),
\[
 \sum_{\substack{y\in J\\y\equiv j\bmod Q}}
          [A_+(y)-\lambda(y)A_-(y)]
                       =O_{\epsilon,m,\delta,A}((x/Q)L^{-A}).    \tag{3}
\]
2. On the original true two-tag box \(Q=kp_2p_3\le x^{.6092}\),
(2) has the same signed transfer to the actual log-prime columns
as \(R_\epsilon\), including arbitrary allowed opposite divisor
weights and the corrected centered variance.
3. \(R^\ast\) is zero on primes and squarefree semiprimes, and
**nonnegative on every squarefree rank-three or rank-four integer**.
The negative correcting term in (2) cannot affect any
squarefree rank \(\le m+1\) at all. Thus at any prescribed
fixed higher rank cutoff one can leave only a pointwise
nonnegative modification of \(R_\epsilon\) below that cutoff
by taking \(m\) sufficiently large beforehand.
This last monotonicity does not assert that \(R_\epsilon\)
or \(R^\ast\) has a favorable sign on ranks five and higher.

## 1. Exact free-variable main for a fixed cofactor

Put \(\xi=.10\) as in the direct hyperbolic argument, and set
\[
 H_Q=\sum_{\substack{s\le x^\xi\\(s,Q)=1}}R_z(s)\frac{\log s}{s},
 \qquad
 \omega_z(Q)=\frac{\varphi(Q)}Q W_z(Q),\qquad
 W_z(Q)=\prod_{\substack{p\le z\\p\nmid Q}}(1-1/p).
\]
For a fixed polynomial cofactor \(c\le 3x^{m\epsilon}\)
that is rough and coprime to \(Q\), the physical progression
sum of \(R_z(y)1_{c\mid y} S(y/c)\), in any interval \(J\)
of the macroscopic box, has principal
\[
        \frac{\varphi(Q)W_z(Q)^2}{Q^2 c}
                \int_J J_{c,Q}(y)\,dy ,
 \quad
 J_{c,Q}(y)=\frac{H_Q}{\omega_z(Q)}
       +\tfrac12[(\log(y/(c R)))^2-(\xi L)^2].                     \tag{4}
\]
For nonunit \(c\) the literal progression contribution is zero.
No coprimality between separate actual factors of \(y\) is inserted
beyond the reduced residue.

Here are the complete uniform error details needed in (4).
Using \(y=sca\), \(a>R\), if \(s\le x^\xi\) then
\(a\gg x^{1-\xi-m\epsilon}\) and the lower bound \(a>R\)
is automatic. Keep the true rough \(s\) and count \(a\) in
its literal reduced residue using the one-free floor argument.
It gives \(W_z(Q)/Q\) times interval length, with negligible
factorial-tail error and floor error
\(x^{\xi+o(1)}\) per \(c\) before summing.
This is the first term of (4), no approximation of the
true short rough \(s\)-sum being made.

For \(s>x^\xi\), open both independent roughness factors
on the free integers \(s,a\) using Bonferroni. For the
absolute error, the two product approximants differ from
their true indicators by at most
\(E(s)+E(a)+E(s)E(a)\), with \(E\) the next positive degree.
This reduces every error to the identical two-free rectangle
count used in the hyperbolic proof. The two opened divisors
are subpower, and if either is not coprime to \(Q\) its
literal term is zero. The local main is \(\varphi(Q)/Q^2\)
times both free lengths. Its two finite rough Euler factors
complete independently to \(W_z(Q)^2\). Absolute
factorial tails save arbitrary log powers at the fixed
cofactor \(c\) on the \(x/(Qc)\) main scale.

The arbitrary \(J\)-endpoints and independent \(a>R,\ s>x^\xi\)
cuts may be imposed on log-fine relative rectangles, allowing
the unresolved cases by the same positive count.
For each \(c\) a relative product strip of width \(L^{-B}\)
costs principal volume \(O(xL^{-B}/c)\); for a
coordinate endpoint its relative strip is estimated in
the same way. The total number of needed rectangles is a
fixed log power. Because the proof is uniform in every
prefix \(J\), these estimates also bound the supremum of
the errors after each fixed \(c\) over such prefixes.
With actual dyadic scales \(C,S_0,W_0\) for \(c,s,a\),
one has \(CS_0W_0\asymp x\) on a relevant rectangle,
\(S_0\gg x^\xi\), and \(W_0\gg R\).
The first nonzero rectangle error summed over all these
\(c\)'s, both opened divisor lists and boxes is
\(x^{m\epsilon+o(1)}Q^{1/2+\nu}\) with arbitrarily small
fixed \(\nu>0\). This saves a power relative to \(x/Q\)
on the stated modulus range. The second is
\(x^{o(1)}(x/S_0+x/W_0)Q^{-1+\nu}\)
and saves a power there as well.
The summed short-\(s\) floor error is
\(x^{\xi+m\epsilon+o(1)}\), also admissible.
Integrating the long \(s\)-part in \(y=sca\) gives
\(\frac12[(\log(y/(cR)))^2-(\xi L)^2]\), with \(1/c\)
as in (4). The interval is nonempty uniformly since
\(m\epsilon<.04\).
Thus the **sum over all \(c\)** of the individual
supremum errors in (4) is \(O((x/Q)L^{-A})\) for every
fixed \(A\), with constants for the fixed parameters.
Higher accuracy can therefore absorb any fixed
logarithmic variation of a real \(y\)-weight.

## 2. A single arithmetic calibration for all moduli

In (4) the common short-\(s\) quotient can be made
independent of \(Q\), to more than the required accuracy.
Indeed
\[
 \omega_z(Q)=V_z\prod_{\substack{p\mid Q\\p>z}}(1-1/p),
 \qquad V_z=\prod_{p\le z}(1-1/p).
\]
The relative difference from \(V_z\) is \(O(L/z)\).
Because \(s\) is already rough, deleting its prime factors
of \(Q\) removes only \(p>z\); hence
\[
 0\le H_1-H_Q
 \ll\sum_{\substack{p\mid Q\\p>z}}\frac1p
               \sum_{t\le x^\xi/p}\frac{\log(pt)}t
 \ll L^3/z.
\]
Thus \(H_Q/\omega_z(Q)=H_1/V_z+O(L^C/z)\)
uniformly. Put
\[
           J_c(y)=\frac{H_1}{V_z}
                 +\tfrac12[(\log(y/(cR)))^2-(\xi L)^2].
\]
On all admitted \(c\le3x^{m\epsilon}\) these are positive
and comparable to \(J_0=H_1/V_z+L^2\);
their variation in \(y\in[x,3x/2]\) is \(O(L)\).
Now define the exact, modulus-independent scalar
\[
 \lambda(y)=
  \frac{4\displaystyle\sum_{c\in\mathcal P_y} J_c(y)/c}
       {2^m\displaystyle\sum_{c\in\mathcal H} J_c(y)/c}.            \tag{5}
\]
Its denominator is \(\asymp_m J_0>0\) by the
positive reciprocal prime mass in the mutually disjoint
fixed exponent intervals. Its numerator is \(O(J_0)\):
the reciprocal sum of pairs \(p,q<C_y\) with product
\(\ge C_y\) is bounded uniformly. To check this directly,
put \(u=\log p/L,\ v=\log q/L,\ \epsilon_y=\log C_y/L\);
the domain is \(u,v<\epsilon_y,\ u+v\ge\epsilon_y\).
For \(u<\epsilon_y/2\), \(v\) lies in an exponent interval
of width \(u\) with \(v\ge\epsilon_y/2\), whose reciprocal
prime mass is \(O((u+L^{-1})/\epsilon_y)\) by ordinary
dyadic prime upper bounds. The \(u\)-sum of that bound
is \(O(1)\) since \(p>z\).
If both exponents exceed \(\epsilon_y/2\), the two
reciprocal prime sums are each bounded.
Thus \(\lambda(y)=O_m(1)\) for fixed parameters.

For each pair \(c=pq\), membership in \(\mathcal P_y\)
means a literal interval in the physical variable \(y\):
\(y>\max(p,q)x^{1-\epsilon}\) and
\(y\le pq x^{1-\epsilon}\).
It creates at most two jumps. Summing their weighted
absolute variations costs at most
\(O(J_0(\log\ell)^2)\), using just
\(\sum_{z<p\le2x^\epsilon}1/p=O(1+\log\ell)\).
The continuous terms \(J_c(y)\) have the smaller
variation described above. The denominator of (5)
has variation \(O_m(L)\) and positive minimum
\(\gg_m J_0\). The quotient therefore has total
variation \(O_m((1+\log\ell)^2)\).
This is enough for ordinary partial summation against
the uniform fixed-\(c\) progression prefixes in (4);
no smooth approximation across the actual finite jumps
of \(\lambda(y)\) is necessary.

For the reduced progression models, reinstate
\((c,Q)=1\) after writing (5). All the primes of a
marked \(c\) are \(>z\), so the harmonic weight lost
by this restriction costs
\(O_m((L/z)(1+\log\ell)^{m-1})\).
The error from \(J_{c,Q}-J_c=O(L^C/z)\) similarly
saves more than arbitrary logs after summation.
Thus the two signed models cancel exactly in the
unmasked normalization (5), with negligible difference
for the actual reduced progression. Applying the
prefix estimates with these weights proves (3).

For the true tagged columns, restoring the additional
\((y,N)=1\) condition costs arbitrary logs in each
actual reduced class: the deleted rough \(y\)'s have a
prime \(>z\) dividing \(N\), and the fixed row divisor
bounds and Shiu apply as in the hyperbolic proof.
Indeed \(|A_+-\lambda A_-|\ll_m L\tau_4(y)\).
The harmonic sum over marked \(Q=kp_2p_3\) is the
same as there. Hence the correction is \(O_A(YL^{-A})\)
in each true tagged column. Comparing with the established
hyperbolic transfer proves the second conclusion of the
theorem, including the unchanged centering and
opposite-row divisor clipping.

## 3. Exact sign for every squarefree rank at most four

The new nonnegative correction in (1) completes precisely
the missing **distinct** two-small-prime terms.
It introduces no second copy of an originally admitted
cofactor: the original inequality was \(c<C_y\).
For squarefree \(y\), it is enough to work on the rough
support. The number of eligible small primes means the
number \(<C_y\), with equality not eligible.
The negative correction is identically zero if
\(\omega(y)\le m+1\), since a divisor \(c\in\mathcal H\)
then leaves \(y/c=1\) or a genuine prime, and \(S\)
is zero on both. This includes all ranks considered next.

With no or one small prime, no two-prime completion is
needed; the previous exact nonnegative sign applies.
On primes and squarefree semiprimes (1) also vanishes,
so their zero score persists.

Suppose squarefree \(y\) has exactly two eligible small
primes \(p,q\). Write \(P=pq\) and \(M=y/P\).
Every \(c\mid P\) is now included, with the exact
coefficient \(\mu_2(c)\), and no other \(c\) can occur.
For each \(d\mid M,\ b\mid P\) with free divisor
\(a=db>R\), sum all original outer labels and
cofactors at that same \(a\).
Writing \(L_M=\log(M/d)\), \(L_P=\log(P/b)\),
the sum of its raw and completed parts is
\[
 \begin{split}
 &\mu(d)\mu(b)(L_M+L_P)
    +\!\sum_{c\mid P/b}\!\mu_2(c)
                  (L_M+\log(P/(bc)))\\
 &=\mu(b)\{\,(\mu(d)+1)L_M+(\mu(d)-1)L_P\,\}.                     \tag{6}
 \end{split}
\]
Here \(\sum_{c\mid P/b}\mu_2(c)=\mu(P/b)=\mu(b)\),
and \(\mu_2*\log=\mu*\Lambda\) equals
\(-\mu(P/b)\log(P/b)\) on the squarefree \(P/b\).
Thus all \(s\)-assignments are included exactly, not just
the initial missing pair label.

At rank four \(M=B C\) is a product of two other primes.
For \(d=1\), no \(b\) qualifies, since \(P\le(1.5x^\epsilon)^2<R\).
For \(d=BC\), \(L_M=0\) and \(\mu(d)=1\), so (6) is zero.
For either \(d=B,C\) with \(\mu(d)=-1\), the admissible
\(b\)'s are a terminal set among \(1,p,q,pq\),
ordered by size. If all are admitted, their total is zero
because \(\sum_{b\mid P}\mu(b)\log(P/b)=\Lambda(P)=0\).
If \(1\) is not admitted, each admitted
\(p,q\) contributes nonnegatively and \(pq\)
contributes zero. This proves the requested sign even
when a raw divisor crosses the \(R\)-threshold.
For rank three the same proof applies with \(M\) one
prime, just using \(d=1,M\).
No angular approximation has been used.

If there are three eligible small primes on a rank-four
integer, the other prime \(g\) exceeds \(R\), since
the product of the three small primes is at most
\((1.5x^\epsilon)^3\). Four eligible small primes are
impossible at this \(y\)-scale. Write \(P=y/g\);
every admitted free or raw divisor \(a\) includes \(g\)
because \(P<R\). The only potentially missing small
cofactor after filling pairs is \(c=P\), but \(S(g)=0\),
so it can be inserted freely. The raw value is
\(-\Lambda(P)=0\), and the completed score is
\[
 \sum_{c\mid P}\mu_2(c)S(y/c)
   =2^{\omega(P)-1}\sum_{c\mid P}\mu(c)\log(P/c)
   =2^{\omega(P)-1}\Lambda(P)=0 .
\]
(The \(P/c=1\) term has zero log.)
Three small primes at rank three are impossible.
This proves all the pointwise statements.

Only this uncapped branch is asserted here.
A separate cap in the free variable would introduce a
new upper-endpoint sign issue; the exact rank-four sign
is not inherited by an arbitrary cap. Nor does this
proof control all higher ranks.
The remaining natural-scale adverse mass must now come
from actual rank at least five (apart from negligible
rough nonsquarefree rows); the newly chosen negative
payer first appears at rank \(m+2\).
Its coefficient is bounded for each fixed \(m\) but no
uniform smallness or \(m\)-limit is claimed.
The usual full rough absolute opposite bound from
\(\tau_4\) and Shiu still costs a factor \(\ell^8\);
the signed correction itself pays it by arbitrary-log
precision, but an unrelated unsigned rank-tail bound
cannot drop it. No conclusion on the sign or smallness
of the full centered covariance follows.

