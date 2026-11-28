# Fixed even moduli: the binary kernel factor persists under CRT

The [ramified binary theorem](ring-lwe-ramified-binary-rank-window.md)
proves a Gaussian transition for the optimal statistical success
modulo the public kernel at modulus two, together with a random
kernel factor for exact-label success. The same phenomenon holds
at every fixed even modulus, including mixed prime factors. What
requires proof is control of the other ideal directions: one cannot
infer it by treating the errors in the Chinese remainder components
as independent.

## 1. Statement

Let \(q\ge2\) be fixed and even, write \(q=2^e u\) with \(u\) odd
and \(e\ge1\), and let \(d\to\infty\) run over powers of two.
Use \(R_d=(\mathbb Z/q)[x]/(x^d+1)\) with coefficient-grid
embedding \(R_d\to\mathbb T^d,\ v\mapsto v/q\).
Fix integers \(m>n\ge1\). A public \(m\times n\) matrix has
independent uniform entries in \(R_d\), a hidden label is
uniform in \(R_d^n\), and response rows are the matrix times
the label in the signal grid plus independent coefficient
errors with circle density
\[
 f_b(t)=\sum_{j\in\mathbb Z}b^{j^2}e^{2\pi i jt},
 \qquad b=b_d\to b_*\in(0,1).
\]
This is the same continuous spherical model as in the
[fixed odd-modulus note](ring-lwe-fixed-odd-modulus-threshold.md),
but with a ramified prime factor. For each scalar grid
order \(\ell\) let \(C_\ell(b)\) be its mutual information with
this noise, as in that note. Write \(V_q(b)\) for the
variance under \(f_b\) of \(\log(f_b(t)/f_{b^{q^2}}(qt))\).

Let \(K_d(A)=\log_2|\ker A|\), including any odd prime factors
in the order inside the logarithm. Let \(P_{\rm class}(A)\)
and \(P_{\rm opt}(A)\) be the unrestricted optimal probabilities
conditional on the matrix for identification modulo \(\ker A\)
and exact identification, respectively. If
\[
  \frac{dm C_q(b_d)-dn\log q}{\sqrt{dm V_q(b_d)}}
      \longrightarrow z\in[-\infty,\infty],
 \tag{1}
\]
then
\[
 \begin{split}
  P_{\rm class}(A)&\to\Phi(z)\quad\text{in }L^1(A),\\
  \mathbb E_A|P_{\rm opt}(A)-2^{-K_d(A)}\Phi(z)|&\to0,\\
  K_d(A)&\Longrightarrow \sum_{j=0}^{n-1}G_{m-j},\qquad
     \Pr(G_a=k)=(1-2^{-a})2^{-ak},
 \end{split} \tag{2}
\]
where the \(G_a\) are independent.
In particular the averaged exact success tends to
\[
       \frac{1-2^{-(m-n+1)}}{1-2^{-(m+1)}}\,\Phi(z).
 \tag{3}
\]
The formula is identical to the binary rank factor, but the
scalar information in (1) is the **full \(q\)-grid** quantity,
not the sum of independent statistics at the separate primes.
No runtime conclusion, concrete parameter estimate, or
hidden-label procedure is involved.

## 2. Information inequalities by choice of CRT order

Write \(a=2^e\). A nonzero ideal of \(R_d\) has a ramified
component \(H_a\) and, if \(u>1\), an odd component \(H_u\).
For a subgroup \(H\) write \(D_H(b)\) for the mutual information
of its uniform grid input plus the product wrapped \(f_b\)-noise.
Equivalently \(D_H(b)=D(p_b\Vert P_Hp_b)\), where \(P_H\)
averages over the subgroup shifts, by observation density
invariance. Take \(D_{\{0\}}(b)=0\).

For \(u>1\) the uniform CRT input has the sum form
\(X_a/a+X_u/u\bmod1\), with the two subgroup inputs independent.
The CRT unit multipliers do not change the uniform subgroup
laws. Revealing \(X_u\) makes its shift known, and the observation
\(aY\bmod1\) deletes the \(a\)-component and multiplies the
noise width by \(a\), equivalently changing the nome to \(b^{a^2}\).
Multiplication by \(a\) on the \(u\)-component is a unit and
also preserves the subgroup law. The mutual information
chain rule and data processing therefore give both bounds
\[
 \begin{split}
 D_H(b)&\ge D_{H_a}(b)+D_{H_u}(b^{a^2}),\\
 D_H(b)&\ge D_{H_u}(b)+D_{H_a}(b^{u^2}).
 \end{split} \tag{4}
\]
These are bounds obtained by **two different orders** of the
chain rule on the same observation, not an independence
claim about its errors.

Put \(c(b)=C_q(b)/\log q\) and
\(\alpha=\log|H_a|/(d\log a),\ \beta=\log|H_u|/(d\log u)\).
The [strict scalar ratio and cyclic bound](logtime-wrapped-gaussian-ideal-bottleneck.md)
give \(C_\ell/\log\ell\) strictly decreasing in \(\ell\)
and \(D_{H_a}(b)\ge\alpha d C_a(b)\), similarly for other
components and widths. Also
\(C_q(b)=C_a(b)+C_u(b^{a^2})=C_u(b)+C_a(b^{u^2})\)
by the scalar entropy-difference formula (the same channel
chain rule as [Luzzi–Ling–Bloch, Appendix B, (43)](https://arxiv.org/abs/2206.10443)).
Thus the first and second lines of (4), respectively,
give lower bounds on \(D_H(b)-c(b)\log|H|\) of
\[
      d\theta_a(b)(\alpha-\beta),\qquad
      d\theta_u(b)(\beta-\alpha),
 \tag{5}
\]
where \(\theta_\ell(b)=C_\ell(b)-c(b)\log\ell>0\)
for \(\ell=a,u\). If \(H_u\) is neither full nor zero,
there is in addition a uniformly positive multiple of \(d\)
in **both** bounds. Indeed the odd-modulus fixed-base
stabilization gives \(d/d_0\) copies of one of finitely many
proper nonzero base ideal types; the cyclic bound is
strict on each and the scalar widths \(b,b^{a^2}\) stay
in compact interior sets. Its uniform per-block gap adds
\(\Omega(d)\). Choose in (5) the order with a nonnegative
first term. This proves a uniform \(\Omega(d)\) excess
for all ideals with nontrivial proper odd component.

If \(H_u\) is full, choose the second line in (5):
the excess is \(\Omega(d(1-\alpha))\).
If \(H_u\) is zero and \(H_a\ne0\), choose the first:
the excess is \(\Omega(d\alpha)\).
The constants are uniform on a compact neighborhood of \(b_*\).
Thus, for \(u>1\), only the large and small ends of the
ramified depth require further control.

## 3. The pure prime-power case and the two ends

Let \(O_d=\mathbb Z[\zeta_{2d}]\). At the prime above two it
has uniformizer \(1-\zeta_{2d}\), denoted \(\pi\), with
\(2O_d=\pi^d O_d\). One elementary verification is that
\(|N(1-\zeta_{2d})|=2\) and that the reduction modulo two is
\(\mathbb F_2[x]/((x+1)^d)\), which has only one maximal ideal.
Thus the ramified component modulo \(a=2^e\) is a chain;
its ideal of depth \(r\in[0,ed]\) has size \(2^{ed-r}\).
For \(r<d\) this ideal is the full inverse image of the
binary ideal \((x+1)^r\) under reduction modulo two.
For \(k=d e-r\le d\) it is \(2^{e-1}\) times the binary
dimension-\(k\) ideal of depth \(d-k\), since
\((\pi^{d})=(2)\). These identities also describe the two
ends of the ramified component when \(u>1\).

Suppose \(u=1\) and \(e\ge2\); \(e=1\) is the cited binary theorem.
For \(r<d\), conditioning a uniform full grid source to depth
\(r\) means imposing a full-rank \(r\)-bit linear constraint
on the least significant bits. Each single-coordinate parity
observation has information \(C_2(b^{(a/2)^2})\): condition on
parity, average over the \(a/2\) high-digit alternatives, and
multiply the circle by \(a/2\). This quotient keeps the whole
likelihood of parity because its two conditional densities
are already periodic under \(1/(a/2)\).
Revealing nonpivot parity bits shows that information about
the \(r\)-bit constraint from all the observations is at most
\(r C_2(b^{(a/2)^2})\) by the same pivot-information argument
as in the binary proof. Subgroup invariance gives this
information as \(D(P_Hp_b\Vert P_{R_d}p_b)\).
Since \(D_H=d C_a(b)-D(P_Hp_b\Vert P_{R_d}p_b)\),
\[
 D_H-c(b)\log|H|\ge
           r\bigl(C_a(b)/e-C_2(b^{(a/2)^2})\bigr).
 \tag{6}
\]
The parenthesis is strictly positive. Indeed
\(C_a(b)=\sum_{j=0}^{e-1} C_2(b^{4^j})\) by telescoping,
and \(C_2(b)\) is strictly increasing in \(b\):
strict log-heat-time concavity makes
\(h(4t)-h(t)\) strictly decreasing in \(t=-\log b\).
Thus the last summand is strictly less than the average.

For \(r\ge d\) the subgroup is contained in the coordinate
even grid. In the conditional coordinate chain every
nontrivial subgroup order is at most \(a/2\). The scalar
ratio ordering thus gives
\(D_H(b)\ge [C_{a/2}(b)/\log(a/2)]\log|H|\)
by the chain bound, with a strict positive gap above
\(c(b)\) per unit of \(\log|H|\). This proves the required
middle-depth gaps for the pure even prime powers.

Now set \(h_d=\lfloor d/(C_1\log d)\rfloor\) for \(C_1\) large
depending only on the fixed parameters and width compact set.
Define near-full ideals as those with full odd component
(if present) and ramified depth \(r\le h_d\).
Define near-zero nonzero ideals as those with zero odd
component (if present) and \(1\le ed-r\le h_d\).
All other proper nonzero ideals are middle. Equations
(5)–(6) and the even-grid bound show that for every middle
ideal
\[
         D_H(b)-c(b)\log|H|\ge c_1 d/\log d
 \tag{7}
\]
with a fixed positive \(c_1\). For the binary \(e=1,u=1\)
case this is the middle bound already proved in the binary
theorem. The number of ideals is \(O_q(d)\), by the chain at
two and fixed-base stabilization at odd primes.

## 4. Applying the three-range statistical argument

For each \(H\) let \(T_H=\sum_i\log(p_b(E_i)/P_Hp_b(E_i))\).
The full \(T_{\rm all}\) is a sum of \(md\) independent
scalar increments of variance \(V_q(b)\), bounded and
bounded away from variance zero on the width interval.
The CLT in (1) with either threshold shift
\(\gamma_d=d^{1/4}\) gives \(\Phi(z)\).

For near-full \(H\), uniform full \(q\)-grid input has
independent binary least significant bits; membership in
\(H\) imposes only the binary ideal constraint of depth \(r\)
on these bits. The posterior of the bits given the product
output is a product, and every scalar posterior parity sign
has absolute value at most \(\rho<1\) uniformly: both
parities give everywhere-positive continuous output densities.
The ratio of the conditioned to full observation densities
is the sum of products of these signs over the binary dual
ideal, by orthogonality of binary characters.
The dual of the depth-\(r\) binary ideal repeats
\(L\ge d/(2r)\) times as in the binary proof.
Thus \(\|P_Hp_b/P_{R_d}p_b-1\|_\infty=O(d^{-4})\)
by the bound \((1+\rho^L)^{d/L}-1\) and large \(C_1\).
Consequently \(T_H=T_{\rm all}+o(1)\) uniformly
for this range. On \(T_{\rm all}>dn\log q+\gamma_d\),
the near-full sum of \(|H|^n e^{-T_H}\) is
\(O(e^{-\gamma_d})\), since
\(|H|/|R_d|=2^{-r}\).

For the middle ideals, when \(z\) is finite or \(+\infty\),
(7) gives \(mD_H(b)-n\log|H|=\Omega(d/\log d)\):
the center difference of the full direction at finite \(z\)
is \(O(\sqrt d)\), and at \(+\infty\) it is eventually
nonnegative. Changing one raw error coordinate changes
the log ratio by a bounded amount, by the scalar
density upper and lower bounds; hence bounded differences
and a union over \(O_q(d)\) inequalities give
\(T_H>n\log|H|+\gamma_d\) for every middle \(H\)
with probability \(1-o(1)\). Their summed ratio
bound is \(O_q(d e^{-\gamma_d})\).

For near-zero \(H\), the grid signals are binary half-shifts
of the repeated ideal of dimension \(k=ed-r\).
For a difference \(v\) generating \(H\), the row shifts
\(Av\) are uniform in \(H^m\) over the public matrix.
In bounding the loss of posterior mass of the true class,
omit differences with \(Av=0\) first; these do not count
as class errors. Then the Hellinger fractional-moment sum
over all differences of this ideal type is at most
\[
       2^{(n-m)k}\bigl((1+\kappa^L)^{mD}-1\bigr),
       \qquad D=d/L,\quad L\ge d/(2k),
\]
where \(\kappa<1\) uniformly bounds the scalar half-shift
affinity on the compact width interval. Indeed the
shift weight enumerator of the repeated binary subspace
is bounded by the enumerator for all \(D\)-bit base words,
and the omitted zero shift accounts for the subtraction 1.
As in the binary proof, this summed contribution is \(o(1)\)
for large \(C_1\).

These three estimates apply the same posterior collision
comparison as in the binary theorem to show
\(\mathbb E_A P_{\rm class}(A)\ge
\Pr(T_{\rm all}>dn\log q+\gamma_d)-o(1)\).
In detail, the sum of likelihood ratios outside the true
class is averaged over \(A\) with fixed errors in the
first two ranges, where the expectation for a difference
of ideal type \(H\) is \(e^{-T_H}\); there are at most
\(|H|^n\) such differences. In the third range its
loss after truncating at 1 is at most the sum of the
square-root ratios with the same-signal differences
removed. The bounds therefore control exactly the
posterior class loss, without any independence claim
between the different directions.
For negative infinite \(z\) only the upper bound is needed.
For fixed \(A\), change of measure using \(P_{R_d}p_b\)
as reference gives a pointwise upper bound
\[
 P_{\rm class}(A)\le
  \Pr(T_{\rm all}>dn\log q-\log|\ker A|-\gamma_d)+e^{-\gamma_d}.
 \tag{8}
\]
Indeed the reference response is independent of the
uniform class and there are \(q^{dn}/|\ker A|\) classes.

## 5. The kernel law is still the binary law

At any odd prime factor of the fixed modulus, the residue
degree is a fixed positive fraction of \(d\) and the
number of primes over it is eventually fixed, by the
odd stabilization lemma. A uniform \(m\times n\) matrix
over a residue field of size \(Q\) is not of full column
rank with probability at most \(Q^{n-m}\), by a union
over nonzero vectors. Consequently all these odd components
are injective with probability \(1-o(1)\); a full-rank residue
minor is a unit across the whole primary component.

At two, lift the public matrix to independent additive-Haar
entries over the completed discrete valuation ring at \(\pi\)
and reduce modulo \(\pi^{ed}\). Its residue field is
\(\mathbb F_2\). The local-field maximal-minor argument of
the binary theorem uses only that residue field size:
the minimum valuation in an \(s\)-entry first column is
\(G_s\), primitive elimination leaves an independent
Haar lower block, and maximal minors carry the first
column factor. Thus the sum of the infinite valuation ring
Smith exponents has the law in (2), independently of
the ramification degree. The kernel exponent upon truncation
is the sum of those exponents capped individually at \(ed\);
the discrepancy probability is at most the tail probability
of the uncapped sum past \(ed\), which tends to zero.
This proves tightness and the claimed limit of \(K_d(A)\),
also when the rare odd-component failures are allowed.

Tightness makes the upper bound (8) converge in probability
to \(\Phi(z)\). The averaged lower bound and boundedness
therefore yield \(L^1\) convergence of \(P_{\rm class}\).
Every class has exactly \(|\ker A|\) equiprobable identical
labels, giving the second line of (2), and the same
geometric telescoping mean as in the binary theorem gives (3).

## 6. Scope

The additional ingredients beyond the binary proof are the
choice of CRT information order, the uniform fixed-base gap
for the odd component, and the high-digit/least-significant-bit
comparison for a pure even prime power. These are positive
information-limit statements in a known product-noise
observation model. They do not identify or evaluate any actual
scheme, imply an efficient estimator, cover growing modulus
or growing matrix shape, or change the assumptions of
[the general Ring-LWE hardness reductions](https://web.eecs.umich.edu/~cpeikert/pubs/rlwe-anyring.pdf).
The companion exact arithmetic checks use only synthetic
finite rings.
