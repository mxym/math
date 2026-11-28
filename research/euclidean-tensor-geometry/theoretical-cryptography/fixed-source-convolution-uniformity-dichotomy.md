# An additive-support dichotomy for exact uniformity of known linear convolutions

**Scope.** The input is a complete forward specification: independent copies of
one fixed finite probability table and supplied linear maps. No observations or
hidden quantities enter the question. The decision is exact uniformity of this
mathematical law, not a sample test or a claim about an implemented scheme.

Fix a finite field \(F=\mathbb F_q\) of characteristic \(p\), a positive integer
\(r\), and a rational probability law \(\nu\) on \(F^r\). Use the trace character
to identify the dual with \(F^r\), and let
\[
                         R=\{u\in F^r:\widehat\nu(u)\ne0\}.
\]
The field, \(r\), and \(\nu\) are fixed throughout the complexity statements.
Given a list of linear maps \(A_i:F^r\to F^d\), consider
\(Z=\sum_i A_i X_i\), where the \(X_i\) are independent with law \(\nu\).
The ambient dimension and maps are explicitly represented.

**Theorem.**
1. If \(R\) is an additive subgroup, exact uniformity of \(Z\) is decided by
   Gaussian elimination over \(\mathbb F_p\). The size of the Fourier support
   is computed exactly in polynomial bit time as well. It is not necessary for
   \(R\) to be an \(F\)-linear subspace.
2. If \(R\) is not an additive subgroup, exact uniformity is coNP-complete.
   Counting the nonzero frequencies in the Fourier support of \(Z\) is
   \(\#\mathrm P\)-complete under polynomial-time metric reductions.
   Both hardness statements hold with every \(A_i\) injective, with the image
   of each supported on at most a constant number of ambient coordinates, and
   with each ambient coordinate involved in at most a constant number of maps.
   The constants depend on the fixed template \(F,r,\nu\), not on \(d\) or the
   number of sources.
3. If \(\nu\) is everywhere positive, the hardness in (2) still holds in the
   injective-map model under a promise that the law is within \(2^{-L}\) total
   variation of uniform, with \(L\) given in unary. The amplification in this
   statement is not claimed to preserve the bounded occurrence in (2).

Thus additivity of the one fixed Fourier support gives a complete criterion
for which side of the decision frontier applies, subject to the usual
\(\mathrm P\) versus coNP distinction.

## 1. A forward-law condition

Write \(T_i=A_i^\top\) in the fixed trace-pairing coordinates. Independence gives
\[
 \widehat{\mathcal L(Z)}(u)=\prod_i\widehat\nu(T_i u),\qquad
 \mathcal R_Z=\{u:T_i u\in R\text{ for all }i\}.                    \tag{1}
\]
Fourier inversion says that \(Z\) is uniform if and only if
\(\mathcal R_Z=\{0\}\). The test at each supplied frequency is exact.
For a rational probability table, group probabilities according to the trace
values \(j\in\mathbb F_p\). The \(p\) resulting rational sums are the coefficients
of a polynomial evaluated at \(\zeta_p\). It vanishes there exactly when all
those coefficients agree, by the minimal polynomial \(1+z+\cdots+z^{p-1}\).
This also gives coNP membership and \(\#\mathrm P\) membership for the
number of nonzero frequencies.

If \(R\) is additive, it is an \(\mathbb F_p\)-linear subspace. Pull back its
linear defining equations under all \(T_i\), which are \(\mathbb F_p\)-linear.
Stacking the resulting matrices gives \(\mathcal R_Z\) as one kernel, so its
cardinality is \(p^{\dim_{\mathbb F_p}\mathcal R_Z}\).

## 2. A zero-unique and parsimonious linear gadget

Suppose that \(R\) is nonadditive. It contains \(0\), is proper, and contains a
nonzero vector. Let
\[
                               S=\{s\in F^\times:sR=R\}.
\]
For any fixed positive integer \(m\), consider the homogeneous conjunction
on \(w=(w_1,\ldots,w_m)\in F^m\)
\[
       \sum_{j=1}^m w_j v_j\in R
             \qquad\text{for every }(v_1,\ldots,v_m)\in R^m.       \tag{2}
\]
Its solutions are precisely \(0\) and the \(s e_j\) with \(s\in S\).
Indeed, setting all \(v\)'s except one to zero proves \(w_jR\subseteq R\).
A nonzero \(w_j\) must therefore be in \(S\) by equal cardinality.
If two coefficients are nonzero, use their inverses in the two positions
to require every \(a+b\), \(a,b\in R\), to lie in \(R\), a contradiction.
The converse is immediate. This is a linear version of the classical
canonical relation construction; the precise treatment of the zero
fiber below is important because all our instances have a zero solution.

Now let \(B\subseteq\{0,1\}^k\) be a nonempty set of allowed Boolean tuples,
with \(k\) bounded. List its distinct members \(b^{(1)},\ldots,b^{(m)}\).
For exposed variables \((t,x_1,\ldots,x_k)\) use (2) and the linear equations
\[
                   (t,x)=\sum_{j=1}^m w_j(1,b^{(j)}).             \tag{3}
\]
If \(t=0\), (2) and (3) give exclusively \(x=w=0\).
If \(t\ne0\), the exposed tuples are exactly
\((t,t b^{(j)})\) for \(t\in S\), and every exposed tuple has **one**
extension, \(w=t e_j\). The same remains true when \(k=1\) with both
Boolean values permitted. The conjunction is constant size for
fixed \(F,R,k\).

Apply the construction to each signed 3-clause of a Boolean formula, taking
its seven satisfying tuples. Also use a one-bit gate for each original
variable, including isolated ones if the counting version has them.
Use separate activation and variable copies for all gate appearances.
Equate all activation copies by a chain of two-variable linear equations.
Equate the copies of each Boolean variable in the same way, including its
bit gate. All-zero exposure has just the all-zero extension by (3).
For each satisfying Boolean assignment, all gates may take the common
activation \(t=s\) for any one \(s\in S\), and there is a unique extension
per choice. Conversely, any nonzero solution has common activation in \(S\);
dividing exposed values by it gives the satisfying Boolean assignment.
In particular the number of nonzero solutions is
\[
                              |S|\,\#\mathrm{SAT}(\phi).         \tag{4}
\]
A formula with no gates can be avoided by adding one pinned Boolean
variable to the original formula; alternatively handle that case directly.
The construction uses only fixed-arity homogeneous \(R\)-pullbacks and
homogeneous single equations, with a constant number of occurrences of each
variable. Repetition of a variable or a literal in a clause causes no
issue because its appearances are separate copies tied by the equality chain.

## 3. Use only full-rank copies of the original source

We now implement all constraints solely as \(T(u)\in R\) with
\(T:F^d\to F^r\) surjective. No change of probability template is required.

For a pin on a full \(F^r\) block \(z\), fix a nonzero \(g\notin R\).
For each nonzero \(v\in F^r\) choose an invertible \(M_v\) taking \(v\) to
\(g\). The fixed family of conditions \(M_v z\in R\) forces \(z=0\),
and zero satisfies all of them. Such matrices exist by extending
each vector to a basis; there are only \(q^r-1\) factors.
For a nonzero linear equation \(\ell(u)=0\), take
\(z=(\ell(u),y_2,\ldots,y_r)\) with fresh auxiliary coordinates.
This map to \(F^r\) is surjective. The pin enforces \(\ell(u)=0\)
and its auxiliary coordinates are uniquely zero. A zero equation needs
no constraint.

For a possibly non-surjective condition \(B(u)\in R\), give it a fresh
\(r\)-coordinate block \(z\) pinned as above, and impose \(B(u)+z\in R\).
The latter map is surjective because of its identity block. This again
adds a unique extension. The degree and support bounds survive: every
gate has constant size, each variable copy has at most two equality links,
and padding carries only its own constant number of factors.
Every constructed \(T\) is surjective, so \(T^\top\) is injective.
Repeated maps may occur and represent independent source copies.

With (1), (4) now proves coNP hardness for exact uniformity by the complement
of 3-SAT, and the counting hardness by exact division by the fixed scalar
\(|S|\) applied to the output of the nonzero-support count. The counting
baseline is [Valiant's class](https://doi.org/10.1137/0208032): a Boolean
verifier circuit compiled by gate-truth clauses of arity at most three
has a unique internal extension for each accepting witness. This is the
ordinary \(\#\)3-SAT baseline, not a unique-satisfiability assumption. Since the construction fixes the
size of all templates in advance, it does not invoke an exponential algorithm
on a template supplied as part of the instance.

For a smallest familiar example take \(F=\mathbb F_2\), \(r=2\), and
\(\nu=(3,2,2,1)/8\) in order \(00,01,10,11\).
Its Fourier values are \((1,1/4,1/4,0)\), and \(R\) is nonadditive.
Even this single strictly positive rational source shows the decision
and counting frontiers. In contrast, any source on \(F_p\) with rational
masses has additive Fourier support, either \(\{0\}\) or \(F_p\);
Galois conjugacy over the prime field excludes an intermediate support.

## 4. Exact hardness need not imply detectable statistical deviation

On the constructed instances \(\bigcap_i\ker T_i=\{0\}\).
Indeed a vector in this common kernel is automatically a satisfying frequency.
If its activation is zero, uniqueness of the zero extension forces the
whole vector to be zero. Otherwise some gate has \(w=s e_j\ne0\).
In its conjunction (2) choose \(v_j\) nonzero in \(R\) and
all other \(v\)'s zero. The corresponding padded map, with padding zero
on the satisfying frequency, takes the value \(s v_j\ne0\), a contradiction.

For positive \(\nu\), let \(\beta=\max_{v\ne0}|\widehat\nu(v)|<1\).
Strictness follows because a nonconstant character does not have a
constant phase on the full support. Each nonzero frequency of the
constructed law then has magnitude \(\le\beta\), including those whose
values vanish. Repeating the entire source list \(h\) times raises
Fourier values to power \(h\) and preserves the support exactly.
By inversion and the triangle inequality, the resulting total variation
distance to the uniform law is at most
\((q^d-1)\beta^h/2\).
A constant depending only on \(\nu\) times \(d+L+1\) repetitions is sufficient.
This proves the promise claim without converting exact uniformity into a
positive-gap sampling question.

## Relation to prior work

The homogeneous gate (2) is the elementary linear specialization of
the relation-by-preserving-operations construction in §3 of
[Geiger, 1968](https://msp.org/pjm/1968/27-1/pjm-v27-n1-p08-s.pdf).
The fixed Boolean constraint background includes the
[Creignou–Hébrard nontrivial-solution results, Proposition 4.7](https://www.numdam.org/item/ITA_1997__31_6_499_0/).
Counting arbitrary complex-weighted Boolean constraints has its own
affine-support obstructions (see [Cai–Lu–Xia](https://arxiv.org/abs/1111.2384));
that is not the same decision or counting task as the Fourier-support size
of a fully specified linear convolution. Wider probabilistic-program
equivalence models use multiplication and conditionals as well
([Barthe–Jacomme–Kremer](https://members.loria.fr/SKremer/files/Publications/b2hd-BJK-tocl22.html)).
Contrast also [Metya–Mukherjee](https://arxiv.org/abs/2609.38243),
whose projection problems optimize distance to a desired distribution over
variable convolution factors, rather than test the given linear images.
Here the fixed-source dichotomy, unique zero extension, and full-rank
constant-occurrence compilation are the concrete claims. The companion verifier uses only finite generated algebra examples.
No global priority is asserted, no inverse inference problem is analyzed, and no
relaxed uniformity criterion inherits the exact decision hardness solely
from the theorem.
