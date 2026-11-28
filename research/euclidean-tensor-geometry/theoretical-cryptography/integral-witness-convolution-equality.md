# Integral witness compression for known convolution law equality

**Scope.** Two fully specified forward laws with explicit local probability
tables and linear maps. The question is exact joint distributional equality,
not fitting unknown distributions or evaluating an original point probability.
There is no input from an implementation.

**Theorem.** Let \(F=\mathbb F_q\) have characteristic \(p\). For each of two laws,
the input is a deterministic shift and a sum of independent linear images
\(A_i X_i\) in \(F^d\), where each local \(X_i\) is given by a complete rational
probability table on its coordinate space \(F^{r_i}\).
Assume that the Fourier support of each local table is an additive subgroup.
This promise is itself checkable in polynomial bit time.
Then exact equality of the two joint laws has a deterministic bit-polynomial
algorithm, even when \(q\) varies in its standard explicit finite-field
representation. It checks the equal-support case by exact Fourier comparisons
at only
\[
                          O(S(1+\log m))
\]
actual frequencies, where \(m\) is the total number of local factors (including
up to one relative shift factor) and \(S\) is their total state count,
as defined below. The chosen frequencies depend only on the restricted local
maps and their state spaces, not on the nonzero Fourier values. Signs and all
root-of-unity phases are retained.

The reusable mechanism is an integer version of reachable-span compression:
one keeps a small set of real input prefixes generating the **integral**
lattice of their state-incidence patterns. It applies to any labels in any
abelian group, so it requires neither field logarithms nor approximate
comparison of phases.

## 1. A group-valued witness lemma

Consider \(m\) deterministic devices which read the same finite sequence of
input positions. Device \(i\) has an explicitly listed state space \(H_i\);
put \(S=\sum_i|H_i|\). Initial states and transition tables are fixed, with
an explicitly listed finite alphabet at each position. At the end, state
\(h\in H_i\) has a label \(g_{i,h}\) in an arbitrary abelian group \(G\).
We want to know if
\[
                             \prod_i g_{i,h_i(w)}=1               \tag{1}
\]
for every word \(w\). Assume only that one can check (1) at a supplied word,
or equivalently check a product of \(m\) labels. The cost of this check is
separate from the witness construction.

Encode a tuple of states as a vector in \(\mathbb Z^S\) with exactly one
entry equal to one in each block and other entries zero. Each input letter
at each position acts by a block diagonal integer matrix on the row pattern.
For a deterministic transition, a row basis vector in its block is sent
to the row basis vector of the destination, including when the map is not
injective. Let \(\mathcal V_j\) be the set of patterns reached by words of
length \(j\), and \(\mathcal L_j=\operatorname{span}_{\mathbb Z}\mathcal V_j\).
If \(P_{j,a}\) acts at the next position, then
\[
                      \mathcal L_{j+1}=\sum_a\mathcal L_j P_{j,a}. \tag{2}
\]
Consequently it is enough to propagate actual words representing integer
lattice generators, rather than all their possible continuations.

The following compression applies at each step. From the finite candidate
list choose a rationally independent spanning subset of rank \(b\), and
let \(L_0\) be its integer span. In its real span, the saturated lattice
\(L_{\rm sat}=\operatorname{span}_{\mathbb R}L_0\cap\mathbb Z^S\)
has covolume at least one (the Gram determinant of an integral basis is a
positive integer). The Gram determinant bound on the \(b\) initial patterns,
each of norm \(\sqrt m\), gives
\[
                           [L_{\rm sat}:L_0]\le m^{b/2}.
\]
Then scan the remaining candidate patterns. Keep a word exactly when its
pattern is not in the current integer lattice and adjoin its pattern.
The rank and saturation remain fixed. Every actual enlargement divides
the index by an integer at least two, so at most \((b/2)\log_2 m\)
additional patterns are needed. Integer lattice membership is exact
polynomial-time by integer normal forms (transposing the row list if
required). This leaves at most \(b(1+\tfrac12\log_2 m)\) words; in particular
the induction (2) uses polynomially many candidates at every position.
For \(m=0\) the product is identically one and no words are needed.

Finally, \(e\mapsto\prod_{i,h}g_{i,h}^{e_{i,h}}\) is a homomorphism out of
\(\mathbb Z^S\). It is trivial on the entire final lattice exactly when
it is trivial on the retained patterns. Hence (1) holds everywhere iff it
holds at the selected actual words. We never evaluate that formal product
on an arbitrary integer generator; there is only one actual label per
block on a witness. This distinction avoids comparisons involving large
binary exponents.

**Large cyclic alphabet variant.** At one position suppose the available
transition matrices are \(P^a\) for \(0\le a<N\), with \(P\) a specified
one-step deterministic update and \(N\) given in binary. The span in (2)
requires only \(a<\min(N,S)\). For \(N>S\), Cayley–Hamilton over the
integers writes \(P^S\), and inductively every higher power, in the integer
span of the lower powers. All retained candidate words are still actual
permitted words. In particular, a shared product of binary-large cyclic
coordinate ranges acting by explicit state translations requires no
iteration out to the coordinate order.

## 2. Applying the witnesses to characteristic values

The trace pairing identifies the frequency space with \(F^d\);
for the linear image \(A_i X_i\) it substitutes \(A_i^\top y\) into the local
characteristic value. Compute each local Fourier support exactly: grouping
the rational mass by exponent of \(\zeta_p\) gives a vector of \(p\)
coefficients, whose sum at \(\zeta_p\) is zero precisely when all
coefficients agree. With the explicit local table, checking additivity
and finding an \(\mathbb F_p\)-basis of the support costs polynomial bit
time. If both laws are made only of dimension-zero variables, simply
compare their shifts; otherwise the prime \(p\) is at most the number of
entries in some nontrivial local table, so these operations are polynomial
even for nonconstant \(p\).

For each law, independence gives Fourier support
\(\bigcap_i (A_i^\top)^{-1}(\operatorname{supp}\widehat X_i)\).
The deterministic shift does not affect this set. It is an
\(\mathbb F_p\)-linear subspace, computable by elimination.
If the two supports differ, the laws differ. Otherwise write the common
support as \(W\), choose an \(\mathbb F_p\)-basis \(b_1,\ldots,b_\ell\), and
express \(y=\sum_j a_j b_j\) with the input letters \(a_j\in\mathbb F_p\).
For each local factor keep its state in \(F^{r_i}\), the current value
of \(A_i^\top y\) after the read prefix. One letter is a translation
of its state. The final label is the corresponding local characteristic
value, inverted for factors of the second law. An individual table can
have zeros, but every state ever reached is the image of a vector in \(W\)
(the prefix is extended by zeros), so the characteristic value there is
nonzero. Labels on unreachable states can harmlessly be set to one.

Combine the two deterministic shifts as a single additional factor,
whose state in \(\mathbb F_p\) computes the trace pairing with their
difference, and whose nonzero labels are the corresponding roots
of unity. It can be omitted if the shifts agree. Now \(S\) is the sum of
the local table sizes including this possible \(p\)-state factor.
Apply §1 in \(G=\mathbb Q(\zeta_p)^\times\). On every actual word the product
of the labels is just the ratio of the two characteristic values at \(y\);
checking the witnesses proves equality on \(W\). Off \(W\) both values
are zero, so Fourier inversion yields full joint equality.

The arithmetic at one witness is plainly bounded: clear the rational
denominators of the local mass sums, multiply the factor polynomials
of each side in \(\mathbb Z[z]/(z^p-1)\), include the shift as a monomial,
and cross multiply the denominators. These are products of only as
many factors as actually supplied. The denominators' bit lengths add;
the coefficient bit lengths are bounded by the sum of logarithms of
the factor coefficient \(\ell_1\) norms, up to the same denominator cost.
The two products agree at \(\zeta_p\) exactly when their degree-\(<p\)
difference polynomial has all coefficients equal. There is no
integer factoring or separation bound for algebraic logs in this step.

## 3. Why the integral requirement matters

For three binary state blocks, consider the four patterns whose bit
tuples are \(000,110,101,011\). Their patterns already span all eight
patterns over the rationals: in coordinates \((1,x_1,x_2,x_3)\)
the four columns have determinant of magnitude two. The corresponding
integer span, however, excludes the odd-parity patterns. Give each state
\(x_i\) the label \((-1)^{x_i}\). All four candidate basis words pass (1),
but some actual words fail. Replacing the integral lattice by only an
ordinary vector-space rank test would lose this genuine phase.
The witness lemma avoids it because it tests membership in the
integer span, not membership in its saturation.

The result is distinct from two previous boundaries. [Progression-law
identity](https://github.com/mxym/math/blob/713cbb44cd43d1fe8c302d8e8791d5968de6113a/research/euclidean-tensor-geometry/theoretical-cryptography/vector-progression-law-identity.md)
handles compactly represented cyclic factors over binary-large primes
without explicit tables. The present theorem instead permits general
multivariate explicit tables with additive Fourier support, including
non-real phases, but it does not exploit that compact input format.
The [nonadditive-support dichotomy](https://github.com/mxym/math/blob/e50536205d18533e0fca4aa9aed6af90613112f1/research/euclidean-tensor-geometry/theoretical-cryptography/fixed-source-convolution-uniformity-dichotomy.md)
shows why merely comparing the nonzero values is insufficient without
a structural hypothesis on the support: deciding the support itself
can be hard, even with full-rank sparse maps. No original point mass
is computed by the witness method.

## Relevant precedents

The use of reachable spans is classical in equivalence of weighted
automata, for example
[Tzeng's probabilistic automata equivalence](https://doi.org/10.1137/0221017).
The finite binary algorithm for the required integer normal forms is
classical as well ([Kannan–Bachem](https://doi.org/10.1137/0208040)).
The concrete additions here are a size bound for **actual-word integer
generators**, the cycle-range variant and the phase-preserving
application to specified convolution laws. No global priority for
reachable-span or finite-state equivalence is claimed. The companion
verifier compares with exact finite enumerations on artificial instances.
