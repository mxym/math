# Fixed-degree binary polynomial source decomposition

All spaces are finite-dimensional over \(\mathbb F_2\); logs are
base two. Fix \(d\ge2\) and \(m\ge8d\). Put
\(p=d-1\), \(r_*=\lfloor m/2\rfloor\), and
\(\delta=2^{-pm-3}\).
Let \(K_d\) be a positive integer for arity \(d\) in
Milićević's dense multilinear variety theorem (stated in §3;
an explicit admissible \(K_d\) is given in §6).
Define
\[
 R_m=K_d(dm+3),\qquad L_{d,m}=\max\{m+4,\ m+dR_m m^{d-1}\}.
 \tag{1}
\]
For fixed \(d\) this is \(O_d(m^d)\).

## 1. Statement and polarisation

Let \(f:\mathbb F_2^s\to\mathbb F_2^n\) have total degree at most \(d\)
in squarefree algebraic normal form. If \(s\ge L_{d,m}\), every
\(L_{d,m}\)-dimensional subspace \(V\) of the generating space
contains an \(m\)-dimensional subspace \(W\) satisfying one of these
conclusions, the same conclusion for every affine coset \(u+W\):

- \(g_u(w)=f(u+w)\) on \(W\) has degree at most \(d-1\).
- For every ordered linearly independent tuple
  \((a_1,\ldots,a_p)\in W^p\), the derivative
  \(\Delta_{a_1}\cdots\Delta_{a_p}g_u(U_W)\) has min-entropy at least \(r_*\).

Here \(\Delta_a f(x)=f(x+a)+f(x)\) and \(U_W\) denotes a uniform
point. If \(f\) is injective, the uniform-input distribution is
exactly the mixture over the \(W\)-cosets; each component is an
injectively sampled \(m\)-bit source. If the output min-entropy is
at least \(k\), then for \(0<\epsilon<1\) and
\(k\ge L_{d,m}+m+\log(1/\epsilon)\), one can choose \(W\) so that
removing at most an \(\epsilon\) fraction of cosets leaves only
injective \(m\)-bit restrictions. This changes the output law by at
most \(\epsilon\) in total variation. The result gives
\(m=\Omega_d(k^{1/d})\) for fixed error or for
\(\log(1/\epsilon)\le\gamma k\) with \(\gamma<1\) fixed.

For a squarefree degree-\(d\) monomial with indices \(i_1,\ldots,i_d\),
its \(d\)-fold additive derivative is the sum over permutations of
the products applying each of the \(d\) directions to one of those
coordinates once. Monomials of lower degree contribute zero.
Thus the top derivative of \(f\) is a vector-valued alternating,
symmetric \(d\)-linear map
\[
 T(a_1,\ldots,a_d)=\Delta_{a_1}\cdots\Delta_{a_d}f(x)
       :(\mathbb F_2^s)^d\longrightarrow\mathbb F_2^n ,
\]
independent of \(x\). Repetition of a direction makes it zero; so
does linear dependence of the tuple, by multilinearity.
The affine function \(\Delta_{a_1}\cdots\Delta_{a_p}g_u(w)\)
has linear part \(w\mapsto T(a_1,\ldots,a_p,w)\).
An affine image of a uniform point has min-entropy equal to its
linear rank, independent of its constant term. In fact a
linearly dependent directional tuple has identically zero derivative
over \(\mathbb F_2\). Write one direction as a sum of some of
the others; using \(I+\Delta_{a+b}=(I+\Delta_a)(I+\Delta_b)\),
expand its difference operator as the sum of nonempty products of
the corresponding previous difference operators. Each term in the
full product vanishes by \(\Delta_a^2=0\). The case of a zero
direction is immediate. Thus dependent tuples must be excluded
from a positive derivative min-entropy requirement.
In coordinates for any basis of \(W\), the degree-\(d\)
coefficients of every \(g_u\) are the values of \(T\) on the
distinct basis \(d\)-tuples. Their simultaneous vanishing is
equivalent to \(T|_{W^d}=0\).

## 2. Sparse bad tuples: keep all independent tuples

A tuple \(\mathbf a\in V^p\) is called bad if
\(\operatorname{rk}(T(\mathbf a,\cdot)|_V)<m\).
The bad probability is measured over independently uniform vectors,
not over only the linearly independent tuples. In particular all
dependent tuples are bad. In an \(N\)-dimensional binary space the
number of ordered independent \(p\)-tuples is
\(\prod_{i=0}^{p-1}(2^N-2^i)\) for \(N\ge p\), since at stage \(i\)
the span already has \(2^i\) points. All other tuples number
\(2^{Np}-\prod_{i=0}^{p-1}(2^N-2^i)\). No dependent tuple is removed
when deciding whether the bad density is at most \(\delta\).

Suppose the bad probability is at most \(\delta\).
Choose \(\phi:\mathbb F_2^m\to V\) with independently uniform basis
images. The probability of a nontrivial kernel is at most
\((2^m-1)2^{-N}<1/16\), since \(N=\dim V\ge m+4\).
Fix one ordered independent \(p\)-tuple in \(\mathbb F_2^m\)
and complete it to a basis. Its images are uniformly and
independently distributed in \(V\); thus the chance they are bad
is at most \(\delta\), including any linear dependence in the images.
Conditional on good images, the remaining \(m-p\) columns under
the contraction are independent uniform points of an image space
of dimension \(r\ge m\). The first \(p\) columns of this contraction
are zero by alternation.

If the \(m-p\) random columns have rank below \(r_*\), a set of
\(r_*-1\) indices spans all of them, padding a smaller spanning
set if necessary. Conditioning on those indices, the probability
all other columns fall in their span is at most
\(2^{-(r-r_*+1)(m-p-r_*+1)}\).
As there are at most \(2^{m-p}\) choices of the index subset, this
gives the bound \(2^{m-p-(m-r_*+1)(m-p-r_*+1)}\).
For \(m\ge8d=8(p+1)\),
\[
 (m-r_*+1)(m-p-r_*+1)\ \ge\ 3m^2/16\
 \ge\ \tfrac32(p+1)m\ \ge\ (p+2)m.
\]
The first inequality uses \(m-r_*+1\ge m/2\) and
\(m-p-r_*+1\ge3m/8\); the last uses \(p\ge1\).
There are fewer than \(2^{pm}\) independent tuple tests. Their
bad-image contribution is at most \(1/8\), and their good-image
rank-failure contribution is at most \(2^{-m-p}\). The sum of
these two bounds and \(1/16\) is less than one.
So an injective \(\phi\) meets the rank requirement in all tests.
Its image \(W\) satisfies the high-derivative conclusion, because
each ordered independent tuple in \(W\) has an independent lift
under \(\phi\). The sampled map imposes no condition on dependent
tuples of generator directions.

## 3. Dense bad tuples: find a degree drop

Suppose instead the bad probability is greater than \(\delta\).
For a fixed tuple \(\mathbf a\), precisely a \(2^{-r}\) fraction
of \(v\in V\) satisfy \(T(\mathbf a,v)=0\), where \(r\) is the
rank of the indicated linear map. For a bad tuple \(r\le m-1\).
Thus the zero set of \(T\) in \(V^d\) has density
\[
 c=\mathop{\mathbb E}_{\mathbf a\in V^p}
       2^{-\operatorname{rk}(T(\mathbf a,\cdot)|_V)}
   >\delta\, 2^{-(m-1)}=2^{-dm-2}.
 \tag{2}
\]
If only the independent bad tuples already have absolute mass
larger than \(\delta\), the same inequality follows using just them;
the proof also handles the case where the dependent tuples make a
contribution to that mass. This is a zero-set density, not the
probability that \(T\) takes an arbitrarily chosen nonzero value.

**Dependency (Milićević, Theorem 2, arXiv:2512.14529v1).**
Over a prime field, a multilinear variety in
\(G_1\times\cdots\times G_d\) of density \(c>0\) contains a multilinear
variety of codimension at most \(K_d(\log_q(1/c)+1)\), where \(q\)
is the prime field order and \(K_d\) depends on the arity alone.
In the source, this kind of codimension means the number of
homogeneous scalar multilinear equations, each on any nonempty
subset of the coordinate blocks. It is not ambient algebraic or
Krull codimension. The conclusion is actual containment, not an
approximate agreement. Appendix §6 gives a binary proof with
explicit constants using the source's argument.

Here \(G_i=V\) in every block, \(q=2\), and we apply the theorem
to the zero set in (2). This is a multilinear variety because
taking the \(n\) scalar coordinates of the vector-valued \(T\)
gives its defining collection of \(d\)-linear forms. The initial
number \(n\) of equations is irrelevant to the conclusion's bound.
Equivalently the scalar \((d+1)\)-linear pairing
\((\mathbf a,v,z)\mapsto z\cdot T(\mathbf a,v)\) has bias exactly \(c\),
since averaging over uniform \(z\) gives the indicator of \(T=0\);
we do not need an analytic-rank or partition-rank theorem.

By (2), there are at most \(R_m\) new scalar equations
\(B_\ell(v_i:i\in I_\ell)=0\), \(I_\ell\subseteq[d]\) nonempty,
whose common zero set is **contained in** the original \(T=0\)
set. Build an ordered independent list \(w_1,\ldots,w_m\) such
that for each \(B_\ell\), every injection from its indexed positions
\(I_\ell\) to the chosen list gives value zero. Start with the
empty list. When adjoining \(w_{j+1}\), check only assignments
using the new vector. For a form with \(a=|I_\ell|\), choose its
new position in \(a\) ways and assign the other \(a-1\) positions
to distinct old vectors in \((j)_{a-1}\) ways, with zero choices
when \(j<a-1\). Each resulting equation on \(w_{j+1}\) is a
homogeneous linear equation, since it is in only one slot.
The number of equations per step is at most
\(dR_m m^{d-1}\) (also covers \(a=1,j=0\)).
The common kernel in \(V\) therefore has dimension at least \(m\)
by (1); since the old span has dimension \(j<m\), select a
new vector outside it. This proves the desired injection property.
Take \(W\) to be the span.

Every \(d\)-tuple of distinct basis vectors of \(W\), in any
order, satisfies all the equations \(B_\ell=0\).
It follows from containment that \(T\) vanishes on these tuples.
It also vanishes on tuples with repetitions by alternation. This
last step uses alternation of \(T\), not of the \(B_\ell\), which
need not vanish on repeated arguments. Thus \(T|_{W^d}=0\) by
multilinearity. This proves the degree-drop branch. In both branches
the choice uses only \(T\); no lower-degree coefficient or coset
representative enters the choice.

## 4. Collision isolation for general min-entropy

Suppose \(f\) is not known to be injective and \(H_\infty(f(U))\ge k\).
Every fiber has at most \(2^{s-k}\) points and \(s\ge k\).
Let \(L=L_{d,m}\) and take \(V\) uniformly among the \(L\)-dimensional
linear subspaces. A given nonzero difference lies in \(V\) with
probability \((2^L-1)/(2^s-1)\), by symmetry and size. Hence for a
fixed \(x\) the probability its \(V\)-coset contains a different
point with the same value of \(f\) is at most
\[
 (2^{s-k}-1)\frac{2^L-1}{2^s-1}\le 2^{L-k}.
\]
The last inequality follows from \(L\le s\). Average over \(x\)
to find one \(V\) with at most a \(2^{L-k}\) fraction of those
bad points. Use §2 or §3 to choose \(W\subseteq V\). Each
noninjective \(W\)-coset contains at least one such bad point.
The \(W\)-cosets partition the full generating space and each
has \(2^m\) elements, so their fraction that are noninjective
is at most \(2^{L+m-k}\le\epsilon\). Conditioning the uniform
input on the remaining cosets discards exactly that amount of
mass in total variation. Applying \(f\) cannot increase this
distance. The retained components, uniform on distinct \(2^m\)
outputs within each coset, have exact min-entropy \(m\).
Different components may share outputs. If \(f\) was injective
initially, no cosets are deleted, with no additional entropy cost.

## 5. The scale is sharp for these affine restrictions

Let \(r=\lfloor m/2\rfloor-1\), \(M=\binom md\), and
\(s_0=\lfloor rM/(2m)\rfloor\). For \(m\ge8d\), \(r\ge m/3\) and
\(M\ge m(m-1)/2\), since \(2\le d\le m/2\), so \(s_0\ge m\).
For each fixed \(d\), \(s_0=\Theta_d(m^d)\).
Choose \(r\) Boolean homogeneous degree-\(d\) forms \(g_i\) on
\(\mathbb F_2^{s_0}\) with all squarefree top-degree coefficients
uniformly and independently chosen, allowing a zero form.
Let \(f(x)=(x,g_1(x),\ldots,g_r(x))\).
Then \(f\) is injective with min-entropy \(s_0\).
The linear part of any \(p\)-fold derivative of any restriction
has rank at most \(r\), since the identity coordinates have
zero \(d\)-fold derivative. Thus the high-derivative alternative
is impossible for every \(m\)-dimensional direction space.

Each top polarisation is uniform among alternating \(d\)-forms;
the coefficient representation and the values on strictly
increasing \(d\)-tuples of any basis give the same vector
space of coefficients. For a fixed \(m\)-space \(W\), restriction
of alternating forms is surjective (extend a basis of \(W\) and
extend its coefficients by zeros). Hence all \(r\) polarisations
vanish on \(W^d\) with probability \(2^{-rM}\).
The number of \(W\)'s is at most \(2^{m s_0}\), by counting ordered
generating lists. The probability any \(W\) works is therefore at
most \(2^{m s_0-rM}\le2^{-rM/2}<1\).
Some such \(f\) admits no \(m\)-dimensional restriction of either
type, at any translate. This proves that the threshold
\(\Theta_d(m^d)\) is sharp up to a constant depending on \(d\)
for the stated common-affine-restriction theorem with derivative
threshold \(\lfloor m/2\rfloor\); it also rules out a mixture of
those affine restrictions in this example. It does not rule out
structures described by arbitrary different sampling maps.

## 6. Binary dense-variety lemma with a dimension-only constant

For completeness this appendix records the combinatorial proof of
the binary case of Milićević's theorem, with coarse explicit
constants and all forms grouped by their coordinate sets when
compressing equations. This appendix is an exposition of the
dependency, not a claim to have originated the dense-variety theorem.

A homogeneous multilinear variety in
\(G_1\times\cdots\times G_\ell\) is the common zero set of a
finite collection of homogeneous scalar multilinear forms, each
on a specified nonempty subset of the blocks. Fixing all blocks
but one gives either an empty set or a linear subspace in that
block. Indeed, the forms not using the block must vanish, and
every other form is homogeneous linear in the remaining variable.
Slices along a fixed coordinate of such a variety are again
varieties on the remaining blocks, provided the slice is nonempty;
constant zero equations may be dropped.

### 6.1 Sparse deletion and coordinate sums

If \(P\) is defined by at most \(r\) forms in \(k\) blocks
and \(D\subseteq P\) has density at most \(2^{-2k-kr}\)
in the whole product, then every point of \(P\) can be obtained
from leaves in \(P\setminus D\) by a binary tree that sums within
one block at each level, with equal other blocks, and has \(2^k\)
leaves. The root sums in coordinate \(k\), its children in
coordinate \(k-1\), and so on.
For \(k=1\), \(|P|\ge2^{-r}|G_1|\) and at most a quarter of
\(P\) is deleted. For any \(x\in P\), the translates of two
copies of \(P\setminus D\) inside \(P\) intersect, proving the
claim at \(k=1\).
For \(k>1\), fix \(x\in P\).
Among values of the last block, the fraction whose \(D\)-slice
has density greater than \(2^{-2(k-1)-(k-1)r}\) inside the
whole product of the first blocks is at most \(2^{-2-r}\) by
averaging. At the fixed first \(k-1\) coordinates of \(x\),
the last-coordinate fiber is a nonempty subspace of density at
least \(2^{-r}\). Removing the exceptional last coordinates loses
at most a quarter of this subspace. One can choose \(y_k\) so
that both \(y_k\) and \(y_k+x_k\) are in the fiber and are
not exceptional. Their first-coordinate slices each admit the
induction construction at \(x_1,\ldots,x_{k-1}\).
Joining the two trees gives the claim. The auxiliary choices in
different branches need not be equal.

### 6.2 Extracting a bounded number of equations

Let \(\ell=k+1\) and suppose the dense-variety result holds for
\(k\) blocks with constant \(K=K_k\), starting at \(K_1=1\)
by the ordinary linear subspace case.
Take a variety \(Z\) in \(\ell\) blocks of density \(c>0\), and
set \(u=\log(1/c)\). First we find, in each deleted-coordinate
product, a low-codimension variety on which the fibers of \(Z\)
are all dense. For the last coordinate, set
\(\beta=2^{-2k-1-2kK}c^{kK+1}\).
For a fixed value \(y\) of the last block, let \(U_y\) be the
corresponding slice of \(Z\) in the first blocks, and let
\(D_y\subseteq U_y\) consist of points whose last-coordinate fiber
in \(Z\) has density at most \(\beta\).
Writing sizes as fractions of the first-block product and
averaging over \(y\) gives \(\mathbb E|U_y|_{\rm rel}=c\)
and \(\mathbb E|D_y|_{\rm rel}\le\beta\).
Therefore some \(y\) satisfies
\[
 |U_y|_{\rm rel}-\frac{c}{2\beta}|D_y|_{\rm rel}\ \ge c/2.
\]
This slice has density at least \(c/2\), and the deleted set in
it has ambient density at most \(2\beta/c\).
By induction \(U_y\) contains a variety \(P\) defined by
at most \(r\le K(u+2)\) forms. Since
\(2\beta/c\le2^{-2k-kr}\), §6.1 applies to
\(P\) with deleted set \(P\cap D_y\).
For every point in \(P\), intersect the last-coordinate fibers
of \(Z\) at its \(2^k\) leaves. Each is a subspace of density
greater than \(\beta\); their intersection has density at least
\(\beta^{2^k}\). Every point of this intersection is also in
the fiber of the root, because fixed-coordinate fibers of \(Z\)
are closed under the sums in the tree. This constructs the
desired \(P\) for the last coordinate. Apply the same argument
after permuting blocks for each coordinate \(i\), giving a
variety \(P_i\) on the product omitting \(i\).

For each \(i\), let \(U^{(i)}\) consist of the equations defining
the \(P_j\)'s that do not involve coordinate \(i\). Regard them
as equations on the product omitting \(i\). They include the
equations for \(P_i\) and number at most \(\ell K(u+2)\).
Let \(U\) be their intersection after lifting each system to the
full product (at most \(\ell^2 K(u+2)\) equations).
Whenever the coordinates other than \(i\) satisfy \(U^{(i)}\),
the \(i\)-fiber of \(Z\cap U\) has density at least
\[
 b=\beta^{2^k} 2^{-k(k+1)K(u+2)}.
\]
To see this, the \(Z\)-fiber has density at least
\(\beta^{2^k}\) by \(P_i\). All equations in the full system
that omit \(i\) have already been imposed; the remaining
equations give at most \(k(k+1)K(u+2)\) additional homogeneous
linear constraints in coordinate \(i\), since the \(U^{(i)}\)
system uses none. This proves the claim.

To cover \(Z\) by an outer variety \(A\) with small excess,
first group its defining forms by their exact nonempty support
\(I\subseteq[\ell]\), making a vector of forms \(F_I\) for each
group. For each group compose \(F_I\) with \(t\) independently
uniform linear functionals, and set \(A\) to their common zeros.
The new equations remain multilinear on their respective
coordinate sets. For a point outside \(Z\), some \(F_I\ne0\);
the chance that this point lies in \(A\) is at most \(2^{-t}\).
Some choice therefore gives \(|A\setminus Z|_{\rm rel}\le2^{-t}\).
The variety \(A\) uses at most \((2^\ell-1)t\) equations.

If \(2^{-t}<b^\ell\), then \(A\cap U=Z\cap U\).
In fact, given a point in their difference, fix all but
coordinate \(i\). The \(Z\cap U\) fiber has density at least
\(b\), because the fixed coordinates satisfy \(U^{(i)}\).
It lies in the \(A\cap U\) fiber, and the inclusion is
strict because the given point is in the difference.
Both fibers are linear subspaces. Their difference has
cardinality at least that of the smaller subspace, so at least
\(b |G_i|\) replacements of coordinate \(i\) keep the point in
the difference. Repeating for \(i=1,\ldots,\ell\) yields a
fraction at least \(b^\ell\) of distinct final points in the
difference (the previously varied coordinates distinguish
branches). This contradicts the excess bound.

For explicit constants, put
\[
 C_k=2^k(2k+1+2kK_k)+2k(k+1)K_k,\qquad
 K_{k+1}=2(k+1)^2 K_k+(2^{k+1}-1)((k+1)C_k+2).
\]
Indeed expanding \(\log(1/b)\) gives
\[
 2^k[(2k+1+2kK_k)+(kK_k+1)u]+k(k+1)K_k(u+2)
 \le C_k(u+1)
\]
because the coefficient of \(u\) is at most the constant
term \(C_k\). Take \(t=\lceil(k+1)C_k(u+1)\rceil+1\);
then \(2^{-t}<b^{k+1}\), and
\(t\le((k+1)C_k+2)(u+1)\).
The subvariety \(A\cap U\subseteq Z\) uses at most
\((k+1)^2K_k(u+2)+(2^{k+1}-1)t\le K_{k+1}(u+1)\)
forms. This proves the dependency by induction, in the actual
binary setting used in §3.
