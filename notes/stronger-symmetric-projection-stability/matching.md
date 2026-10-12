# A sharp square-root matching theorem for bounded laws

This note strengthens the matching lemma in the completed upper-end stability
supplement. It is separate research; it does not alter that supplement.

## Statement and conventions

Let \(d\ge3\), let \(\nu\) be a Borel probability measure supported in the
Euclidean unit ball, and let \(X_1,\ldots,X_{d+1}\) be independent samples.
Write
\[
 A=\mathbb E|\det(X_1,\ldots,X_d)|.
\]
For a tuple of \(d+1\) vectors, let \(\phi\) denote the fourth-largest of
the \(d+1\) absolute \(d\)-dimensional cofactors. Suppose
\[
 A\ge a>0,\qquad \mathbb E\phi\le\varepsilon,
 \qquad q=4(d+1)\varepsilon/a.
\]
Hadamard's inequality implies \(a\le1\).

**Theorem 1 (square-root matching).** There are a basis matrix \(U\) whose
columns lie in the support of \(\nu\), and a partition of its coordinates
into singletons and pairs, such that the union \(\mathcal W\) of the
resulting coordinate blocks satisfies
\[
 |\det U|\ge a/2,\qquad \|U\|\le\sqrt d,
 \qquad \|U^{-1}\|\le2\sqrt d/a,
\]
and, if \(0\le q\le1\),
\[
 \mathbb E\operatorname{dist}(U^{-1}X,\mathcal W)
 \le5d^2a^{-2}\sqrt q.                                      \tag{1}
\]
The conclusion includes nonatomic laws and singular sampled tuples.
The power \(1/2\) cannot be increased under these hypotheses, even for even
finite laws and fixed dimension.

## Proof of Theorem 1

For a candidate sampled basis \(b=(b_1,\ldots,b_d)\), put
\[
 Q(b)=\int\phi(b_1,\ldots,b_d,x)\,d\nu(x)
 +\sum_{j=1}^d\iint
 \phi(b_1,\ldots,\widehat b_j,\ldots,b_d,x,y)
 \,d\nu(x)\,d\nu(y).
\]
Tonelli's theorem gives \(\mathbb E_bQ(b)\le(d+1)\varepsilon\).
Since \(D(b)=|\det b|\le1\) and its expectation is at least \(a\),
the event \(D(b)\ge a/2\) has probability at least \(a/2\). If
\(\varepsilon>0\), Markov's inequality gives
\(\mathbb P(Q(b)>q)\le a/4\). These two events therefore intersect.
If \(\varepsilon=0\), \(Q(b)=0\) almost everywhere and the determinant-good
event again intersects it. Fix such a basis \(U=(b_i)\), and write
\[
 D=|\det U|\ge a/2,\qquad R=D^{-1}.
\]
Each inverse row has length at most \(D^{-1}\), by its cofactor-wedge
formula and the unit-length bound on the other columns. Consequently
\(\|U^{-1}\|\le\sqrt d/D\), \(\|U\|\le\sqrt d\), and the coordinates
\(\alpha=U^{-1}X\) obey \(\max_i|\alpha_i|\le R\).

Let \(s_3(\alpha)\) be the third-largest coordinate magnitude. The
absolute cofactors of \((b_1,\ldots,b_d,X)\) are \(D\) times
\((1,|\alpha_1|,\ldots,|\alpha_d|)\). If \(s_3\le1\), the fourth
largest is at least \(Ds_3\); otherwise it is at least \(D\), and
\(s_3\le D^{-1}\). Thus
\[
 \mathbb Es_3\le Q_0/D^2\le q/D^2,                           \tag{2}
\]
where \(Q_0\) is the one-sample term of \(Q(U)\).

For every \(\alpha\), retain its two largest coordinates, breaking ties
by index, and set all others to zero. Denote the resulting vector by
\(\widetilde\alpha\). This is a Borel map, it does not enlarge the
coordinate bounds, and
\[
 \|\alpha-\widetilde\alpha\|_\infty\le s_3(\alpha),
 \qquad |\alpha-\widetilde\alpha|\le\sqrt d\,s_3(\alpha).    \tag{3}
\]

We first control the two-sample sections after this truncation. For
independent coordinate vectors \(\alpha,\beta\), the absolute cofactors
of the tuple omitting \(b_j\) and appending \(U\alpha,U\beta\) are the
absolute values of
\[
 D\alpha_j,\quad D\beta_j,\quad
 D(\alpha_i\beta_j-\alpha_j\beta_i)\quad(i\ne j),             \tag{4}
\]
up to signs and reordering. This is the polynomial determinant identity
obtained by applying \(U^{-1}\) to every column.

Replacing both vectors by their truncations changes either linear entry
by at most \(D(s_3(\alpha)+s_3(\beta))\). For every bilinear entry,
telescoping the two products and using all coordinate bounds \(R=D^{-1}\)
gives a change at most
\[
 2DR\bigl(s_3(\alpha)+s_3(\beta)\bigr)
 =2\bigl(s_3(\alpha)+s_3(\beta)\bigr).
\]
Taking absolute values and the fourth-largest entry are both
1-Lipschitz for the maximum norm on these finite lists. Therefore the
truncated section expectation \(\widetilde Q_j\) satisfies
\[
 \widetilde Q_j\le Q_j+4\mathbb Es_3
 \le q+4q/D^2=:\widetilde q.                                \tag{5}
\]
No regularity or atom assumption is used here.

For each unordered pair \(ij\), let \(E_{ij}\) be the Borel event that
\(i,j\) are the selected two largest coordinates. Define its *weighted*
mass by
\[
 m_{ij}=\mathbb E\left[
   \min(|\alpha_i|,|\alpha_j|)\,\mathbf1_{E_{ij}}\right].     \tag{6}
\]
Zero second coordinates contribute zero, so arbitrary tie choices there
are harmless. Consider distinct \(i,j,k\). On \(E_{ij}\times E_{jk}\),
the two truncated vectors are exactly supported on \(ij\) and \(jk\).
Put \(r_\alpha=\min(|\alpha_i|,|\alpha_j|)\) and
\(r_\beta=\min(|\beta_j|,|\beta_k|)\). Four entries in (4) have
absolute values
\[
 D|\alpha_j|,\quad D|\beta_j|,\quad
 D|\alpha_i\beta_j|,\quad D|\alpha_j\beta_k|.
\]
Since \(r_\alpha,r_\beta\le R\) and \(D\le1\), each of these is at
least \(D^2r_\alpha r_\beta\). Integrating the fourth cofactor over this
product event gives
\[
 D^2m_{ij}m_{jk}\le\widetilde Q_j\le\widetilde q.           \tag{7}
\]
In particular, edges of weight strictly greater than
\(w=\sqrt{\widetilde q}/D\) cannot share a vertex. They form a matching.
Use those edges as pair blocks and every remaining coordinate as a
singleton block. Every discarded edge has weight at most \(w\).

If the selected top pair of \(\alpha\) is a matching edge, its truncated
vector lies in its plane block. Otherwise, its distance to the block
containing its largest coordinate is at most the smaller retained
coordinate. By (3) and the triangle inequality,
\[
 \operatorname{dist}(\alpha,\mathcal W)
 \le\sqrt d\,s_3(\alpha)
  +\min(|\alpha_i|,|\alpha_j|)
       \mathbf1_{\{ij\text{ discarded}\}}.
\]
Hence (2), (5), and (6) give
\[
 \mathbb E\operatorname{dist}(\alpha,\mathcal W)
 \le\frac{\sqrt d\,q}{D^2}
   +\binom d2\frac{\sqrt{q+4q/D^2}}D
 \le\frac{\sqrt d+\sqrt5\binom d2}{D^2}\sqrt q.             \tag{8}
\]
The last step uses \(q\le1\) and \(D\le1\). Finally, \(D\ge a/2\),
\(\sqrt5\le5/2\), and \(\sqrt d\le d\) imply
\[
 4\left(\sqrt d+\sqrt5\binom d2\right)
 \le4d+5d(d-1)\le5d^2,
\]
which proves (1). At \(q=0\), (7) says all positive-weight edges form a
matching, (2) gives exact two-sparsity almost everywhere, and (8) has
zero right-hand side. This proves the zero case directly.

## A sharp obstruction under the intermediate hypotheses

**Lemma 2 (cofactor vanishing for a block union).** Let
\(\mathbb R^d=\bigoplus_jW_j\), where \(\dim W_j\in\{1,2\}\).
For every \(d+1\) vectors in \(\bigcup_jW_j\), the fourth absolute
cofactor is zero.

**Proof.** If the tuple has rank below \(d\), all cofactors vanish.
Otherwise assign each vector to one block containing it, assigning a
zero vector arbitrarily. If block \(j\) receives \(n_j\) vectors, full
rank requires \(n_j\ge\dim W_j\) for every block. As their sum is
\(d+1\), exactly one block receives one extra vector and the others
receive precisely their dimensions. The unique relation on the tuple
is supported on that oversampled block, which receives at most three
vectors. Cofactors are its relation coefficients, so at most three
cofactors are nonzero. \(\square\)

**Lemma 3 (a quantitative distance witness).** If \(z_1,\ldots,z_{d+1}\)
are in the unit ball, then, for every block union \(\mathcal V\) in
Lemma 2,
\[
 \sum_{i=1}^{d+1}\operatorname{dist}(z_i,\mathcal V)
 \ge\phi(z_1,\ldots,z_{d+1}).                               \tag{9}
\]

**Proof.** Project each \(z_i\) orthogonally onto a closest block and
call the resulting vector \(y_i\). Then \(|y_i|\le1\) and
\(|z_i-y_i|=\operatorname{dist}(z_i,\mathcal V)\). For each cofactor,
multilinear telescoping and Hadamard's inequality bound its change by
the sum of these distances over its \(d\) columns, hence by the full
sum. The fourth absolute cofactor is 1-Lipschitz in the list of
cofactors, and it vanishes for the \(y_i\) by Lemma 2. \(\square\)

Now put
\[
 v_{12}=(e_1+e_2)/\sqrt2,\qquad v_{23}=(e_2+e_3)/\sqrt2,
 \qquad 0<p\le1/(d+2),\qquad w=(1-2p)/d.
\]
Let \(\nu_p\) give total mass \(w\) to each antipodal pair
\(\{\pm e_i\}\), and mass \(p\) to each of
\(\{\pm v_{12}\},\{\pm v_{23}\}\), distributing each antipodal mass
equally. This is an even law in the unit ball, and \(w\ge p\).
Sampling the \(d\) axis directions in any order gives
\[
 A(\nu_p)\ge d!w^d\ge a_d:=d!/(d+2)^d>0.                 \tag{10}
\]
Any repeated direction gives a relation supported on its two repeated
columns. If the tuple has rank below \(d\), all cofactors vanish; otherwise
its unique relation is that repeated-direction relation, so at most two
cofactors are nonzero. Thus such a tuple has fourth cofactor zero.
Among distinct-direction \(d+1\)-tuples,
the only set with positive fourth cofactor is
\[
 (e_1,e_3,e_4,\ldots,e_d,v_{12},v_{23}).                     \tag{11}
\]
Indeed, omitting an outside axis gives rank below \(d\); omitting one of
the two new directions leaves a three-term circuit; and omitting \(e_1\)
or \(e_3\) likewise leaves the three-term circuit on \(e_2,e_3,v_{23}\)
or \(e_1,e_2,v_{12}\). In (11), the four nonzero absolute cofactors are
\(1/2,1/2,1/\sqrt2,1/\sqrt2\), and all other cofactors are zero. Its fourth
cofactor is \(1/2\). Therefore, exactly,
\[
 \varepsilon_p:=\mathbb E_{\nu_p^{d+1}}\phi
 =\frac{(d+1)!}{2}\,w^{d-1}p^2.                            \tag{12}
\]
Signs and permutations do not change this value.

Applying Lemma 3 to (11), and using that every direction has mass at
least \(p\), gives for *every* direct sum of line and plane blocks
\[
 \mathbb E_{\nu_p}\operatorname{dist}(X,\mathcal V)
 \ge p/2.                                                  \tag{13}
\]
This lower bound is independent of the choice, angles, or uniqueness of
the decomposition. For any basis \(U\) with unit-length columns, let
\(\mathcal V=U\mathcal W\). Since \(\|U\|\le\sqrt d\),
\[
 \mathbb E\operatorname{dist}(U^{-1}X,\mathcal W)
 \ge\frac1{\sqrt d}\mathbb E\operatorname{dist}(X,\mathcal V)
 \ge\frac p{2\sqrt d}.                                    \tag{14}
\]
As \(p\downarrow0\), (12) is a positive constant depending on \(d\)
times \(p^2+O_d(p^3)\), while (10) is uniformly positive. Thus an
estimate with power \(\gamma>1/2\) and constants depending only on \(a,d\)
is impossible under the hypotheses of Theorem 1.

The obstruction is about arbitrary bounded even laws. No claim is made
that these particular laws are cone laws of centrally symmetric bodies.
The completed cone-specific half-mass argument must still be retained
when applying the matching theorem to convex bodies.

## Consequence for the existing proof chain

Keeping the completed estimate
\(\mathbb E\phi\le F_d\delta^{2/3}\), its determinant lower bound
\(a=a_d^{\mathrm{John}}\), and its geometry lemma unchanged, (1) gives
\[
 s\le5d^2(a_d^{\mathrm{John}})^{-2}
       \sqrt{4(d+1)F_d/a_d^{\mathrm{John}}}\;\delta^{1/3}.
\]
The same cap-to-containment step therefore yields a proved upper-end
power \(1/(3d)\), with explicit constants obtained by this substitution.
The root assembly is responsible for stating and simplifying the final
global constant. The intermediate square-root matching step is sharp,
so improving it further requires additional cone-law information or a
different geometric route.

## Verification scope

`check_matching_improvement.py` checks the cofactor formula, the truncation
perturbation inequality, the adjacent-edge lower bound, and the exact
finite-law obstruction formula using rational arithmetic. For the last
check it uses the rational variant \(v_{ij}=(e_i+e_j)/2\), whose fourth
cofactor is \(1/4\) and whose expectation is
\((d+1)!w^{d-1}p^2/4\), avoiding any floating-point square roots. These finite
checks support the polynomial identities; the measure-theoretic
selection and integral proof above do not depend on enumeration.
