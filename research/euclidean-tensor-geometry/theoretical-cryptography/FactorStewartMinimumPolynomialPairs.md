# Classification at the first polynomial square-root scale for cubes and fifth powers

**Theorem.** Let \(A,B\) be monic complex polynomials of degrees \(10,6\), respectively. Suppose \(A^3-B^5\) is nonzero of degree at most \(15\). Up to a common complex affine change of variable, renormalizing each polynomial to be monic, there are exactly **11** pairs. Three classes admit real coefficients, and precisely one admits rational coefficients. In that rational class, after centering \(B\) by a rational translation, necessarily
\[
 B=x^6+\beta x,\qquad A=x^{10}+\frac53\beta x^5+\frac59\beta^2,
 \qquad \beta\in\mathbb Q^\times .
\]
The three Galois orbits have sizes \(1,2,8\). Explicit fields of definition are respectively \(\mathbb Q\), \(\mathbb Q(\sqrt{-3})\), and the degree-eight field of the invariant below.

**Consequence for Stewart's question.** For fixed rational polynomials whose cube and fifth power have common degree 30, no infinite sequence of **distinct positive integer power pairs** from evaluation at rational parameters can lie in intervals of length \(\alpha\sqrt N\) with any fixed \(0<\alpha<1/\sqrt5\) and \(N\to\infty\). This upgrades the [older obstruction for the sparse binomial ansatz](FactorStewartConstructionObstructions.md) to the entire first possible polynomial degree. It does not rule out higher-degree pairs, nonpolynomial constructions, or individual close integer pairs. In particular, it says nothing about the unrestricted four-powers conjecture in [Stewart, §4](https://uwaterloo.ca/pure-mathematics/sites/default/files/uploads/documents/aa133-2-01.pdf).

[Beukers–Stewart, *Neighboring powers*](https://doi.org/10.1016/j.jnt.2009.09.006) give the binomial family and the degree obstruction used here. Their sporadic \((3,5,1)\) example in §7.4 has common power degree 15 and gap degree 8, not the degree-30 case. The tree reduction uses [Pakovich–Zvonkin](https://arxiv.org/abs/1306.4141), and the arithmetic proof below does not use Gröbner basis output as an exclusion certificate.

## 1. From polynomial pairs to 11 weighted plane trees

Write \(F=A^3/B^5\). At infinity \(F=1+c x^{k-30}+O(x^{k-31})\) for \(k=\deg(A^3-B^5)\le15\) and \(c\ne0\). The identity
\[
             F'=A^2 B^{-6}(3A'B-5AB')
\]
forces \(3A'B-5AB'\) to be a nonzero polynomial of degree \(k-15\), since the prefactor has leading exponent \(20-36=-16\). Thus \(k=15\) and the parenthesized expression is a nonzero constant. It follows that \(A,B\) are squarefree and coprime: a multiple root or common root would make this constant vanish. It also follows that all finite preimages of 1 under \(F\) are simple. Consequently \(F\) has three branch partitions \(3^{10}\), \(5^6\), and \((15,1^{15})\), at 0, infinity, and 1, respectively.

Equivalently \(G=F/(F-1)\) is a Belyi map whose zeros have multiplicity 3, whose preimages of 1 have multiplicity 5, and whose poles are one of order 15 and fifteen simple poles. Conversely such a map gives a pair by moving its unique order-15 pole to infinity and writing \(G/(G-1)=A^3/B^5\); the limit at infinity is 1 so both polynomials can be taken monic. The unique distinguished pole also means that equivalences of \(G\) reduce exactly to affine changes of the polynomial parameter. The [weighted-tree correspondence, §2.4 and Theorem 2.24](https://arxiv.org/pdf/1306.4141) identifies this passport with weighted bipartite plane trees having ten black vertices of weighted degree 3 and six white vertices of weighted degree 5. The 15 underlying edges have positive integer weights. A plane tree means a tree with a specified cyclic order at every vertex, modulo orientation-preserving isomorphism.

Here is the full enumeration used for the upper bound. Cut at a marked edge oriented black-to-white, and recursively encode each of the two resulting ordered branches. In a branch with black root, incoming weight \(w\), and \(b\) black and \(c\) white vertices, summing the signed weighted degrees gives \(3b-5c=w\). For a white root the same signed sum is \(-w\). At a branch root the ordered child-edge weights sum to its weighted degree minus \(w\), and must all lie in \(\{1,2,3\}\). Choose a first child weight, assign it a permitted color and vertex-count pair, and recurse on that child and on the remaining children using the remaining counts and weight. An empty child list has zero weight and no child vertices. The marked edge fixes where the cyclic neighbors are read, so these ordered constructions encode all marked plane trees without ambiguity. The same marking is then moved to each black-to-white edge and the least code is kept to forget the marking.

The [checker](verify_stewart_minimum_polynomial_pairs.py) produces 133 distinct edge-rooted codes, with root-weight groups \(47,39,47\) for weights \(1,2,3\), respectively. The unmarked codes give 11 classes, distributed as follows:

| Order of orientation-preserving automorphism group | Not equivalent to mirror | Equivalent to mirror |
| ---: | ---: | ---: |
| 1 | 6 | 2 |
| 3 | 2 | 0 |
| 5 | 0 | 1 |

For example, the automorphism count is 15 divided by the number of distinct codes obtained by re-marking: an automorphism fixing an oriented edge fixes both ordered branches recursively. The mirror codes reverse all cyclic orders. The algebra below independently provides every one of the 11 classes and establishes the real count without a descent assumption for a mirror-fixed tree.

## 2. Three explicit symmetric classes

With \(B=x^6+\beta x\), \(\beta\ne0\), the terms of nonnegative degree in the expansion of \(B^{5/3}\) at infinity give exactly the stated \(A\). The first omitted nonzero term is of degree \(-5\), with coefficient \(\binom{5/3}{3}\beta^3\ne0\). The resulting difference has degree 15. All nonzero complex \(\beta\) give one class by dilation.

For the other two take \(B=x^6+x^3+e\) and require
\[
                           27e^2-9e+1=0 .
\]
Take \(A\) to be the polynomial part of \(B^{5/3}\). In this case the series is \(x^{10}(1+x^{-3}+e x^{-6})^{5/3}\), so the only potentially nonzero coefficient of degrees \(-1,-2,-3,-4\) is the \(x^{-2}\) coefficient. It is \(5(27e^2-9e+1)/243\), hence zero. The powers are not identical: otherwise coprime exponents 3 and 5 force \(B\) to be the cube of a monic quadratic. Since \(B\) is centered, that quadratic would have no linear term, impossible with the \(x^3\) term. Section 1 then forces difference degree 15. These two classes are distinct, because a normalized affine equivalence between centered polynomials is a dilation, and for \(B=x^6+b_3x^3+e\) the ratio \(e/b_3^2\) is invariant under dilation. This ratio is nonreal at both roots and prevents either class from having a real model. The two roots are conjugate over \(\mathbb Q(\sqrt{-3})\).

## 3. Eight further classes certified by one invariant

Centering a monic \(B\) by the unique translation eliminating its \(x^5\) coefficient, write
\[
 B=x^6+b_2x^4+b_3x^3+b_4x^2+b_5x+b_6.
\]
Centering is defined over the polynomial's coefficient field. Under dilation each \(b_i\) is rescaled with weight \(i\), so if \(b_2b_3\ne0\), then
\[
                            X=\frac{b_3^2}{b_2^3}
\]
is an affine invariant. Define
\[
\begin{aligned}
P(X)={}&425018949365248X^8+22295682257118711X^7\\
 &+6316111837287875520X^6-4111834237544927232X^5
   -2314441681632755712X^4\\
 &+1809645368871223296X^3+69231012709662720X^2\\
 &-200937055646121984X+28855583159353344 .
\end{aligned}
\]
The [certificate](stewart_minimum_polynomial_pairs_certificate.json) gives three rational polynomials \(U,Z,H\) of degree at most seven. For every root \(X\) of \(P\), set
\[
 b_2=b_3=X^{-1},\qquad b_4=U(X)X^{-2},\quad
 b_5=Z(X)X^{-2},\quad b_6=H(X)X^{-3}.
\]
This realizes the specified invariant directly, without adjoining a square root of \(X\). The coefficients of \(B^{5/3}/x^{10}\) in \(x^{-1}\) are determined by \(a_0=1,a_1=0\) and
\[
           3k\,a_k=\sum_{i=2}^{\min(6,k)}(8i-3k)b_i a_{k-i},
\]
obtained by logarithmic differentiation of \((1+\sum_i b_i x^{-i})^{5/3}\). In \(\mathbb Q[X]/(P)\) the checker verifies \(a_{11}=a_{12}=a_{13}=a_{14}=0\), \(a_{15}\ne0\). Taking \(A=x^{10}\sum_{k=0}^{10}a_k x^{-k}\) therefore gives a degree-15 difference.

The checker also verifies irreducibility of \(P\) modulo 5 by trying all 780 monic polynomials of degrees 1 through 4 as divisors. Since the degree does not drop modulo 5, \(P\) is irreducible over \(\mathbb Q\); \(X\) is nonzero, and the certified \(a_{15}\ne0\) stays nonzero under each embedding. We get eight inequivalent classes since the invariants have distinct values. These eight are different from the preceding three because \(b_2\) is nonzero, an affine-invariant condition on centered \(B\). Thus 11 constructed classes exhaust the tree upper bound. The eight classes form one Galois orbit because \(P\) is irreducible and all coefficients have been expressed rationally in its root. Their coefficient field up to affine equivalence cannot be smaller than \(\mathbb Q(X)\) because every model with centered monic \(B\) must have that invariant in its coefficient field. By an exact Sturm count \(P\) has two real roots, hence exactly two of these eight classes have real models. None can have a rational model, again by the invariant.

## 4. Integer specializations and the lower coefficient

A nonmonic rational pair approaching square-root scale must have equal leading coefficients in its powers. Otherwise \(|A^3-B^5|\) has degree 30. For leading coefficients \(a,b\) of \(A,B\) with \(a^3=b^5\) and positive leading terms, take \(c=a^2/b^3\in\mathbb Q_{>0}\), so \(a=c^5,\ b=c^3\). After the rational centering, the rational pair is therefore exactly
\[
   B=c^3(x^6+\beta x),\qquad
   A=c^5\left(x^{10}+\tfrac53\beta x^5+\tfrac59\beta^2\right).
\]
Unbounded values along rational parameters force those parameters to be unbounded in absolute value, so approaching square-root scale requires degree at most 15 for the nonzero difference. The formulas are in the sparse ansatz of our [previous arithmetic obstruction, §2](FactorStewartConstructionObstructions.md). That result applies even with variable rational scalings and parameters, and shows that in square-root intervals the limiting normalized separation for the surviving integer specializations is \(1/\sqrt5\). This gives the consequence with every fixed \(\alpha<1/\sqrt5\). No uniform exclusion across pairs of unbounded polynomial degree follows.

To replay both the finite tree enumeration and rational identities, run `python3 verify_stewart_minimum_polynomial_pairs.py` next to its JSON certificate. It uses only standard Python and integer/rational arithmetic. Numerical optimization and external algebra software are not part of verification; discovery of the coefficient table used polynomial elimination, but completeness follows from the checked tree bound and the 11 explicit constructions.
