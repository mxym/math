# Nonregular extremal pairs of MOLS from the Csörgő–Drápal loop

For every prime \(p\geq5\) there are two orthogonal Latin squares of order
\(3p^2\) whose joint autotopy group is transitive on the cells and contains no
regular subgroup. The number two is the maximum for **jointly cell-transitive**
MOLS of this order, by Keita–Shapiro's sharp bound. In particular, this gives
negative instances of the regularity question in their Remark 5.11 with two
squares, not just a one-square family.

The first square before the factor of three is a relabeling of a known
Csörgő–Drápal conjugacy-closed loop. We construct a common-transitive
orthogonal mate, give a self-contained obstruction to regularity for the
whole autotopy group of the first square, and prove that the obstruction
survives the product used for extremality. Neither the seed loop, the general
direct-product construction for MOLS, nor the numerical bound is new.

## 1. Conventions and the cubic pair

For a Latin square \(L:R\times C\to V\), an autotopy is a triple of
permutations \((\rho,\kappa,\sigma)\) satisfying
\(L(\rho r,\kappa c)=\sigma L(r,c)\). For a pair the two symbol permutations
are independent but the row and column permutations are shared. Coordinate
roles are fixed: we do not allow an exchange of the squares, rows, or
columns. The action on cells is faithful because the symbol permutation
of each square is determined by the action on rows and columns. A regular
action is transitive with trivial point stabilizers, equivalently free and
transitive. Coordinatewise relabeling conjugates the action on cells.

Let \(F=\mathbf F_p\) and \(Q=F^2\), with both rows and columns indexed by \(Q\).
For \(t\in\{1,2\}\) set
\[
 L_t((x,y),(u,v))=(z,w)
 =(x+tu,\ y+tv+t x^2u-2xu^2).
 \tag{1}
\]
In a fixed row, the first coordinate determines \(u\), then the second
determines \(v\); in a fixed column they determine \(x\) and \(y\) in that
order. The two squares are orthogonal: their first coordinates \(z_1,z_2\)
recover \(u=z_2-z_1\) and \(x=2z_1-z_2\). After subtracting the known cubic
terms, the two other coordinates are \(y+v,y+2v\), which recover \(y,v\).

## 2. Joint transitivity

The following table gives two types of base-coordinate shift and one type
of fiber shift. The row and column entries do not depend on \(t\); the
symbol entry is evaluated for each \(t\) separately:
\[
\begin{array}{c|c|c|c}
 &\text{row }(x,y)&\text{column }(u,v)&
     \text{symbol }(z,w)\text{ of }L_t\\ \hline
 A_a&(x+a,y+a x^2)&(u,v+3a u^2-a^2u)&(z+a,w+a z^2)\\
 B_b&(x,y-3b x^2+2b^2x)&(u+b,v-2b u^2)&(z+tb,w-2b z^2/t)\\
 T_{r,s}&(x,y+r)&(u,v+s)&(z,w+r+ts)
\end{array}
\tag{2}
\]
These are permutations since each first-coordinate shift is invertible
and the second-coordinate changes are translations on fibers.
For \(A_a\), substituting into (1) gives the increment in \(w\)
\[
 ax^2+(3t a-2a)u^2-t a^2u+t(2ax+a^2)u
   =a(x+tu)^2.
\]
For \(B_b\) it gives
\[
 (-3b+tb)x^2-4b xu-2tb u^2+2b^2x-2b^2x
   =-\frac{2b}{t}(x+tu)^2 .
\]
Both equalities use \(t^2-3t+2=0\). The corresponding increments of \(z\)
are \(a,tb\), respectively. The formula for \(T_{r,s}\) follows just by
linearity in \(y,v\). Thus these are joint autotopies. Taking \(a,b\)
arbitrarily first puts the row and column base coordinates wherever
desired, and \(r,s\) then put both fiber coordinates wherever desired.
This gives transitivity on the \(p^4\) cells.

## 3. The first square cannot act regularly

### 3.1 The known loop and its stabilizer

Apply the same coordinate bijection
\[
 h(x,y)=\bigl(x,(y+(2/3)x^3)/3\bigr)
\]
to the rows, columns and symbols of \(L_1\). The result is the loop with
identity \((0,0)\) and product
\[
 (x,y)*(u,v)=(x+u,\ y+v+x^2u).                     \tag{3}
\]
Indeed \(x^2u-2xu^2+(2/3)((x+u)^3-x^3-u^3)=3x^2u\).
Division by 3 is why we take \(p\geq5\). This is the known third
nonassociative conjugacy-closed loop of order \(p^2\) in the
Csörgő–Drápal description, not a new loop. Its transitivity here also
follows from (2) by conjugation.

Write \(E=\{0\}\times F\). For three inputs with first coordinates
\(x,u,k\), the second-coordinate difference between
\(((x,y)*(u,v))*(k,\ell)\) and \((x,y)*((u,v)*(k,\ell))\) is
\(2xuk\), by expanding (3). So an element with first coordinate
different from 0 fails to associate in the first position when \(u=k=1\).
Elements of \(E\) commute and associate in all positions directly by
(3). Thus the loop center (the elements with both properties) is
exactly \(E\), a characteristic subgroup. Both \(E\) and the quotient
by its cosets have the additive group of \(F\). An automorphism induces
multipliers \(d,s\in F^\times\) on the center and quotient, respectively,
because \(F\) is prime. As \((x,y)=(x,0)*(0,y)\), the automorphism has
form \((x,y)\mapsto(sx,dy+g(x))\). Its product equation is
\[
 g(x+u)-g(x)-g(u)=(s^3-d)x^2u.
\]
The left side is symmetric in \(x,u\), whereas \(x^2u\) is not (test
\(x=1,u=2\)). Hence \(d=s^3\) and \(g\) is additive, so \(g(x)=c x\).
Conversely, every \((x,y)\mapsto(sx,s^3y+c x)\) preserves (3).
There are \(p(p-1)\) such automorphisms.

For any loop an autotopy fixing the identity cell has its row and
column permutations fix the identity. Evaluating the autotopy
identity along either identity axis shows that all three permutations
coincide and form a loop automorphism. Thus for (3) the cell stabilizer
has order \(p(p-1)\), and the full autotopy group \(G\) has order
\(p^5(p-1)\) by transitivity. Indeed the triples in (4) move the identity cell to
all cells, so together with the diagonal stabilizer they generate
all autotopies. Its Sylow \(p\)-subgroup \(P\) is unique:
the number of such subgroups divides \(p-1\) and is 1 modulo \(p\).

### 3.2 A forced cell stabilizer in every candidate regular group

The following triples act on (3) (direct substitution); the variables
in each position are \((x,y)\) in the row, \((u,v)\) in the column,
and \((z,w)\) in the symbol:
\[
\begin{array}{c|c|c|c}
 A&(x+1,y+x^2)&(u,v+u^2-u)&(z+1,w+z^2)\\
 B&(x,y-x^2)&(u+1,v)&(z+1,w)\\
 S_c&(x,y+c x)&(u,v+c u)&(z,w+c z)\\
 F_{h,k}&(x,y+h)&(u,v+k)&(z,w+h+k)
\end{array}
\tag{4}
\]
The increments in the symbol fiber for \(A,B\) are \(z^2,0\), respectively:
for \(A\) the extra term in \((x+1)^2u\) is \(2xu+u\), which combines
with the row/column increments to give \((x+u)^2\); for \(B\) the
change \(x^2\) in \(x^2(u+1)\) is canceled in the row fiber. The
autotopies \(A,B,S_1\) have order \(p\). For \(A\), on a shifting
base coordinate the fiber changes over \(p\) iterations sum to
\(\sum_{j\in F}j^2=0\) (multiply the sum by \(2^2\ne1\)); the unchanged
column base simply repeats its fiber shift \(p\) times. For \(B\)
and \(S_1\) the same check is immediate by addition. They belong to
the unique \(P\).

Write \([U,V]=UVU^{-1}V^{-1}\), with the rightmost map applied first.
For \(A,S_1\), the shear on the row fiber under conjugation changes
from \(x\) to \(x-1\), and likewise on the symbol, with no change
in the column. For \(B,S_1\), it is the column and symbol that change,
from \(u\) to \(u-1\) and \(z\) to \(z-1\), respectively. Hence
\[
 [A,S_1]=F_{-1,0},\qquad [B,S_1]=F_{0,-1}.
\]
For \([A,B]\) the base shifts cancel in all three positions. The
respective surviving increments are
\[
 x^2-(x-1)^2=2x-1,\qquad
 (u^2-u)-((u-1)^2-(u-1))=2u-2,\qquad
 (z-1)^2-(z-2)^2=2z-3 .
\]
Thus \([A,B]=F_{-1,-2}S_2\). The two preceding commutators generate
every \(F_{h,k}\), so \(S_2\) belongs to \(P'\). It is nonidentity
and fixes the identity cell.

A regular subgroup would have order \(p^4\), hence lie in \(P\) as
an index-\(p\) subgroup. Any such subgroup contains \(P'\): the action
of \(P\) on its \(p\) cosets is transitive and has image a \(p\)-subgroup
of the symmetric group on \(p\) letters, thus an order-\(p\) image,
with the original index-\(p\) subgroup as kernel. So any candidate
contains \(S_2\) and fails to be free. This rules out regularity
for (3), and therefore for \(L_1\) and for the common group of the
two squares in (1).

## 4. The product of order \(3p^2\) and extremality

Use the additive and twice-slope squares \(M_t(a,b)=a+t b\) on
\(\mathbf F_3\), for \(t=1,2\). They are Latin, are orthogonal since the
two slopes differ, and the two input translations act regularly on
the cells with the induced symbol translations. Define the product pair
on \(Q\times\mathbf F_3\) by
\[
 N_t((r,a),(c,b))=(L_t(r,c),M_t(a,b)),\qquad t=1,2.
 \tag{5}
\]
The Latin and orthogonality conditions hold componentwise; the product
of the two exhibited transitive groups gives joint transitivity. We
still must rule out a new regular subgroup that mixes the product factors.

After applying \(h\) in the \(Q\) coordinate, \(N_1\) is the loop
\(Q_*\times C_3\), where \(Q_*\) denotes (3). Its center is
\(E\times C_3\): commutation and each of the three associativity
tests split coordinatewise, and \(C_3\) is abelian. Inside that
center, \(\{e\}\times C_3\) is exactly the set of elements of order
dividing 3, and hence characteristic in the whole loop. If \(\phi\)
is a loop automorphism, the \(C_3\)-component of
\(q\mapsto\phi(q,0)\) is a homomorphism \(Q_*\to C_3\).
Every nonempty fiber of that homomorphism is a translate of the
identity fiber: multiplication by a fixed preimage is a bijection
onto the fiber, with inverse obtained by loop division and group
cancellation. Its image size therefore divides \(p^2\) and 3,
so it is trivial. Consequently \(\phi\) preserves \(Q_*\times\{0\}\)
as well, by finiteness. Given \((q,b)=(q,0)*(e,b)\), \(\phi\)
acts separately on the two factors. This proves full loop-automorphism
splitting, not just inclusion of product automorphisms.

Both factors have transitive autotopy groups. For any autotopy of
\(Q_*\times C_3\), choose a product autotopy taking the identity cell
to the same image. Their difference fixes that cell, and, as proved
in §3.1, is a loop automorphism in all three coordinates; it splits
by the preceding argument. Thus the full autotopy group of \(N_1\)
is the direct product of the two autotopy groups in their action
on the product of cell sets.

Now suppose \(N_1\) has a regular group \(H\) on the \(9p^4\) cells.
Its Sylow \(p\)-subgroup \(U\) has order \(p^4\). By the splitting,
\(U\) acts on the \(9\) cells of the \(C_3\) factor. Orbit sizes
are powers of \(p\), and \(p\nmid9\), so some cell of that factor
is fixed by all of \(U\). On the fiber over that cell \(U\)
therefore acts by autotopies of \(Q_*\), and acts freely because
\(H\) was free on the full product. The restriction to this fiber
is injective (a restriction in the kernel would fix every point
of that fiber), and the order \(p^4\) equals the fiber size.
This contradicts §3.2. In particular, a common regular group
for \(N_1,N_2\) is impossible, because forgetting the second square
leaves a subgroup of the autotopy group of \(N_1\) with the same
action on cells.

Finally \(f(3p^2)=\min(3-1,p^2-1)=2\), in the notation of Keita–Shapiro.
Their Theorem 5.7 makes (5) extremal among jointly cell-transitive
families, not necessarily among arbitrary MOLS of that order.

## 5. Sources and exact scope

* A. Keita and I. Shapiro, *Transitive Sets of Mutually Orthogonal
  Latin Squares*, [arXiv:2601.22205v2](https://arxiv.org/abs/2601.22205v2),
  18 November 2026. Definition 2.4 names the two transitivity notions;
  Proposition 2.5 is the positive product construction; Theorem 5.7 and
  Corollary 5.10 give the sharp bound. Remark 5.11 (p. 10 of the PDF)
  leaves outside the theorem both the classification of equality groups
  and whether equality families must be simply transitive. Example 6.1
  (p. 11) gives a single non-topolinear square of order 9, not an
  extremal family. This note proves nonregularity for a two-square
  extremal family; it does not classify all equality groups.
* A. Keita, [dissertation](https://cs.uwaterloo.ca/~cbright/group/amadou_thesis.pdf),
  Chapter 5, Examples 5.5.11 (pp. 132–133) and 5.5.13 (pp. 133–135).
  The latter's square \(M'\) already provides a **singleton** transitive
  but not simply transitive family in order 10, for which the later
  bound is \(f(10)=1\). Hence even a negative answer to the unrestricted
  yes/no question is not claimed here as a first.
* D. S. Krotov and V. N. Potapov, *Constructions of transitive Latin
  hypercubes*, [arXiv:1303.0004v3](https://arxiv.org/abs/1303.0004v3),
  DOI [10.1016/j.ejc.2015.12.001](https://doi.org/10.1016/j.ejc.2015.12.001).
  Section 8 asks for a non-topolinear, isotopically transitive single
  square; Keita–Shapiro already answer that question. Proposition 2
  concerns preservation of **positive** transitivity and topolinearity
  under products of factors having the corresponding property.
* V. N. Potapov, *Isotopically transitive pairs of MOLS*, [Mal'tsev
  Meeting abstracts, 2015](https://math.nsc.ru/conference/malmeet/15/malmeet15.pdf),
  p. 146, Theorems 1–2, supplies a related two-layer construction using
  **quadratic** corrections and a different coefficient condition.
  In (1) each base and fiber coefficient row is the same \((1,t)\),
  and the corrections have mixed degree three. In odd characteristic
  a square in the quadratic construction has a group-table isotope:
  for a base output \(l_1x+l_2u\), a multiple of its square removes
  the single mixed quadratic term \(xu\), and the remaining univariate
  terms are absorbed in the row and column fibers. Here \(l_1,l_2\)
  and both fiber coefficients are nonzero by the Latin property of
  the triangular model. By contrast (3) is a nonassociative loop,
  whereas any group-table isotope that is a loop is isomorphic to
  that group: if a loop's product satisfies
  \(\rho(x)\kappa(y)=\sigma(x*y)\) in the group, the two identity
  axes give \(\sigma(x*y)=\sigma(x)\sigma(e)^{-1}\sigma(y)\), so
  \(\sigma(e)^{-1}\sigma\) (left multiplication of its values) is
  a group isomorphism. Potapov's result on not being isotopic to a linear or
  Cartesian-product **pair** is not a no-regular-subgroup claim.
* K. Kunen, *The structure of conjugacy closed loops*, Trans. AMS
  **352** (2000), 2889–2911,
  [DOI 10.1090/S0002-9947-00-02350-3](https://doi.org/10.1090/S0002-9947-00-02350-3),
  Theorem 4.17(2) (pp. 2908–2909) classifies the nonassociative CC loops
  of order \(p^2\). In its \(C(p,0)\) coordinates the extra fiber term
  is \(xu(u-1)/2\). The map
  \((x,y)\mapsto(x,-y/2+x^3/6-x^2/4)\) is an explicit isomorphism
  from (3) to that representation: the added univariate term has
  additive difference \((x^2u+xu^2-xu)/2\).
  P. Csörgő and A. Drápal, *Left conjugacy closed loops of nilpotency
  class two*, Results Math. **47** (2005), 242–265,
  [DOI 10.1007/BF03323028](https://doi.org/10.1007/BF03323028),
  describe the seed (3); the exact formula is reproduced in
  [LOOPS manual §9.7.2, Case m=3](https://gap-packages.github.io/loops/doc/chap9_mj.html).
  The generator computation in §3 is included as a direct
  proof, not a claim to classification priority for that known loop.
  Multiplication groups generated by left/right translations in the
  literature need not be the full autotopy group acting on cells.

Searches on 27 November 2026 combined the named papers, *jointly
transitive MOLS*, *non-topolinear orthogonal pair*, *non-simply
transitive extremal MOLS*, and *conjugacy closed loops* with *orthogonal
Latin square* and *autotopy group*. The primary sources checked above
did not give the specific combination of a jointly transitive cubic
orthogonal pair with the obstruction and its \(3p^2\) extremal lift.
This is a bounded literature check, not a universal priority claim.

## 6. Reproducibility

Python 3 standard library only. The scripts are independent and neither
imports the other. The universal result is the proof above; finite runs
are regression and witness checks.

```text
python3 verify_construction.py
python3 verify_atop.py
```

Expected independent raw-table checks:

```text
p=5, b=1: |Aut_loop|=20, |Atop|=12500, |P|=3125, |P'|=125, |P' intersect stab|=5
p=7, b=1: |Aut_loop|=42, |Atop|=100842, |P|=16807, |P'|=343, |P' intersect stab|=7
p=5, b=3: |Aut_loop|=40, |Atop|=225000, |P|=3125, |P'|=125, |P' intersect stab|=5
associative translation control PASS
PASS raw autotopy
```
