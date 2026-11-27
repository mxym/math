# Three mutually orthogonal array-bic squares exist above order seven

**Answer to Q3:** \(\operatorname{MOAS}(10,3)\) exists. More generally,
for every positive integer \(q\) coprime to six there is a
\(\operatorname{MOAS}(7q+3,3)\). The order-ten arrays are given as
standalone static data in [arrays_order10.json](arrays_order10.json).

**Source.** Sam Adriaensen, John Bamberg, and Jason Williford,
[*On configurations that are nearly generalised polygons*,
arXiv:2611.17855v1](https://arxiv.org/abs/2611.17855v1), submitted
13 November 2026. The array-bic and orthogonality conditions are
[Definitions 2.16 and 2.17, printed p. 10](https://arxiv.org/pdf/2611.17855v1#page=10).
[Section 3, Q3, printed p. 13](https://arxiv.org/pdf/2611.17855v1#page=13)
asks: “Does there exist a MOAS\((s,3)\) for \(s>7\)?”
Their Example 2.18, printed p. 11, supplies the order-three seed used
here. The claimed answer is existence, not a classification of
orders. In particular we make no nonexistence claim about 8 or 9
or minimality claim about 10. Three squares also do not assert
a regular antipodal plane at these orders: Proposition 2.20
would require \(s\) mutually orthogonal squares.

## 1. Definitions and the small kernel

Use a set \(S\) of \(s\) row and column labels and a separate
symbol \(0_*\notin S\). A square of position \(i\in S\) has empty
diagonal, and its other entries are in \((S\setminus\{i\})\cup\{0_*\}\).
Its column \(i\) is filled with \(0_*\) off the diagonal; any other
column contains every \(S\setminus\{i\}\) symbol once. Its row \(x\)
contains every \(S\setminus\{i,x\}\) symbol once, as well as \(0_*\)
if \(x\ne i\). For distinct positions \(i,k\), orthogonality means
that the ordered outputs in equal off-diagonal cells give each
allowed ordered pair exactly once: the pair may not have equal
symbols, and the swapped pair \((k,i)\) is excluded.

Take \(H=\{1,2,3\}\), with positions \(i=1,2,3\).
The order-three kernel \(K_i\), as in the source, is the following
rule on \(H\times H\) off the diagonal:
\[
 K_i(x,y)=
 \begin{cases}
   0_*,&y=i,\\
   \text{the element of }H\setminus\{i,y\},&x=i,\ y\ne i,\\
   y,&x\ne i,\ y\ne i.
 \end{cases}
\]
The row and column requirements follow immediately: in row \(i\)
the two non-special symbols are exchanged; any other row has
\(0_*\) and the one remaining allowed symbol. Each column \(y\ne i\)
has \(y\) and the remaining symbol. For a pair \(i,k\) and third
position \(l\), the six output pairs are
\((l,0_*),(0_*,l),(k,l),(l,i),(0_*,i),(k,0_*)\), as is seen by
taking the cells \((i,k),(k,i),(i,l),(k,l),(l,i),(l,k)\)
in that order. These are exactly the allowable pairs at order three.

## 2. Four-region construction

Adjoin a finite additive group \(G\), disjoint from \(H\)
and from \(0_*\), to get the label set \(S=H\sqcup G\).
The group identity in \(G\) is *not* the symbol \(0_*\).
Write \(G^\times=G\setminus\{0_G\}\); this notation does not
imply a multiplicative group. For each position \(i\in H\) use:

* A two-element set \(D_i\subset G^\times\), with the three
  sets pairwise disjoint, and a bijection
  \(\eta_i:D_i\to H\setminus\{i\}\).
* \(f_i:G^\times\setminus D_i\to G\);
  \(\beta_i:H\setminus\{i\}\to G\);
  \(\gamma_i:H\to G\).

The off-diagonal rule in each region is
\[
\begin{array}{c|l}
(x,y)&A_i(x,y)\\ \hline
H\times H & K_i(x,y)\\
H\times G & y+\gamma_i(x)\\
G\times H & 0_*\text{ if }y=i,\quad x+\beta_i(y)\text{ otherwise}\\
G\times G & \eta_i(d)\text{ if }d=y-x\in D_i,\quad
              x+f_i(d)\text{ otherwise}.
\end{array}
\tag{1}
\]
Use the following three difference tests. The braces in these tests
mean **lists with multiplicity**, so matching a target set requires each
entry exactly once:
\[
\begin{aligned}
 R_i&=\{f_i(d):d\in G^\times\setminus D_i\}
           \ \sqcup\ \{\beta_i(y):y\in H\setminus\{i\}\}=G^\times,\\
 C_i&=\{f_i(d)-d:d\in G^\times\setminus D_i\}
           \ \sqcup\ \{\gamma_i(x):x\in H\}=G,\\
 P_{ik}&=\{f_k(d)-f_i(d):d\in G^\times\setminus(D_i\cup D_k)\}\\
 &\hspace{17mm}\sqcup\ \{\beta_k(l)-\beta_i(l)\}
           \ \sqcup\ \{\gamma_k(x)-\gamma_i(x):x\in H\}=G^\times,
           \qquad l\in H\setminus\{i,k\}.
\end{aligned}
\tag{2}
\]

**Each square.** For a row \(x\in H\), the kernel gives all the
allowed small symbols, and the \(H\times G\) part is a translation
giving all of \(G\). For a row \(x\in G\), its \(G\times H\)
part gives the one \(0_*\); the special differences \(D_i\)
give each \(H\setminus\{i\}\) symbol; its other entries are
\(x+R_i\), which is \(G\setminus\{x\}\). Column \(i\) is all
\(0_*\) off the diagonal. For a different column \(y\in H\), the
kernel gives \(H\setminus\{i\}\) and the outer rows give all of
\(G\) by translation. In a column \(y\in G\), the special
differences give all \(H\setminus\{i\}\); the non-special
\(G\times G\) values are \(y+f_i(d)-d\), and the \(H\times G\)
values are \(y+\gamma_i(x)\). Together they give \(y+C_i=G\).
This verifies all four conditions in Definition 2.16.

**Each pair of squares.** Fix \(i<k\), and call the elements of
\(H\cup\{0_*\}\) small.

1. Both outputs small: these are exactly the \(H\times H\)
   cells, giving the six allowed pairs of the kernel. In
   \(G\times G\) the sets \(D_i,D_k\) are disjoint, so they
   cannot both give small values. The mixed regions cannot
   give two small values either.
2. One output small, one in \(G\): if the first output is
   \(0_*\), the cells are \((x,i)\) for \(x\in G\); the second
   output takes every value \(x+\beta_k(i)\) once. If the
   first output is a label in \(H\setminus\{i\}\), its unique
   corresponding difference \(d\in D_i\) gives
   \((x,x+d)\) for \(x\in G\); the second output is
   \(x+f_k(d)\), again each \(G\) symbol once. Swapping the
   roles proves all pairs with the second output small.
3. Both outputs in \(G\): on \(G\times G\) this occurs
   for the differences outside \(D_i\cup D_k\).
   Each such difference contributes, as \(x\) varies, all
   ordered pairs whose second output minus the first is
   \(f_k(d)-f_i(d)\). On \(G\times H\) the only column giving
   two outer outputs is \(l\), contributing the difference
   \(\beta_k(l)-\beta_i(l)\) in exactly the same way. On
   \(H\times G\) each small row \(x\) contributes the
   difference \(\gamma_k(x)-\gamma_i(x)\) as \(y\) varies.
   These six or more translation classes are disjoint and
   cover exactly the unequal pairs in \(G\times G\) by \(P_{ik}\).

This gives all allowed ordered pairs precisely once and no forbidden
pair, proving Definition 2.17 for all three pairs of squares.

## 3. The certificate in the cyclic group of order seven

For \(G=\mathbb Z/7\mathbb Z\), identify its symbols with array
labels \(4,\ldots,10\) by adding 4; \(0_*\) is numeric 0.
The table provides every parameter in (1). A dash indicates
an unused value. When defining \(\eta_i\), take the two
members of \(D_i\) in the displayed order and the two elements
of \(H\setminus\{i\}\) in increasing order.

| \(i\) | \(D_i\) | \(f_i(d)\) for \(d=1,2,3,4,5,6\) | \(\beta_i(1),\beta_i(2),\beta_i(3)\) | \(\gamma_i(1),\gamma_i(2),\gamma_i(3)\) |
|---|---|---|---|---|
| 1 | \(1,6\) | –, 1, 6, 4, 2, – | –, 3, 5 | 1, 2, 5 |
| 2 | \(2,5\) | 2, –, 5, 1, –, 6 | 4, –, 3 | 3, 5, 6 |
| 3 | \(3,4\) | 6, 3, –, –, 1, 5 | 2, 4, – | 4, 0, 2 |

The \(f_i\) values fill \(G^\times\) once combined with the
respective \(\beta_i\), verifying \(R_i\).
The four shifts \(f_i(d)-d\), in increasing admissible \(d\), are
\((6,3,0,4)\), \((1,2,4,0)\), and \((5,1,3,6)\); the
\(\gamma_i\) rows complete these to \(G\).
For the three pairs, here are the full lists \(P_{ik}\), grouping
first the two outer differences (in increasing \(d\)), then the
one \(\beta\) difference, then the three \(\gamma\) differences:
\[
 \begin{array}{c|ccc}
 (i,k)&\text{outer}&\text{column }l&\text{small rows}\\ \hline
 (1,2)&(6,4)&5&(2,3,1)\\
 (1,3)&(2,6)&1&(3,5,4)\\
 (2,3)&(4,6)&5&(1,2,3).
 \end{array}
\]
Each is a permutation of \(1,\ldots,6\). Thus (1) gives the
asserted order-ten triple without needing a search or a program.

## 4. Infinitely many orders

For positive \(q\) with \(\gcd(q,6)=1\), use
\(G=\mathbb Z/(7q)\mathbb Z\), and let \(U\) be the subgroup
of order seven, embedded by \(j\mapsto qj\).
Embed \(D_i,\beta_i,\gamma_i\) and the above values of \(f_i\)
on \(U^\times\setminus D_i\) by this map, and keep \(\eta_i\)
on the embedded special differences. On \(d\in G\setminus U\),
define \(f_i(d)=a_i d\), with \(a_1=2,a_2=3,a_3=4\).
The interior of \(U\) in (2) is exactly the verified order-seven
lists. Outside \(U\), the additional terms in \(R_i,C_i,P_{ik}\)
are multiplication by \(a_i\), \(a_i-1\), and \(a_k-a_i\),
respectively. These are units modulo \(7q\) because their prime
divisors are among 2 and 3. Each of these multiplications maps
\(U\) onto itself, and being bijective on \(G\) maps its
complement onto itself. Therefore each outside list covers
\(G\setminus U\) once and does not enter the subgroup lists.
All of (2) hold, and the construction has order \(7q+3\).

## 5. Replay and prior-work scope

All proofs above are exact. With Python 3.10+ (standard library):
```sh
python3 verify_parameters.py
python3 verify_static.py
```
The first verifies the parameter criteria, expands (1) to compare
with the fixed order-ten matrices, and checks sample larger orders
without relying on the matrix checker. The second uses only the
static matrices and checks the original row, column and pair
definitions directly; it also rejects a deliberate corruption.

The order-three kernel and definitions are from the cited paper.
The new part is the cyclic-group difference construction above
and its exact parameter certificate. Searches to 27 November
2026 covered the arXiv number and title, author combinations,
the phrases “array-bic squares” and “MOAS(10,3)” and Q3
solutions or follow-ups. No same-scope construction appeared in the
primary sources located; this does not assert absolute priority.
