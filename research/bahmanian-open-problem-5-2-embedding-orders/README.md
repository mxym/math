# Exact sharpness of the simple multi-Latin embedding bound

Let \(E(r,\lambda)\) be the worst, over simple partial
\(r\times r\) \(\lambda\)-Latin squares on \(r\) symbols, of the
smallest order of a simple \(\lambda\)-Latin square extending
the partial array. We prove
\[
 E(r,\lambda)=
 \begin{cases}
 \lambda,&\lambda\ge r,\\
 3,&(r,\lambda)=(2,1),\\
 5,&(r,\lambda)=(3,1),\\
 2r,&\text{otherwise}.
 \end{cases}
\]
In the last case the obstruction is a cyclic square changed in
only three cells, with one vacant slot in each of two cells.

A related but different question asks for the fixed orders at
which **every** partial array embeds. We also determine the exact
set of such orders:
\[
 \mathcal U(r,\lambda)=
 \begin{cases}
 \{n:n\ge2r\},&\lambda<r,\\
 \{\lambda\}\ \cup\ \{n:n\ge\max(2r,\lambda)\},&\lambda\ge r .
 \end{cases}
\]
One cannot recover the worst minimum order just by testing which
individual fixed orders are universal.

## 1. The question and the model

Amin Bahmanian,
[*Ryser’s theorem for simple multi-Latin rectangles*](https://doi.org/10.1007/s10623-025-01728-3),
Designs, Codes and Cryptography **93** (2025), 5535–5550. The
[version of record, §5, Problem 5.2, printed p. 5549](https://d-nb.info/1387819259/34#page=15)
asks, for \(\lambda\le r\), for a single partial array with no
embedding order below \(2r\). In
[arXiv:2509.11471v1, §5, Problem 5.2, p. 12](https://arxiv.org/pdf/2509.11471v1#page=12)
the same question ranges over all positive \(r,\lambda\), with
bound \(r+\max\{r,\lambda\}\). The original alphabet \([r]\)
is the one stated in the discussion before the problem and in
[Corollary 4.4, printed p. 5547](https://d-nb.info/1387819259/34#page=13).

A simple partial array on \([r]\) has a subset of at most
\(\lambda\) symbols in each cell, with each symbol occurring at
most \(\lambda\) times in each row and column. An extension of
order \(n\ge r\) has \(\lambda\) distinct symbols from \([n]\)
in each cell and preserves every prescribed entry in the original
top-left block. Each of its \(n\) symbols occurs exactly \(\lambda\)
times in each row and column (by the at-most condition and row
or column total). Completion at \(n=r\) counts as an embedding.
If one instead requires a **strictly larger** order, see §5
below. No conclusion relies on assuming a missing old symbol is
still required as a prescribed entry: one can choose the original
alphabet as any \(r\)-subset of the target alphabet by relabelling.

## 2. The two-vacant-slot construction

Suppose \(1\le\lambda<r\), \(\lambda(r-1)>2\).
Relabel the original rows, columns, and symbols by
\(\mathbb Z/r\mathbb Z\). For every \(i,j\) start with the full
simple \(\lambda\)-Latin square
\[
 C_{ij}=\{i+j,i+j+1,\ldots,i+j+\lambda-1\}\pmod r .
\]
For a fixed row or column, a symbol occurs for exactly one index
at each of the \(\lambda\) offsets. The entries 0 and 1 occur
alone relative to each other in the cells with \(i+j=1-\lambda\)
(only 0) and \(i+j=1\) (only 1), respectively; this follows by
comparing the consecutive residue windows which contain either.
Each exceptional diagonal is a perfect matching from rows to
columns, and the two matchings are disjoint since \(\lambda<r\).
Their union is a set of alternating even cycles.

Set \(a=1-\lambda\). In an alternating path of three edges the
cells are \((0,a)\), \((\lambda,a)\), \((\lambda,a-\lambda)\);
the first and third contain only 0 among the two chosen symbols,
and the middle contains only 1. Delete the 0 at the first and
third cells, and change the 1 to 0 in the middle cell. This is
equivalently the two-colour switch on the length-one component
created by cutting the two disjoint matching edges. The other
symbols and all other cells stay unchanged. The rows \(0,\lambda\)
are distinct, as are the columns \(a,a-\lambda\).
Row 0 now lacks one 0 and is otherwise full; row \(\lambda\)
has lost a 0 and replaced a 1 by 0, so lacks one 1.
Column \(a\) likewise lacks one 1; column \(a-\lambda\) lacks
one 0. Every other row and column still has exactly \(\lambda\)
occurrences of each symbol, and simplicity is preserved because
the inserted 0 was absent in the middle cell. The two vacant
slots have these respective forced colours in the row/column:
\[
 (0,a):\ (0,1),\qquad
 (\lambda,a-\lambda):\ (1,0).
\]
Neither can be completed at order \(r\).

Next suppose \(n=r+\delta\) with \(1\le\delta\le r-1\).
Each of the \(\delta\) new symbols occurs \(\lambda r\) times
in the first \(r\) rows of any extension. At most
\(\lambda\delta\) of these occurrences lie in the last \(\delta\)
columns, since a column contains \(\lambda\) occurrences in all
its rows. The top-left block must therefore contain at least
\(\lambda(r-\delta)\) occurrences of each new symbol. All must
fit in the two vacant slots since no new symbol was prescribed.
Yet their total is at least
\[
 \lambda\delta(r-\delta)\ \ge\ \lambda(r-1)\ >2 .
\]
The inequality uses
\(\delta(r-\delta)-(r-1)=(\delta-1)(r-\delta-1)\ge0\).
Thus no order below \(2r\) works. Corollary 4.4 gives the
extension at \(2r\) for every partial array with \(\lambda<r\).
The stated construction therefore attains the worst minimum
order whenever \(\lambda(r-1)>2\) and \(\lambda<r\).

## 3. Exceptional first-order minima

If \(\lambda\ge r\), a simple target needs at least \(\lambda\)
symbols per cell, so \(n\ge\lambda\). At \(n=\lambda\), fill
every cell with all \(\lambda\) symbols. Every original partial
array is contained in that square, proving \(E=\lambda\).

For the remaining pairs \((2,1)\) and \((3,1)\), the following
are partial arrays, with a dot denoting absence:
\[
 \begin{pmatrix}1&\cdot\\ \cdot&2\end{pmatrix},
 \qquad
 \begin{pmatrix}
 \cdot&\cdot&1\\
 2&3&\cdot\\
 3&2&\cdot
 \end{pmatrix}.
\]
The first cannot be a 2-square completion since its
off-diagonal cells would need different symbols from their rows
and columns. In the second, the empty cells in column 3 at rows 2
and 3 each already have 2 and 3 in their row, and 1 in their column.
They cannot both be filled at order 3 or at order 4: at order 3
no symbol is available there, and at order 4 both cells would
require the unique new symbol in the same column.

Here is an upper bound for **every** partial in these two cases,
independent of enumeration. An ordinary partial \(r\)-square with
zero holes is full, and with one hole has a completion at order
\(r\): the global deficit multiset read by rows is the same as
the one read by columns, forcing the same missing symbol in the
one deficient row and column. Otherwise let \(h\ge2\) be the
number of holes and \(t\) the number of absent old symbols.
Each present old symbol has at most \(r\) occurrences, so
\(h\ge rt\). For \(r=2,3\) it follows that
\(h\ge(r-1)+t\): for \(t=0\) use \(h\ge2\), and for \(t\ge1\)
use \(rt\ge r-1+t\). In distinct holes, prescribe one occurrence
of each of the \(t\) absent old symbols and the \(r-1\) new
symbols, which is possible since none has yet been used. Then
fill the remaining holes greedily using the \(2r-1\) symbols:
any unfilled cell has at most \(2(r-1)\) symbols forbidden
by its occupied row and column. The full \(r\times r\) block
uses all \(2r-1\) symbols. By [Ryser's classical embedding theorem
(1951)](https://doi.org/10.1090/S0002-9939-1951-0042361-0),
a full \(r\times r\) Latin rectangle on \(n\) symbols embeds
at order \(n\) if each symbol appears at least \(2r-n\) times.
Here this lower bound is one, so the filled block embeds at
order \(2r-1\). This proves the exceptional values 3 and 5.

## 4. Supplement: the spectrum of fixed universal target orders

When \(\lambda<r\), Corollary 4.4 gives universality for
\(n\ge2r\). The fully filled cyclic square \(C\) of §2 cannot
be contained at any fixed \(r<n<2r\): the count giving
\(\lambda(r-\delta)>0\) for a new symbol would require a vacant
slot in \(C\), which has none. The examples above show that
order \(r\) itself is not universal. Thus this case gives
\(\mathcal U(r,\lambda)=\{n:n\ge2r\}\), including the two small
exceptions to the worst-minimum formula.

Now let \(\lambda\ge r\). The partial array \(S_r\) containing
all \(r\) original symbols in every cell is allowed and contains
every other original partial array. Thus a fixed target order
is universal iff it accommodates \(S_r\). Set
\(\mu=\lambda-r\) and, for \(n\ge\lambda\), set \(\delta=n-r\).
An old symbol must occur \(r^2\) times in the top-left block
and \(r\mu\) in each of the two off-diagonal blocks, because
each original row and column already has \(r\) copies and
needs \(\lambda\). Of its total \(\lambda n\) occurrences,
this leaves \(\lambda\delta-r\mu\) for the lower-right
\(\delta\times\delta\) block. Simplicity implies that this
is at most \(\delta^2\), so
\[
 0\le\delta^2-\lambda\delta+r\mu
     =(\delta-r)(\delta-\mu).
 \tag{1}
\]
As \(\delta\ge\mu\), the only possibilities are \(\delta=\mu\)
or \(\delta\ge r\). The former is the all-symbol extension at
\(n=\lambda\).

For sufficiency in the latter case, let
\(\delta\ge\max(r,\mu)\). Complete the top-left block by
adding, in cell \((i,j)\) with \(0\le i,j<r\), the \(\mu\)
new symbols
\[
  \{\,\mu(i+j)+k\bmod\delta:\ 0\le k<\mu\,\}
 \tag{2}
\]
in a separate alphabet \(\mathbb Z/\delta\mathbb Z\).
No cell has repetitions since \(\mu\le\delta\), and the
case \(\mu=0\) just adds nothing. For a fixed row, the displayed
labels across columns are the residues of a consecutive interval
of length \(\mu r\); the same holds in a fixed column. Every
new symbol therefore occurs either \(\lfloor\mu r/\delta\rfloor\)
or \(\lceil\mu r/\delta\rceil\) times in that row or column.
The upper count is at most \(r\le\lambda\). The lower count
is at least \(\lambda-\delta\), because (1) is equivalent to
\(\mu r/\delta\ge\lambda-\delta\) and the right side is integral.
Old symbols have row and column count \(r\ge\lambda-\delta\)
since \(\mu\le\delta\).

To finish, apply Bahmanian's
[Corollary 4.2, printed p. 5545](https://d-nb.info/1387819259/34#page=11):
for a filled simple \(r\times r\) \(\lambda\)-Latin block
on the \(n\) symbols, require \(\lambda\le n\), row and
column counts of each symbol at least \(\lambda+r-n\), and
total block counts between \(\lambda(2r-n)\) and
\(\lambda(2r-n)+(n-r)^2\). The row and column conditions and
\(\lambda\le n\) were just verified. The lower total bound
is nonpositive since \(\delta\ge r\). The upper total bound
is at least \(r^2\) by (1), and no symbol can occur more than
\(r^2\) times in a simple block. All assumptions hold, so
(2) extends at order \(n\). This completes the second spectrum.

## 5. Scope, prior work, and reproduction

At a **strictly larger** order, the filled cyclic square
excludes every \(r<n<2r\) when \(\lambda\le r\) and Corollary
4.4 gives order \(2r\). If \(n=r\) counts, Problem 5.2 in
the version of record has affirmative witnesses precisely
when \(\lambda<r\) outside the two small exceptional pairs.
At \(\lambda=r\) it has none. In the wider arXiv version
there are also no such witnesses when \(\lambda>r\), because
\(n=\lambda<r+\max\{r,\lambda\}\).

The ordinary (\(\lambda=1\)) Evans–Stein proper-order
sharpness is classical; see the cases in
[Jared Howell, *Constructions of mutually orthogonal Latin
squares*, proof of Theorem 1.5, printed pp. 11–12](https://dspace.library.uvic.ca/server/api/core/bitstreams/b7398c71-3b70-48e0-9825-c1b48bc1c2d8/content).
The ordinary two-hole obstruction for \(r\ge4\) is likewise
classical, and we make no priority claim for it. The new result
here is the simultaneous sharp embedding-order classification
for the multi-symbol version, including the two-vacant-slot
generalization of that obstruction. We use the stated
Bahmanian and Ryser results for positive embeddings and do not
claim those bounds as new. Searches to 27 November 2026 used
the DOI and arXiv id, “Problem 5.2”, the author name, multi-Latin
square sharpness, and Evans–Stein embedding bounds. No identical
multi-symbol classification was located in the primary sources
examined. This is not an absolute priority assertion.

Both proof statements above are analytic. The reproducibility
checks need only Python 3.10+:
```sh
python3 verify_construction.py
python3 verify_small_orders.py
```
