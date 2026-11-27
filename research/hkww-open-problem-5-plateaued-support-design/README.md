# Exactly when the canonical plateaued extension of the HKWW support design works

Let \(f\) be \(r\)-plateaued in \(m\) binary variables, with \(1\le r<m\).
The canonical maximal proper weight class of affine cuts on \(f^{-1}(1)\)
from nonzero Walsh coefficients gives a nontrivial 2-design **if and
only if** \(r=1\) and the Walsh support is a hyperplane coset not
containing 0. The resulting design is the complement of the addition
design of a bent function on \(m-1\) variables; in particular the
extension does not create any genuinely new nontrivial design of this
form. The other proper weight classes are classified below as well.

## 1. Which extension?

[Hyun–Kwon–Wang–Wu, arXiv:2605.24355v1, §VI-B, Theorem 6
(p. 13), Open Problem 5 (p. 14)](https://arxiv.org/pdf/2605.24355v1#page=13)
ask whether their bent construction extends to \(r\)-plateaued
functions. In Theorem 6 the points are \(D=f^{-1}(1)\); for each
nonzero frequency \(a\), use the affine cut \(a\cdot x+f^*(a)=1\)
on \(D\), with \(f^*(a)\) given by the sign of the Walsh coefficient.
At positive plateau order there is no sign for a zero coefficient.
Here we classify the direct extension that uses exactly all
nonzero frequencies with nonzero Walsh coefficient and takes the
same sign rule there. We also classify what happens if instead one
takes all cuts of either other proper weight. We do not rule out
arbitrary choices of subsets of cuts or constructions on a changed
point set.

For \(V=\mathbb F_2^m\), set \(N=2^m\),
\(u=2^{(m-r)/2}\), \(A=N/u\), \(W_f(a)=\sum_x(-1)^{f(x)+a\cdot x}\),
\(S=\{a:W_f(a)\ne0\}\), \(v=|D|=(N-W_f(0))/2\).
By plateauedness \(W_f(a)\in\{0,\pm A\}\); Parseval gives
\(|S|=u^2=N/2^r\). Since \(r<m\), \(m-r\) is at least 2 and even,
and \(u\ge2\). For \(a\in S\), let \(c_a\in\mathbb F_2\) satisfy
\(W_f(a)=A(-1)^{c_a}\).
For every \(a\ne0\), summing \((-1)^{a\cdot x}\) over \(D\) gives
\(-W_f(a)/2\), so the three indexed affine-cut families are:
\[
\begin{array}{c|l|c}
\text{family}&\text{parameters }(a,c)\text{ for the cut }a\cdot x+c=1&
     \text{size of each block}\\
+&a\in S\setminus\{0\},\ c=c_a&v/2+A/4\\
-&a\in S\setminus\{0\},\ c=c_a+1&v/2-A/4\\
0&a\notin S,\ a\ne0,\ c=0,1&v/2.
\end{array}
\]
These are all the possible proper nonempty weights of affine
restrictions to \(D\). We use a *nontrivial* 2-design to mean
\(2\le k<v\), with \(\lambda>0\). Whenever the block weight is
proper, passing between indexed cuts and the distinct blocks of the
same weight preserves the 2-design property: the parameter map
\((a,c)\mapsto(a\cdot x+c)_{x\in D}\) is linear and all its nonempty
fibres have the same size. The two constant cuts are not in a
proper weight class. Hence all multiplicities divide out at once;
this covers the distinct codewords of the punctured affine code,
not just a list of parameters.

## 2. One Fourier criterion for all three classes

Let \(H(t)=\sum_{a\in S}(-1)^{a\cdot t}\) and
\(\delta={\bf1}_{0\in S}\). For each \(p\in D\), Fourier
inversion gives
\[
 \sum_{a\in S\setminus\{0\}}
        (-1)^{a\cdot p+c_a}=-N/A-\delta(-1)^{c_0},
\]
with the last term taken as zero if \(0\notin S\).
In particular point replication is constant in either signed family,
since a block indicator equals \((1-(-1)^{a\cdot p+c})/2\).
In the zero family, the two signs for each \(a\) give constant
replication immediately.

For distinct \(p,q\in D\), putting \(t=p+q\), the products of the
two sign evaluations sum to \(H(t)-\delta\) in either signed family.
In the zero family they sum to
\(2[-H(t)-(1-\delta)]\), since the full character sum vanishes
when \(t\ne0\). Expanding the two block indicators shows that each
family has constant pair multiplicity if and only if
\[
              H(t)\text{ is constant on }(D+D)\setminus\{0\}.
              \tag{1}
\]
One can apply this even when a family only gives singleton or full
blocks. The condition needed for a *nontrivial* design also
requires its block size to be proper and at least 2.

## 3. Complete classification of the plus family

Suppose that the plus family is a nontrivial 2-design. Its number
of indexed blocks is \(|S|-\delta\); Fisher's inequality gives
\(|S|-\delta\ge v\). This bound also holds with indexed repeated
blocks since the real point Gram matrix is
\((R-\lambda)I+\lambda J\) and is nonsingular when \(k<v\):
\(R(k-1)=\lambda(v-1)\) and \(\lambda>0\).

* If \(W_f(0)=-A\), then \(v>N/2\), while \(|S|\le N/2\).
  This is impossible.
* If \(W_f(0)=0\), then \(v=N/2\); necessarily \(r=1\).
* If \(W_f(0)=A\), then \(v=N(1-1/u)/2\). When \(u=2\) the plus
  blocks are all of size \(v\), outside the nontrivial case.
  When \(u\ge4\), \(v>N/4\); again \(r=1\) is necessary. In this case
  \(N=2u^2\), \(v=u(u-1)\), the block size is \(u^2/2\), and
  the indexed block count is \(u^2-1\). Double counting point pairs
  gives
  \[
    \lambda=\frac{u(u+1)(u^2-2)}{4(u^2-u-1)}
       =\frac{u(u+2)}4+\frac{u^2}{4(u^2-u-1)} .
  \]
  The first summand is integral, and the second is strictly between
  0 and 1 when \(u\ge4\); this is impossible. A simple design would
  imply an indexed design too, so repetitions cannot avoid this
  obstruction.

It remains to consider \(r=1\) with \(W_f(0)=0\), so \(v=|S|=N/2\)
and \(k_+=u(u+1)/2\) is nontrivial. A *period* \(t\ne0\) of \(f\)
would give \(a\cdot t=0\) for every \(a\in S\) by transforming the
periodicity identity. Then \(p,p+t\in D\) would have identical
incidence columns, impossible in a nontrivial 2-design since it
would imply \(R=\lambda\). Thus no nonzero period exists.

A nonzero difference \(t\) is missing from \(D+D\) exactly when
\(D+t\) is disjoint from \(D\). Since \(D\) has size \(N/2\),
this happens exactly when \(D+t=V\setminus D\), i.e.
\(f(x+t)=f(x)+1\) everywhere (an *anti-period*). The sum of two
distinct anti-periods would be a nonzero period, so there is at
most one. If none exists, (1) would make \(H(t)\) constant on all
nonzero directions. Fourier inversion would make \({\bf1}_S\)
constant on all nonzero frequencies, contrary to \(0\notin S\)
and \(|S|=N/2\) with \(N\ge8\). Thus there is exactly one
anti-period \(t_0\).

Transforming the anti-period identity gives \(a\cdot t_0=1\)
for every \(a\in S\). Since \(|S|=N/2\), precisely
\[
                   S=\{a:a\cdot t_0=1\}.
\]
Conversely, if \(S\) equals this hyperplane coset, it excludes 0
and has size \(N/2\), hence \(r=1\) and \(f\) is balanced. Fourier
inversion gives the anti-period identity and \(H(t)=0\) for
\(t\notin\{0,t_0\}\); no pair in \(D\) has difference \(t_0\).
Now (1) proves the plus blocks form a nontrivial 2-design.

## 4. Exact design in the surviving case; other weights

Choose linear coordinates \((x,b)\in\mathbb F_2^{m-1}\times\mathbb F_2\)
on the point space with \(t_0=(0,1)\), and the dual coordinates
on frequencies, so the dot pairing is unchanged. Write
\(f(x,b)=F(x)+b\) by the anti-period identity. Direct summation
in \(b\) gives \(W_f(a,1)=2W_F(a)\), \(W_f(a,0)=0\). Thus \(F\)
is bent, and the points of \(D\) are \((x,1+F(x))\). The plus
blocks in these coordinates have indicators
\[
                   a\cdot x+F^*(a)+1+F(x),
                   \qquad a\in\mathbb F_2^{m-1}.
\]
They are the complements of the usual addition-design blocks of
\(F\), as claimed. The parameters are
\(2-(u^2,u(u+1)/2,u(u+2)/4)\). Indeed the indexed block count
is \(v=u^2\); from (1), replication is \(k_+\) and double
counting gives \(\lambda=k_+(k_+-1)/(u^2-1)=u(u+2)/4\).
The design is symmetric, not a two-distinct-intersection-size
analogue of the non-symmetric quasi-symmetric examples.
Its binary rank is \(m+1\): subtract the row indexed by \(a=0\)
from every other row. The resulting affine rows span all
first-order affine forms in \(x\); otherwise some nonzero
functional would annihilate all \((a,F^*(a)+F^*(0))\), forcing
either all \(a\) in a hyperplane or \(F^*\) affine. The latter
is impossible: character inversion from the constant-magnitude
Walsh formula implies \(F^*\) is bent. The remaining row is
non-affine, so adds one to the \(m\)-dimensional affine-form
space. Ranks here concern the actual incidence matrices.

The minus blocks are pointwise complements of the plus blocks,
hence share condition (1); in this surviving case they are
the addition design of \(F\) with the smaller block size. They
are singleton blocks when \(u=2\). The zero family here is
the ordinary affine hyperplane design on \(\mathbb F_2^{m-1}\):
the zero frequencies in the chosen coordinates are \((a,0)\),
so restrictions are exactly the affine cuts \(a\cdot x+c\).
It is simple, of block count \(2(v-1)\) and parameters
\(2-(v,v/2,v/2-1)\).

The only extra way for the zero family to satisfy (1) is
\(u=2,W_f(0)=A\), when plus blocks are full and minus blocks
empty. In fact \(|D|=N/4\), \(0\in S\), and each of the other
three \(a\in S\) has character sum on \(D\) of absolute value
\(A/2=|D|\). Each character is therefore constant on \(D\).
Their span has dimension at least two because they are distinct;
the simultaneous affine constraints permit \(N/4\) points, so
the dimension is at most two. Thus \(D\) is an affine
codimension-two subspace and \(S\) is its annihilator of directions.
The zero family gives all affine hyperplanes of \(D\), with
constant multiplicity before deduplication. This is nontrivial
only when \(\dim D\ge2\).
These cases exhaust positive \(r<m\): outside that full-plus
exception the plus block size is at least 2 and below \(v\);
constant pair multiplicity at that size forces positive
\(\lambda\) by counting pairs inside blocks. Hence (1) would
give a nontrivial plus design, covered by §3.

## 5. Attribution and verification

The proof treats the weight-class interpretation of Theorem 6 and
its Proposition 5 directly. Their Remark 5 uses a related character
sum for weight classes on the **full** point space \(V\), not on
\(D=f^{-1}(1)\). The distinction matters: requirement (1) need
only hold on the occurring differences. The equivalence between
affine Walsh support and classical partially bent functions is
background due to [Hodžić, Pašalić, Wei, and Zhang (2019)](https://doi.org/10.1109/TIT.2019.2909910);
the new result here is that the indicated nontrivial support-design
property forces that particular balanced codimension-one case.
Searches through 27 November 2026 used the title, arXiv number,
authors, Open Problem 5, support-restricted affine weight design,
three Walsh values, and quasi-symmetric support designs. No
same-scope answer was found in the primary sources located; this
is not an unconditional priority claim.

No catalogue or computation is needed for the proof. Two
supplementary checks can be run with Python 3.10+:
```sh
python3 verify_exhaustive.py
python3 verify_families.py
```
