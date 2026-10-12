# Independent-arity simplex recursions: a unique asymptotic maximizer

**Research note (entry 005 continuation), 7 October 2026.**
Prepared with AI assistance. This is a written mathematical proof with a
replayable exact-rational finite certificate, not an external referee report or
a Lean formalization. No literature-wide novelty or priority claim is made.

## 1. Setting and theorem

For a full-dimensional convex body \(K\subset\mathbb R^d\), let \(\Pi K\)
be its projection body and put
\[
R(K)=\frac{|\Pi K|}{|K|^{d-1}},\quad
g(d)=\frac{d^d}{d!},\quad
c_d=(d+1)g(d).
\]
Products are Cartesian products in independent coordinate spaces and joins
are affine joins (so \(\dim(A*B)=\dim A+\dim B+1\)).
The auxiliary affine invariant \(a(K)>0\) and its complete geometric
definition are in [005 v2](../../preprints/005-simplex-product-optimum/v2/paper.md),
Section 2. We use its proved product/join calculus, restated and applied below.

Given **independent positive integers** \(m,k,p\), start with a
\(p\)-simplex \(K_0=T_p\) and set
\[
K_{j+1}=(K_j^m)^{*k}.
\]
Write
\[
\Lambda_{m,k,p}=\lim_{j\to\infty}R(K_j)^{1/\dim K_j}.
\]

**Theorem (independent-arity unique optimum).** The limit exists for all
positive integers \(m,k,p\). Its unique maximum throughout this
three-parameter family occurs at \((m,k,p)=(2,2,5)\). More precisely,
\[
\boxed{
 (m,k,p)\ne(2,2,5)
 \Longrightarrow
 \log\Lambda_{m,k,p}<\frac{131}{125}
 <\log\frac{14267}{5000}
 <\log\Lambda_{2,2,5}.
}
\]
Thus equality cannot occur at any other seed or pair of arities.

The strict last comparison imports the exact integer witness already
published in [005 v5](../../preprints/005-simplex-product-optimum/v5/paper.md),
Section 9 and its
[checker](../../preprints/005-simplex-product-optimum/v5/code/check_balanced.py).
Everything required to exclude *independent* arities is proved here.

## 2. Exact recurrence and limiting series

The 005 v2 identities give
\[
R(A\times B)=R(A)R(B),\quad
a(A\times B)=\frac{r a(A)+s a(B)}{r+s}
\]
for \(\dim A=r\), \(\dim B=s\), and
\[
R(A*B)=\frac{g(r+s+1)}{g(r)g(s)}
       R(A)R(B)(a(A)+a(B)),\quad
a(A*B)=\frac{a(A)a(B)}{a(A)+a(B)}.
\]
In particular, the self-join of \(k\) copies of a \(b\)-dimensional
body \(P\) satisfies
\[
R(P^{*k})=
k\,a(P)^{k-1}\frac{g(k(b+1)-1)}{g(b)^k}R(P)^k,
\quad a(P^{*k})=a(P)/k.
\]
This follows by induction from the binary identities.

For \(m,k\ge2\), set
\[
T=mk,\qquad c=\frac{k-1}{T-1},\qquad
d_j=\dim K_j,\qquad R_j=R(K_j),\qquad a_j=a(K_j).
\]
Since \(R(T_p)=c_p\) and \(a(T_p)=1/(p+1)\), the identities give
\[
\begin{split}
d_{j+1}&=Td_j+k-1,&d_j+c&=(p+c)T^j,\\
a_{j+1}&=a_j/k,&a_j&=\frac1{(p+1)k^j},\\
R_{j+1}&=R_j^T D_j,&
D_j&=k\,a_j^{k-1}\frac{g(d_{j+1})}{g(md_j)^k}.
\end{split}\tag{2.1}
\]

Robbins' inequalities, for every integer \(n\ge1\), are
\[
n-\tfrac12\log(2\pi n)-\frac1{12n}
<\log g(n)
<n-\tfrac12\log(2\pi n)-\frac1{12n+1}.
\tag{2.2}
\]
They imply \(\log D_j=qj+O_{m,k,p}(1)\) with
\(q=\tfrac{k-1}{2}\log(m/k)\): expand (2.2) at
\(n=md_j\) and \(n=Td_j+k-1\), note that
\(\log d_j=j\log T+O_{m,k,p}(1)\), and use the formula for \(a_j\).
Consequently \(\sum_j T^{-j-1}\log D_j\) converges absolutely, and
\[
\boxed{
\log\Lambda_{m,k,p}
=\frac{A_p+\sum_{j\ge0}T^{-j-1}\log D_j}{p+c},
\qquad A_p=\log c_p.
}\tag{2.3}
\]
This establishes existence in the nondegenerate case.

For \(m=1,k\ge2\), each join of simplices remains a simplex of dimension
\(k^j(p+1)-1\). Stirling gives \(\log\Lambda_{1,k,p}=1\).
For \(k=1\), iterated Cartesian powers give
\(\log\Lambda_{m,1,p}=A_p/p\). Both cases will fall strictly below the
claimed winner by the universal gap established below.

## 3. Universal majorant

For \(m,k\ge2\), define
\[
\begin{split}
B_{m,k,p}
  &=1+\tfrac12\log(2\pi m(p+c))-\log(p+1),\\
C_{m,k,p}
  &=\tfrac12\log k+(k-1)B_{m,k,p}
     +\frac{k}{12mp},\\
q_{m,k}&=\frac{k-1}{2}\log\frac mk .
\end{split}
\tag{3.1}
\]
Here \(C\) is a *logarithmic* constant, not a multiplicative factor.

**Lemma 3.1.** For all \(j\ge0\),
\[
\log D_j<C_{m,k,p}+q_{m,k}j.
\tag{3.2}
\]

**Proof.** Put \(n=Td_j+k-1\). Applying the upper bound
\(g(n)<e^n/\sqrt{2\pi n}\), and the lower bound
\(g(md_j)>e^{md_j}(2\pi md_j)^{-1/2}e^{-1/(12md_j)}\),
gives
\[
D_j<
\sqrt{k}\,\left[e\sqrt{2\pi m}\,
a_j\sqrt{d_j}\right]^{k-1}
 e^{k/(12md_j)}.
\]
Indeed \(n>Td_j\) gives the factor \(1/\sqrt{mk}\)
when bounding \((md_j)^{k/2}/\sqrt n\).
Using (2.1),
\[
a_j\sqrt{d_j}<
\frac{\sqrt{p+c}}{p+1}\left(\sqrt{\frac mk}\right)^j,
\quad d_j\ge p,
\]
so taking logarithms proves (3.2). \(\square\)

The geometric sums
\[
\sum_{j\ge0}T^{-j-1}=\frac1{T-1},
\qquad
\sum_{j\ge0}jT^{-j-1}=\frac1{(T-1)^2}
\]
give the strict bound
\[
\log\Lambda_{m,k,p}
<U_{m,k,p}:=
\frac{A_p+C_{m,k,p}/(T-1)+q_{m,k}/(T-1)^2}{p+c}.
\tag{3.3}
\]
For any nonnegative integer \(J\), an exact restart instead gives
\[
\log\Lambda_{m,k,p}<
\frac{A_p+
 \sum_{j=0}^{J-1}\frac{\log D_j}{T^{j+1}}+
 \frac1{T^J}\left(
  \frac{C_{m,k,p}+Jq_{m,k}}{T-1}
  +\frac{q_{m,k}}{(T-1)^2}
 \right)}{p+c}.
\tag{3.4}
\]
The exact checker bounds all logarithms in these expressions from the
correct side; it does not calculate an approximate limit and compare it
to a threshold.

Set \(L=131/125\), \(\delta_p=Lp-A_p\), and
\[
h_{m,k,p}=-\frac6{125}
 +\tfrac12\log(2\pi m(p+c))-\log(p+1).
\]
An algebraic rearrangement of (3.3) shows that \(U_{m,k,p}<L\)
is **equivalent** to
\[
\delta_p>
c h_{m,k,p}+E_{m,k,p},\quad
E_{m,k,p}=
\frac{\log k}{2(T-1)}
+\frac{k}{12mp(T-1)}
+\frac{c}{2(T-1)}\log\frac mk .
\tag{3.5}
\]

## 4. The uniform simplex gap

**Lemma 4.1.** For every integer \(p\ge1\),
\(\delta_p>3/20\). For \(p\ge32\), the stronger
\(\delta_p>2/3\) holds.

**Proof.** The checker uses exact rational logarithm intervals for
\(1\le p\le31\) and certifies \(\delta_p>3/20\) for each.
For \(p\ge32\), (2.2) gives
\[
\delta_p>
\phi(p):=\frac6{125}p-\log(p+1)
+\frac12\log(2\pi p)+\frac1{12p+1}.
\]
For all real \(p\ge32\),
\[
\phi'(p)\ge\frac6{125}-\frac1{33}
-\frac{12}{385^2}>0.
\]
The rational interval checker certifies \(\phi(32)>2/3\),
which simultaneously establishes the two statements. \(\square\)

In particular \(A_p/p<L\) for every \(p\ge1\), settling \(k=1\).
The pure-join case is settled by \(1<L\).

## 5. Three infinite parameter tails

We now reduce the infinitely many triples to the finite core
\[
2\le m,k\le31,\qquad 1\le p\le31.
\tag{5.1}
\]

**Lemma 5.1 (large product arity).** If \(m\ge32\),
\(k\ge2\) and \(p\ge1\), then \(U_{m,k,p}<L\).

**Proof.** Because \(0<c<1/m\) and \(p+c\le p+1\),
\[
h_{m,k,p}\le\tfrac12\log(\pi m)-\tfrac6{125}.
\]
For \(k\ge2\), elementary calculus gives
\(\log k\le k/2\). The potentially positive last term of
\(E_{m,k,p}\) can occur only when \(k<m\), and satisfies
\[
E_{m,k,p}\le
\frac1{4(m-1/2)}
+\frac1{12m(m-1/2)}
+\frac{\log m}{2m(2m-1)}.
\tag{5.2}
\]
The functions on the right and
\((\tfrac12\log(\pi m)-6/125)/m\) are decreasing for \(m\ge32\).
Their sum at \(m=32\), with rational log bounds, is strictly less than
\(3/20\). Thus
\(c h+E<3/20<\delta_p\); apply (3.5). \(\square\)

**Lemma 5.2 (large seed dimension).** For
\(2\le m\le31\), \(k\ge2\) and \(p\ge32\),
\(U_{m,k,p}<L\).

**Proof.** By \(c\le1/m\le1/2\) and \(p+c\le p+1\),
\[
h_{m,k,p}
\le\frac12\log\left(\frac{2\pi m}{p+1}\right)
-\frac6{125}
\le\frac12\log\left(\frac{62\pi}{33}\right)
-\frac6{125}<\frac{17}{20}.
\]
The logarithmic bound is rational-interval certified. The three
terms of \(E\) satisfy
\[
E_{m,k,p}<
\frac16+\frac1{1152}+\frac1{25}.
\]
Indeed the first follows from \(\log k\le k/2\),
the second from \(m\ge2,p\ge32\), and the third is nonpositive
for \(m=2\); for \(m\ge3\), it is at most
\(\log m/[2m(2m-1)]\le\log3/30<1/25\).
The last monotonicity follows from \(\log m\ge1\) for \(m\ge3\).
Therefore
\[
ch+E<
\frac{17}{40}+\frac16+\frac1{1152}+\frac1{25}
<\frac23<\delta_p,
\]
as required. \(\square\)

**Lemma 5.3 (large join arity, regular regime).**
For \(2\le m\le31\), \(1\le p\le31\), \(k\ge32\),
with either \(m\ge3\) or \(p\ge8\), one has
\(U_{m,k,p}<L\).

**Proof.** Here \(k>m\), so the final term of \(E\)
in (3.5) is nonpositive. Define
\[
H_{m,p}=-\frac6{125}
+\frac12\log(2\pi m(p+1/m))-\log(p+1).
\]
Since \(c<1/m\) and \(h\le H\),
\[
c h+E\le
\frac{\max\{0,H_{m,p}\}}m
+\frac{\log32/64+1/(12mp)}{m-1/32}.
\tag{5.3}
\]
We used \(\log k/k\le\log32/32\) for \(k\ge32\).
All \(29\cdot31+24=923\) inequalities asserting that the right side
of (5.3) is strictly below \(\delta_p\) are checked with exact
rational intervals. No integer \(k\ge32\) is omitted. \(\square\)

**Lemma 5.4 (large join arity, seven exceptional seeds).**
For \(m=2\), \(1\le p\le7\), and \(k\ge32\),
\(\log\Lambda_{2,k,p}<L\).

**Proof.** The bound (3.3) is too weak for some of these
parameters, so restart at \(J=1\). Put
\[
\begin{split}
E_p&=2p+1-\log(p+1)-\log g(2p),\\
B_p&=1+\tfrac12\log(4\pi(p+1/2))-\log(p+1).
\end{split}
\]
With \(n=k(2p+1)-1\), the upper inequality
\(\log g(n)<n-\tfrac12\log(2\pi n)\) gives
\[
\log D_0<
kE_p+\log(k(p+1))-1-\tfrac12\log(2\pi n).
\tag{5.4}
\]
For \(k\ge32\), the inequality
\(n\ge k(2p+1/2)\) and the certified seven inequalities
\[
\log(p+1)-1-\tfrac12\log(2\pi(2p+1/2))<0
\]
reduce (5.4) to
\[
\frac{\log D_0}{2k}
<\frac{E_p}{2}+\frac{\log k}{4k}.
\tag{5.5}
\]
Moreover \(q_{2,k}\le0\),
\(C_{2,k,p}\le\tfrac12\log k+(k-1)B_p+k/(24p)\),
and \(B_p>0\) for the seven displayed values of \(p\).
Dropping the nonpositive \(q\)-tail in (3.4) now gives the
uniform upper numerator
\[
A_p+\frac{E_p}2+\frac{\log32}{128}
+\frac{B_p+1/(24p)+\log32/64}{126}.
\tag{5.6}
\]
Finally \(c=(k-1)/(2k-1)\ge31/63\). The checker
certifies, for each \(1\le p\le7\), that (5.6) is strictly
less than \(L(p+31/63)\). \(\square\)

## 6. The finite core and endpoint

**Lemma 6.1 (finite exclusions).** Every triple in (5.1) except
\((2,2,5)\) satisfies \(\log\Lambda_{m,k,p}<L\).

**Proof.** For all triples with \(m\ge3\), or with \(m=2\)
and \(p\ge8\), apply (3.3) and check
\[
A_p+\frac{C}{T-1}+\frac{q}{(T-1)^2}<L(p+c).
\]
There are exactly \(27,690\) such comparisons.
For \(m=2,p\le7\), apply the three-level restart (3.4) with
\(J=3\); all \(209\) comparisons away from
\((2,2,5)\) are strict. Each \(d_j\) is an explicit integer
and each logarithm is enclosed by a rational interval as described
in Section 7. The exhaustive loop ranges and counts are in
[check.py](check.py). \(\square\)

The inherited [v5 endpoint checker](../../preprints/005-simplex-product-optimum/v5/code/check_balanced.py)
reconstructs the level-six exact rational \(R_6\) for
\((m,k,p)=(2,2,5)\), proves \(d_6=21845\), and verifies
\[
\left(\frac{14267}{5000}\right)^{65536}<3R_6^3.
\]
Its written Lemma in v5 Section 9 proves every later multiplier
\(D_j>3\), hence
\(\Lambda_{2,2,5}>(3R_6^3)^{1/65536}>14267/5000\).
The checker here independently encloses
\(\log(14267/5000)>131/125\).
Together with Lemmas 4.1 and 5.1--6.1, this completes the
theorem. \(\blacksquare\)

## 7. Exact certificate semantics and reproduction

The file [check.py](check.py) is standard-library Python and contains
no floating-point comparisons or disabled assertions. Its correctness
reductions are the displayed analytic inequalities in Sections 2--6,
not an assumption that finitely many experiments prove the infinite
theorem.

* The identity \(\pi=16\arctan(1/5)-4\arctan(1/239)\)
  follows from the tangent addition formula and the principal
  argument. The checker encloses both arctangents by 16 terms of the
  alternating rational Taylor series, including a signed rational
  remainder.
* For each positive rational \(x\), factor out powers of two and use
  \(\log y=2\operatorname{artanh}((y-1)/(y+1))\),
  \(1\le y<2\). Eighteen rational terms enclose the result; the
  omitted positive tail is at most
  \(2z^{37}/(37(1-z^2))\). The same method bounds \(\log2\).
* For \(1\le n\le20\), \(g(n)=n^n/n!\) is formed exactly
  using integer factorials and its log bounded by the preceding rule.
  For \(n\ge21\), the two-sided Robbins bounds (2.2) give explicit
  rational-log intervals. Each signed coefficient in (3.3)--(3.4)
  is evaluated using the correct interval endpoint.
* The finite loop covers \(2\le m,k\le31\), \(1\le p\le31\)
  and omits exactly the known winner. The other branches certify the
  global \(m,p,k\) tails with explicit monotonicity reductions; hence
  their union covers **all** independent positive arities and seeds.

From the repository root run:

```sh
python3 notes/independent-arity-simplex-recursions/check.py
python3 -O notes/independent-arity-simplex-recursions/check.py
python3 preprints/005-simplex-product-optimum/v5/code/check_balanced.py
python3 -O preprints/005-simplex-product-optimum/v5/code/check_balanced.py
```

The two modes must produce identical logs for each checker.
The main checker prints the numbers of strict comparisons it actually
performs and raises a runtime error on the first failed inequality.

## 8. Dependence, scope and attribution

The geometric projection-body identities and the initial binary
construction are *inherited* from public entry 005 v2, which itself
acknowledges [OpenAI/math family 088](https://github.com/openai/math)
and earlier geometric inequalities. The previous equal-arity
classification \(m=k\) is the published entry 005 v5 theorem.
The additional result here is the full independent-arity
\((m,k,p)\)-classification and its all-parameter exact certificate.

This result does **not** classify arbitrary nonhomogeneous product/join
trees, periodic changes of arity, or the unrestricted optimal
projection-volume growth rate. The separate mixed Bellman ceiling in
the repository concerns a strictly larger closure class, so there is
no equality claim for that ceiling.

No external peer review, Lean formalization of the whole theorem,
literature-wide originality certification, or optimization over arbitrary
operation trees is asserted.
