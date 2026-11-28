# Proof

## 1. From support advice to usable exponent chains

Construct
\[
 E=\prod_{\substack{r\in\mathcal S\\r\le N}}
      r^{\lfloor\log_rN\rfloor}. \tag{2}
\]
Every prime power dividing \(\lambda(N)\) is at most \(N\), so
\[
 \lambda(N)\mid E,\qquad
 \log E\le|\mathcal S|\log N. \tag{3}
\]
The complete factorization of \(E\) is known by construction. Entries
of \(\mathcal S\) that divide \(N\) are tried by exact division first.
If one is \(p\) or \(q\), the factorization is already complete. We may
therefore assume \(p,q\notin\mathcal S\).

For an ordinary base \(u\), the algorithm first uses
\[
 \gcd(N,u^{\lceil\log_2N\rceil}) \tag{4}
\]
to saturate any prime-power component dividing \(u\). On blocks coprime
to \(u\), it computes
\[
 \gcd(u^{E/r^j}-1,N),
 \qquad r\in\mathcal S,\quad0\le j\le v_r(E). \tag{5}
\]
These chains distinguish unequal \(r\)-adic components of local
multiplicative orders.

## 2. The coprime cofactor coordinates

Put
\[
 g=\gcd(p-1,q-1),\qquad
 A=\frac{p-1}{g},\qquad B=\frac{q-1}{g}. \tag{6}
\]
Then
\[
 \gcd(A,B)=1,\qquad
 N=ABg^2+(A+B)g+1. \tag{7}
\]
The algorithm does not know \(g,A,B\); they are used only for the
correctness dichotomy.

Choose a real parameter \(y>e\). Write
\[
 L=\log N,\qquad s=\log y,\qquad
 T=\exp\!\left(\frac{L\log L}{s}\right). \tag{8}
\]

## 3. Large coordinate: subgroup escape

Consider an endpoint
\[
 h=Cg+1\in\{p,q\},\qquad C\in\{A,B\},
\]
and suppose \(C>T\). Put \(x=h-1=Cg\). In
\(\mathbb F_h^\times\), the subgroup
\[
 H=\{z:z^g=1\} \tag{9}
\]
has exactly \(g=x/C\) elements.

If \(y\ge x\), scanning all ordinary bases through \(y\) trivially
finds a residue outside the proper subgroup \(H\). Suppose \(y<x\).
The Konyagin--Pomerance bound gives
\[
 \Psi(x,y)>x^{\,1-\log\log x/\log y}. \tag{10}
\]
Since \(x<N\),
\[
 x^{\log\log x/\log y}
 \le
 \exp\!\left(\frac{L\log L}{s}\right)=T<C. \tag{11}
\]
Thus
\[
 \Psi(x,y)>x/C=g. \tag{12}
\]
If every prime \(\ell\le y\) lay in \(H\), then every \(y\)-smooth
integer at most \(x<h\) would give a distinct element of \(H\), contrary
to (12). Hence some prime \(\ell\le y\) satisfies
\[
 \ell^g\not\equiv1\pmod h. \tag{13}
\]

If \(\ell\) is the other prime factor, saturation (4) splits \(N\).
Otherwise \(\operatorname{ord}_h(\ell)\nmid g\). Some
\(r\mid C\) therefore satisfies
\[
 v_r(\operatorname{ord}_h(\ell))>v_r(g). \tag{14}
\]
Because the two coordinates \(A,B\) are coprime, the other endpoint
\(h'=C'g+1\) has
\[
 v_r(h'-1)=v_r(g),
\]
and hence
\[
 v_r(\operatorname{ord}_{h'}(\ell))\le v_r(g). \tag{15}
\]
The prime \(r\) divides \(\lambda(N)\), so \(r\in\mathcal S\), and one
of the known chains (5) detects (14)--(15). Scanning all bases through
\(y\) therefore factors \(N\) whenever \(\max(A,B)>T\).

## 4. Small coordinates: exact reconstruction

It remains to treat
\[
 A\le T,\qquad B\le T. \tag{16}
\]
Enumerate ordered positive integer pairs \((a,b)\) with
\(a,b\le\lceil T\rceil\). For each pair form
\[
 \Delta_{a,b}=(a+b)^2+4ab(N-1). \tag{17}
\]
If \(\Delta_{a,b}=d^2\) and
\[
 t=\frac{d-a-b}{2ab} \tag{18}
\]
is a positive integer, verify
\[
 (at+1)(bt+1)=N. \tag{19}
\]
For the true pair \((A,B)\), equations (7) and (17) give
\[
 \Delta_{A,B}=(2ABg+A+B)^2,
\]
so (18) returns \(t=g\), and (19) recovers \(p,q\).
This branch uses \(O(T^2)\) candidates and polynomial work per candidate.

## 5. Optimizing the two exits

Take
\[
 s=\sqrt{2L\log L},\qquad y=\lceil e^s\rceil. \tag{20}
\]
Then
\[
 \log y=(1+o(1))\sqrt{2L\log L},
\]
while
\[
 2\log T
 =\frac{2L\log L}{s}
 =\sqrt{2L\log L}. \tag{21}
\]
The base-scan branch costs \(y\) times polynomial overhead, and the
coefficient branch costs \(T^2\) times polynomial overhead. Equations
(20)--(21) make both
\[
 \exp\!\left((\sqrt2+o(1))
       \sqrt{\log N\,\log\log N}\right). \tag{22}
\]
The logarithms and safe integer ceilings in (8) and (20) can be computed
to sufficient precision in polynomial time. Finitely many small \(N\)
are absorbed into direct trial division. This proves the theorem.

## 6. Finite verifier

The checker independently:

* constructs exact support advice and the exponent (2);
* verifies the coprime-coordinate identity (7) and its discriminant;
* recovers every tested semiprime by coefficient enumeration;
* computes exact smooth-number counts for several base budgets;
* finds prime subgroup escapes and replays the complete exponent-chain
  split;
* adds a false-positive factor to the support list and checks the direct
  strip.

The finite computation validates both branches but is not a substitute
for the analytic smooth-number estimate (10).
