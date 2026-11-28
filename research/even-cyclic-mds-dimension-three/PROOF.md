# Proof

Throughout, \(q=p^f\) is a prime power, \(n\ge5\), \(p\nmid n\), and
\(q\not\equiv\pm1\pmod n\). An \([n,k]_q\) cyclic code here is a
linear code invariant under the usual cyclic coordinate shift; MDS
means minimum Hamming distance \(n-k+1\). Let \(\mu_a\) denote the
group of \(a\)-th roots of unity in an algebraic closure in the
characteristic in use.

## 1. Fourier and Frobenius reduction

Fix a primitive \(n\)-th root \(\zeta\). Over a splitting field of
\(X^n-1\), the shift is diagonalizable with distinct eigenspaces
spanned by \(v_e=(1,\zeta^e,\ldots,\zeta^{(n-1)e})\),
\(e\in\mathbb Z/n\mathbb Z\). On extension of scalars every cyclic
code is therefore spanned by the rows \(v_e\) of a set \(E\);
\(|E|\) is its dimension. The \(q\)-power Frobenius takes \(v_e\)
to \(v_{qe}\), so \(qE=E\). Conversely each stable set \(E\) gives
a base-field cyclic code: in the polynomial model take the monic
generator \(\prod_{j\notin -E}(X-\zeta^j)\). This product belongs
to \(\mathbb F_q[X]\) by Frobenius invariance and the stated Fourier
rows span its code after extension (the polynomial associated to
\(v_e\) evaluates to zero at \(\zeta^j\) unless \(j=-e\)). A linear
dimension-three code is MDS iff each three-coordinate projection is
an isomorphism: a singular projection is exactly a nonzero
codeword vanishing on those three coordinates, and Singleton gives
the other direction. Thus the test is that every three-column
determinant of the Fourier rows is nonzero. Base-field ranks are
unchanged on extension.

For every two different \(e,e'\in E\),
\(\gcd(n,e-e')\le2\) is necessary. Otherwise three distinct roots
in the kernel of \(z\mapsto z^{e-e'}\) give three columns on which
those rows coincide. If \(n\) is even, \(p\) is odd and the exponents
cannot all have the same parity: the two columns at \(z,-z\) would
be proportional. Consequently when \(n\) is even at least one
difference is a unit, and when \(n\) is odd all differences are units.

**Even \(n\).** Modulo even \(n\), \(q\) is odd and preserves parity.
Its permutation of \(E\) cannot be a three-cycle, which would put
all three exponents in one parity class. The identity fixes a unit
difference and would give \(q=1\bmod n\). Thus it fixes an exponent
\(a\) and swaps \(a+u,a+v\), with \(v=qu\) and \(u=qv\). The two
gcds \(\gcd(n,u)=\gcd(n,v)\) coincide and are at most two; they
cannot both be two because then all exponents have the same parity.
Hence both \(u,v\) are units, so \(q^2=1\bmod n\).
The remaining difference gives
\(\gcd(n,q-1)=\gcd(n,v-u)=2\). Write \(n=2m\). Now \(m\mid q+1\).
Since \(q\ne-1\bmod n\), \(q=m-1\bmod 2m\); as \(q\) is odd,
\(m\) is even. Finally
\(\gcd(2m,m-2)=\gcd(4,m-2)=2\) forces \(4\mid m\).

The equivalent parametrization is \(h=(q+1)/m\) positive odd
with \(4\mid m\). Conversely for \(m\ge4\) divisible by four and
\(q+1=hm\) with \(h\) positive odd, \(q\equiv m-1\bmod 2m\)
is a unit (indeed its square is \(1\bmod 2m\)).
The residues of \(q-1\) and \(q+1\) are \(m-2\) and \(m\),
both nonzero, so the parameters are in the open nonclassical
range, including \(h=1\), which §3 excludes. If \(h\) were
even, then \(2m\mid q+1\) would put it outside this range.
Under these conditions the set
\(\{0,1,m-1\}\) is stable, and all possible MDS supports just obtained
normalize to it by subtracting the fixed \(a\) and multiplying by
\(u^{-1}\). This is an equivalence **over the base field**: the
translation of \(a\) is implemented by scaling each coordinate
by \(\zeta^{-aj}\), which lies in \(\mathbb F_q^\times\), and a
unit multiplier is a coordinate permutation. If the MDS test
passes there is thus exactly one monomial-equivalence class in this
even-length scope. A base-field representative is
\[
\{(A+\operatorname{Tr}_{q^2/q}(B\zeta^j))_{j=0}^{n-1}
  : A\in\mathbb F_q,\ B\in\mathbb F_{q^2}\}.
\]
Indeed, \(\zeta\) has degree two over \(\mathbb F_q\) and the two
trace rows span \(v_1,v_{m-1}\) over the splitting field: if \(B\)
ranges over \(1,b\) with \(b\notin\mathbb F_q\), the coefficient
matrix on these rows has determinant \(b^q-b\ne0\).

**Odd \(n\), for context.** Again the identity is impossible by a
unit difference. In the transposition case \(q^2=1\bmod n\) and
\(\gcd(n,q-1)=1\), so \(q=-1\bmod n\), also excluded. For a
three-cycle \(E=\{e,qe,q^2e\}\), the difference \((q-1)e\) is a
unit, so \(\gcd(n,q-1)=1\), \(e\) is a unit, and \(q^3=1\bmod n\)
gives \(n\mid q^2+q+1\). Conversely those two conditions give a
stable three-element orbit with \(e=1\), as \(q\ne1\bmod n\).
All such supports are related by coordinate multipliers. Their
trace realization is
\((\operatorname{Tr}_{q^3/q}(B\zeta^j))_j\); after an
\(\mathbb F_q\) basis change its three rows span the Fourier
orbit: \(\zeta\) has degree three over \(\mathbb F_q\), so
the coordinates at \(1,\zeta,\zeta^2\) already determine \(B\)
by nondegeneracy of the trace pairing, and the formula expands
as a combination of the three Fourier rows.
This is the irreducible Singer-type case, with prior exact
Schur-norm tests. We record only an alternative convenient formula:
translate the exponents by \(-e\) and multiply by
\(((q-1)e)^{-1}\), obtaining \(\{0,1,r\}\) with
\(r=q+1\bmod n\), taken between \(0\) and \(n-1\). The translation
in this sentence is only used to compare determinants over the
splitting field, not to assert a base-field monomial map.
Both \(r\) and \(r-1\) are units, since \(q\) is a unit and
\(q+1\) is invertible by \(q^2+q+1=0\bmod n\). As explained in
the next section, the test is injectivity of
\(F_r(X)=1+X+\cdots+X^{r-1}\) on \(\mu_n\setminus\{1\}\).
Equivalently, the characteristic polynomial of multiplication by
\(F_r\) in
\(\mathbb F_p[X]/(1+X+\cdots+X^{n-1})\) has no repeated root.
The same polynomial over \(\mathbb Z\) has nonzero discriminant:
on the complex roots \(z=\exp(2\pi i j/n)\), its values are
\[
 F_r(z)=e^{\pi i (r-1)j/n}\,
          \frac{\sin(\pi rj/n)}{\sin(\pi j/n)},\qquad 1\le j<n.
\]
The real ratios are nonzero, and equality for two indices forces
\(n\mid(r-1)(j-k)\), hence \(j=k\). This auxiliary formula is not
a new existence claim for the odd Singer-type range.

## 2. Exact even-length obstruction

Retain \(n=2m,\ 4\mid m,\ q=m-1\bmod 2m\).
For three distinct column labels, multiply the labels by the
inverse of one of them; this preserves zero/nonzero determinant
because it only rescales the three rows. For normalized exponents
\(\{0,1,r\}\), labels \(1,z,w\) give a zero determinant exactly
when \(F_r(z)=F_r(w)\): subtract the first column from the other
two and divide by \((z-1)(w-1)\). This justifies the odd test as
well, in both directions.

In the even case \(r=m-1\). A label \(z\) has sign \(z^m=\pm1\).
Choose two labels of the same sign and normalize one to \(1\).
The other is then \(b\in\mu_m\setminus\{1\}\).
For such \(b\), \(F_{m-1}(b)=-1/b\), which is injective on
that sector; hence a bad triple has exactly two of one sign.
Write \(\gamma\) for its third normalized label:
\(\gamma^m=-1\), so \(\gamma\ne0,\pm1\).
For this label \(F_{m-1}(\gamma)=-(\gamma+1)/(\gamma(\gamma-1))\).
Therefore the triple \(1,b,\gamma\) is singular iff
\[
  b=\beta(\gamma):=\frac{\gamma(\gamma-1)}{\gamma+1}
     \quad\text{and}\quad b\in\mu_m\setminus\{1\}. \tag{1}
\]
Neither denominator vanishes, and the distinctness of the labels
is ensured because their signs differ except for \(1,b\).

For **existence of a singular triple**, the exclusion \(b\ne1\)
can be suppressed. The sign change preserves the odd sector
because \(m\) is even and satisfies
\(\beta(\gamma)\beta(-\gamma)=-\gamma^2\in\mu_m\).
If \(\beta(\gamma)=1\), then \(\beta(-\gamma)=-\gamma^2\ne1\):
otherwise \(\gamma^2=-1\) would give \(\gamma^m=1\) by \(4\mid m\).
Thus a collision exists iff some odd-sector \(\gamma\) has
\(\beta(\gamma)^m=1\).

Using \(\gamma^m=-1\), the equation for \(\beta(\gamma)^m=1\)
is \((\gamma-1)^m+(\gamma+1)^m=0\). Since \(p\ne2\), its left
side is twice \(B_m(\gamma^2)\), where
\[
 B_m(T)=\sum_{j=0}^{m/2}\binom{m}{2j}T^j .
\]
Squaring maps the roots of \(X^m+1\) two-to-one onto the roots
of \(T^{m/2}+1\). All these polynomials with roots of unity are
separable where required (\(p\nmid 2m\)). It follows that the
representative is MDS exactly when
\[
  D_m:=\operatorname{Res}_T(T^{m/2}+1,B_m(T))
        \quad\text{satisfies}\quad p\nmid D_m. \tag{2}
\]
Both polynomials in this integer resultant have degree \(m/2=n/4\).
No splitting field is needed to compute the test: reductions mod
\(p\) are coprime iff the resultant is nonzero mod \(p\).
Over \(\mathbb C\), \(D_m\ne0\). Otherwise
\(|\gamma|=|\beta(\gamma)|=1\) would give
\(|\gamma-1|=|\gamma+1|\), so \(\gamma=\pm i\), contrary to
\(\gamma^m=-1\). Thus for each fixed even length divisible by eight,
(2) excludes a finite set of characteristic primes, and only those
primes among fields in the specified residue class. It does not
assert all fields in the residue class are good. For instance,
\(D_4=36\) and \(D_8=2^4\,7^4\,17^2\). Dirichlet's theorem also gives
infinitely many prime fields satisfying the residue and avoiding
this finite set: \(\gcd(m-1,2m)=1\).

There is an exact count, including for the failing codes. Define
\[
 d=\deg\gcd_{\mathbb F_p[T]}(T^{m/2}+1,B_m(T)),\qquad
 e=\deg\gcd_{\mathbb F_p[X]}(X^m+1,X^2-2X-1).
\]
There are \(2d\) odd-sector \(\gamma\)'s with
\(\beta(\gamma)\in\mu_m\), and precisely \(e\) of these have
\(\beta(\gamma)=1\). Every remaining \(\gamma\) yields one bad
normalized triple with anchor \(1\) by (1). Choosing any of the
\(2m\) column labels as anchor produces every bad unordered triple
exactly twice, once for each of its two labels with the same sign.
Hence the number of unordered singular three-column minors of the
canonical representative is \(m(2d-e)\).

## 3. The norm-one curve and the first odd index

Let \(h=(q+1)/m\), a positive odd integer because
\(q=m-1\bmod 2m\). In particular \(p\nmid h\).
All \(2m\)-th roots of unity lie in \(L=\mathbb F_{q^2}\).
Let \(U\) be the norm-one torus of \(L/\mathbb F_q\);
\(U(\mathbb F_q)=\{x\in L^\times:x^{q+1}=1\}\) is cyclic of
order \(q+1\). Its subgroup of \(h\)-th powers is \(\mu_m\).
Choose \(\gamma_0\in\mu_{2m}\) with \(\gamma_0^m=-1\).
Then \(\gamma_0^{q+1}=-1\), and the set of odd-sector labels is
\(\gamma_0\mu_m\). If \(z\in L^\times\) has norm \(-1\), then
\(\bar z=-1/z\), and
\(\overline{\beta(z)}=\beta(-1/z)=1/\beta(z)\). The identities
also hold on the norm \(-1\) torsor as algebraic identities.
Consequently \(\beta\) is an \(\mathbb F_q\)-rational map from
that torsor to \(U\), wherever its values are defined and nonzero.
In particular the open curve in \(U\times U\) given by
\[
   y^h=\beta(\gamma_0 x^h) \tag{3}
\]
is defined over \(\mathbb F_q\). To see descent explicitly,
over \(L\) represent \(U\) by coordinates \((x,1/x)\);
the norm \(-1\) torsor has split coordinates \((z,-1/z)\).
The two conjugate coordinates of the map \(x\mapsto\gamma_0 x^h\)
are \((\gamma_0 x^h,\bar\gamma_0 x^{-h})\), of product \(-1\).
The formula for \(\beta(-1/z)\) verifies the two coordinates of
its image are inverse, so (3) is compatible with the interchange
of the split coordinates. Denominators and zero values are
excluded by the open domain; no rational \(x\in U\) is excluded
because neither \(1\) nor \(-1\) has norm \(-1\).

Over an algebraic closure divide by \(x^h\) and put \(Y=y/x\).
The function-field equation is
\[
  Y^h=\gamma_0\frac{\gamma_0 x^h-1}{\gamma_0 x^h+1}. \tag{4}
\]
For \(h>1\) its right side has \(h\) distinct simple zeros and
\(h\) distinct simple poles, all at finite nonzero \(x\).
The polynomial in \(Y\) is Eisenstein at a simple zero, so the
extension degree is \(h\) and the curve is geometrically integral.
In the tame Kummer cover onto the \(x\)-line, the \(2h\) simple
zeros/poles have ramification index \(h\) (a valuation \(1\) or
\(-1\) forces this), and all other points are unramified:
the right side is a unit there and the \(h\)-th root equation
has invertible derivative at its nonzero roots in the residue
field. This includes \(0,\infty\), with respective values
\(-\gamma_0,\gamma_0\). Riemann–Hurwitz on the smooth projective
model \(\mathcal C\) gives
\(2g-2=-2h+2h(h-1)\), hence \(g=(h-1)^2\).
For \(h=1\) the same conclusion follows from (4) being a rational graph.

Every \(\mathbb F_q\)-point of \(\mathcal C\) is represented in
(3). Indeed, each projection to the smooth projective norm-one
conic extends over the smooth complete curve. Writing
\(L=\mathbb F_q(\sqrt a)\) for \(a\) nonsquare, this conic is
\(u^2-av^2=w^2\); its two points at \(w=0\) are conjugate and
neither rational. Both projections of a rational point are
therefore in \(U(\mathbb F_q)\). At these \(x\) no zero/pole is
present in (3), and the \(y\)-derivative in the split equation
is invertible, so every such pair is a unique smooth point on
the model. Each allowed \(\gamma\) has exactly \(h\) preimages
under \(x\mapsto \gamma_0 x^h\) and each allowed value
\(\beta(\gamma)\) has precisely \(h\) preimages under
\(y\mapsto y^h\). It follows from §2 that
\[
 \#\mathcal C(\mathbb F_q)=2h^2d,\qquad
 \text{MDS}\ \Longleftrightarrow\ \mathcal C(\mathbb F_q)=\varnothing .
\]
There is also an explicit pairing on the actual points of (3),
not just on their projected labels. Choose \(\rho\in U(\mathbb F_q)\)
with \(\rho^h=-\gamma_0^2\), possible since \(-\gamma_0^2\in\mu_m\).
Then
\[
 (x,y)\longmapsto (-x,\rho x^2/y)
\]
is an involution without fixed rational points: \(h\) is odd,
\((-\!x)^h=-x^h\), and the second coordinate has \(h\)-th power
\(-\gamma^2/\beta(\gamma)=\beta(-\gamma)\). Applying it twice
returns both coordinates, and no nonzero \(x\) equals \(-x\).
If a point has \(\beta(\gamma)=1\), its paired point has
\(\beta(-\gamma)=-\gamma^2\ne1\) and gives the three distinct
labels in (1). This explains why there is no subtraction for
these coincidences in the Hasse–Weil exclusion, even though there
is a subtraction in the exact minor count.

Hasse–Weil now excludes an MDS code whenever
\(q+1>2(h-1)^2\sqrt q\). For \(h=1\) this always excludes.
For any surviving code, \(q+1\le 2(h-1)^2\sqrt q<2h^2\sqrt q\).
Thus \(n=2(q+1)/h<2\sqrt{2(q+1)\sqrt q}\);
in particular \(n<4q^{3/4}\). For any fixed \(h\) the inequality
leaves only finitely many possible \(q\), and (2) is exact for
them. This does not give a single finite list of bad \(q\) when
the index is allowed to vary.

If \(h=3\) then \(q\equiv11\bmod12\).
The Hasse–Weil bound excludes \(q\ge62\), since
\(q+1>8\sqrt q\) for \(q\ge62\) (equivalently
\((q+1)^2>64q\)). The positive integers under 62 in that residue
are \(11,23,35,47,59\), with 35 not a prime power.
For \(q=11,23,47,59\), respectively,
\(m=4,8,16,20\); the exact gcd degrees \(d\) are \(0,0,4,6\),
and the degrees \(e\) are \(0,0,0,2\).
Both replay paths independently certify the MDS survivors
\(q=11,n=8\) and \(q=23,n=16\), and the exclusions
\(q=47,n=32\), \(q=59,n=40\). The positive codes are not asserted
to be new examples.

## 4. Duality and boundaries

The Euclidean dual of a cyclic code is cyclic because the inverse
coordinate shift is its adjoint and also preserves the original
code. A generator matrix for a dimension-three code is a
parity-check matrix for its dual, and the smallest support of
a nonzero dual word is the minimum number of linearly dependent
columns (with nonzero relation coefficients on that support).
For the given \(n\ge5\) all triples independent is equivalent
to this minimum being four, by the rank bound and containment of
each smaller column set in a triple. Thus MDS is preserved
in both directions, and all existence and equivalence results
transfer to dimension \(n-3\); monomial equivalence transfers
by inverse transpose. Dimensions three and \(n-3\) are both
nontrivial for \(n\ge5\); the first admissible even length is eight.
Repeated-root lengths \(p\mid n\), as well as \(n\mid q\pm1\),
were outside the question slice from the outset. In characteristic
two the even-\(n\) slice is empty by \(p\nmid n\).
