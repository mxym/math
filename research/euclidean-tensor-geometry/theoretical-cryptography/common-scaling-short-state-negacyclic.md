# A recognizable short-state class of weighted negacyclic convolutions

**Scope.** This is an exact calculation of the output probability mass of
a given linear transform of a supplied product distribution over a finite
algebra. All multiplier entries, local weights, and requested output are
given. There is no secret parameter, observed sample, inverse-problem
implementation, or security claim. The same negacyclic coefficient algebra is
used abstractly in Ring-LWE; the point is to identify when a particular
forward distribution admits calculable exact checks and how rare the
stated structure is in a uniform multiplier ensemble.

Let \(F=\mathbb F_q\) with \(q\) odd, \(n=2^s\), and
\(R=F[X]/(X^n+1)\) in its coefficient basis. Let
\(M=(f_{ai})\in R^{h\times m}\) be supplied. For each input component
\(i\) and site \(j\in\{0,\ldots,n-1\}\), let \(w_{i,j}:F\to\mathbb Q_{\ge0}\)
be an explicit table; it need not be stationary, strictly positive, or
normalized. For supplied \(v\in R^h\), the mass is
\[
   Z_M(v)=
   \sum_{\substack{x\in R^m\\Mx=v}}
          \prod_{i=1}^m\prod_{j=0}^{n-1}w_{i,j}(x_{i,j}).\tag{1}
\]
The result is a normalization formula, not an algorithm for an unknown
parameter of a sampling experiment.

Say that \(M\) has **common scaling width at most \(r\)** if there is a
unit \(Q\in R^\times\) such that every entry of \(QM\), reduced to the
coefficient basis, has degree at most \(r\); zero entries are allowed.
The scaling polynomial itself can be dense and its degree in \(R\) is
not restricted.

## 1. Recognizing a common scaling and counting its frequency

Let \(d_{\min}\) be the least degree of an irreducible factor of
\(X^n+1\) over \(F\).

**Theorem 1.** If \(r<d_{\min}\), common scaling width at most \(r\)
is deterministically recognized and a scaling found by finite-field
linear algebra and polynomial gcd. If also \(2r<n\), the primitive
polynomial vector representing the scaled family is unique up to a
common constant, and its maximum degree is the minimum scaling width.
For a fixed odd \(q\), both hypotheses hold for \(r=O(\log n)\) and
sufficiently large dyadic \(n\).

Indeed, every nonzero polynomial of degree at most \(r<d_{\min}\) is
a unit: no irreducible divisor of the modulus can divide it.
Thus if \(M\) is not all zero, every nonzero entry must be a unit.
Test one nonzero reference \(f_0\) by gcd, and reject if it is not
a unit. Enumerate the other entries as \(f_1,\ldots,f_\ell\).
Fix \(g_i=f_i/f_0\) in \(R\). A desired scale produces
\(p_0=Q f_0\ne0\) of degree at most \(r\) with
\[
             \deg(p_0 g_i\bmod (X^n+1))\le r\quad(1\le i\le\ell).
             \tag{2}
\]
Conversely any such \(p_0\ne0\) is a unit, hence so is
\(Q=p_0 f_0^{-1}\), and it gives the promised numerators. The high
coefficients in (2) are homogeneous linear equations in the \(r+1\)
coefficients of \(p_0\). No guessing of a denominator, decomposition
of a dense matrix, or search for a unit inside a general subspace is
needed in this parameter range. For the zero family \(Q=1\) suffices.

For uniqueness, write \(p_i=p_0g_i\) as the degree-\(\le r\) representative
and divide all \(p_i\), including \(p_0\), by their common monic gcd. The
gcd is a unit in \(R\), so the new vector still gives a valid scale.
Normalize \(p_0\) to be monic. If \(p\) and \(\tilde p\) are two such
primitive tuples, \(p_0\tilde p_i-\tilde p_0p_i\) is divisible by
\(X^n+1\) but has degree at most \(2r<n\), hence is zero as a polynomial.
Bezout with \(\gcd(p_0,p_1,\ldots,p_\ell)=1\) implies \(p_0\mid\tilde p_0\).
The same argument in the other direction gives equality, then equality
of all other components. Any smaller width is still in the same no-wrap
range and so cannot improve on the primitive tuple's maximum degree.

For dyadic \(n\), each root of \(X^n+1\) over an algebraic closure has
order \(2n\). Thus all irreducible degrees are
\(\operatorname{ord}_{2n}(q)\). If \(c=v_2(q^2-1)\) is fixed
and \(s+1>c\), the lifting formula
\(v_2(q^{2^j}-1)=c+j-1\) for \(j\ge1\) gives
\(\operatorname{ord}_{2n}(q)=2^{s+2-c}\). This is linear in \(n\)
for fixed \(q\), proving the logarithmic-width claim.

**Theorem 2 (exact frequency).** Fix one unit reference \(f_0\);
let the other \(\ell\) entries be independent uniform elements of \(R\).
Under \(r<d_{\min}\) and \(2r<n\), the passing probability is exactly
\[
          \frac{U_{r,\ell}}{q^{n\ell}},\qquad
 U_{r,\ell}=T_{r,\ell}-qT_{r-1,\ell},\qquad
 T_{r,\ell}=\frac{q^{r+1}-1}{q-1}q^{(r+1)\ell},\quad
 T_{-1,\ell}=0.                                               \tag{3}
\]
In particular when \(\ell\ge1\),
\((1-q^{-\ell})T_{r,\ell}\le U_{r,\ell}\le T_{r,\ell}\).
If all \(L=hm\) entries are uniform and **no** unit reference is fixed,
the passing probability instead equals
\[
   \frac{1+|R^\times|\sum_{\ell=0}^{L-1}U_{r,\ell}}{q^{n L}}.\tag{4}
\]
Here the all-zero tuple contributes 1 and \(U_{r,0}=1\).

To prove this, choose \(p_0\) monic of degree at most \(r\)
and choose the other \(\ell\) polynomials arbitrarily of degree
at most \(r\); there are \(T_{r,\ell}\) choices. Factoring out
the monic gcd of degree \(a\) leaves a primitive tuple of degree
bound \(r-a\), and there are \(q^a\) monic factors of that degree.
Thus \(T_{r,\ell}=\sum_{a=0}^r q^a U_{r-a,\ell}\), giving (3).
Primitive tuples enumerate distinct ratio families by Theorem 1.
Multiplication by the fixed unit reference is a bijection, so the
ratios retain independent uniform laws. The stated bounds follow from
\(qT_{r-1,\ell}/T_{r,\ell}\le q^{-\ell}\).
For (4), partition nonzero tuples according to the first nonzero entry.
Its value must be a unit; there are \(|R^\times|\) choices and
\(U_{r,\ell}\) choices for the remaining \(\ell\) entries. The preceding
entries are fixed zeros. This counts each tuple once. For odd \(q\)
one may compute \(|R^\times|=q^n\prod_P(1-q^{-\deg P})\)
over the distinct irreducible factors of \(X^n+1\).
Formula (3) is an exact structural rarity statement for the indicated
artificial multiplier model, not a characterization of any sampled
security instance.

## 2. The weighted forward law using a short reachable state

Suppose a scale has been found or supplied. Write
\[
 QM=\sum_{t=0}^r A_t X^t,\quad A_t\in F^{h\times m},
 \qquad \widetilde v=Qv .
\]
Since \(Q\) is a unit, (1) is unchanged after replacing the constraint
by \((QM)x=\widetilde v\). At site \(j\), set \(x_j\in F^m\)
and extend the coefficients by \(x_{j+n}=-x_j\). Multiplication
modulo \(X^n+1\) is exactly
\[
    \widetilde v_j=\sum_{t=0}^r A_t x_{j-t}.
\]

Consider \(Z=(F^h)^r\), with left shift \(J(z_0,\ldots,z_{r-1})
=(z_1,\ldots,z_{r-1},0)\), and define \(B:F^m\to Z\) by
\(Bu=(A_1u,\ldots,A_ru)\). Let \(P:Z\to F^h\) select the first
block. For \(r=0\), take \(Z=0\), \(B=P=0\).
The actual pending state at site \(j\) contains the contributions
of past sites to the next \(r\) output blocks:
\[
 z_j[t]=\sum_{\substack{a\ge1\\ a+t\le r}} A_{a+t}x_{j-a},
 \qquad 0\le t<r .
\]
This gives the first-order recurrence and output equation
\[
    z_{j+1}=Jz_j+Bx_j,\qquad Pz_j+A_0x_j=\widetilde v_j,       \tag{5}
\]
and the exact antiperiodic boundary \(z_n=-z_0\), not an ordinary
cyclic trace.

Let
\[
   W=\operatorname{span}_F\{J^a Bu:u\in F^m,\ 0\le a<r\},
   \quad D=\dim_F W,\quad
   K=\{(A_0u,Bu):u\in F^m\}\subseteq F^h\oplus W,\quad E=\dim_F K .
\]
These two dimensions are obtained by ordinary elimination;
\(D\le hr\) and \(E\le h+D\). All pending states belong to \(W\).

A useful exact converse is that every input tuple \(x_0,\ldots,x_{n-1}\)
has exactly one state tuple satisfying the recurrence and boundary,
ignoring the output tests. Indeed \(J^n=0\) since \(r<n\) and the
recurrence fixes \(z_n\) independently of \(z_0\); the boundary then
fixes \(z_0=-z_n\). The antiperiodic pending formula already gives
a solution, so this is the only one. Thus transfer around the signed
boundary introduces no duplicate weighting.

At each site, let \(H_j(c_0,c_+)\) be the weight distribution of
\((A_0x_j,Bx_j)\in K\) from the given independent tables.
To form it, add the effect of the \(i\)-th scalar coordinate in turn,
a convolution by one scalar table supported on the line
\(\{(A_0e_i,Be_i)t:t\in F\}\). This needs at most \(O(mq^{E+1})\)
rational operations per site. Use the transfer matrix on the
\(q^D\) states of \(W\)
\[
 \mathcal T_j[z,z']
 =H_j(\widetilde v_j-Pz,\ z'-Jz),                              \tag{6}
\]
with zero outside \(K\). The weighted mass is exactly
\[
               Z_M(v)=\sum_{z\in W}
            (\mathcal T_0\cdots\mathcal T_{n-1})[z,-z].         \tag{7}
\]
Indeed each expanded path and choice of scalar contributions counts
one input of (1), and the preceding uniqueness argument counts
each valid input exactly once.

Straight matrix multiplication and (6) give
\[
        O\bigl(nm q^{E+1}+n q^{3D}\bigr)
\]
rational operations, besides field-linear-algebra and indexing
overhead. With explicit rational tables the bit complexity remains
polynomial times this arithmetic count. Clear denominators separately
in each local table and divide by the product at the end. Every
intermediate weighted path sum then has bits bounded by the sum of
input weight bit lengths plus a polynomial bound for the log number
of terms. For fixed \(q\) this is classical polynomial time whenever
\(D,E=O(\log(\text{input size}))\), for instance fixed \(h\) and
logarithmic \(r\). The state dimension is not \(mr\): all \(m\)
site contributions are aggregated before the next site. If \(h=1\)
and \(r\) is the true maximum numerator degree, any nonzero entry
at degree \(r\) supplies a cyclic vector of the shift, so \(D=r\).

There is also a limited exact interpretation of \(D\) as a state
requirement. In the open causal filter in (5), starting at zero,
all \(q^D\) states are attainable after \(r\) past sites. For any
two distinct such states, giving identical all-zero future inputs
produces different next-\(r\) output blocks: their difference is
read successively by \(P J^a\). Thus any deterministic one-pass
generator of all filtered outputs must distinguish those states at
the corresponding cut. This is a state bound for that causal
conversion only, not a lower bound for arbitrary evaluation of (1).

## 3. An odd composite coefficient ring

The forward calculation does not need a field. Over
\(A=\mathbb Z/q\mathbb Z\) with odd \(q\), the same formulas hold
for the actual finite modules \(W\) and \(K\), with arithmetic bound
\(O(nm q\,|K|+n|W|^3)\) and polynomial overhead in their sizes.
Generate their elements by successively adding the finite
subgroups spanned by the indicated generators; this costs polynomial
overhead per element and also provides exact membership/index maps.
The signed-boundary uniqueness proof uses only nilpotence of \(J\),
not inversion in the coefficient ring. Input tables may be arbitrarily
correlated across the CRT factors of a site value. The computation
does not factor those probabilities.

A scale can also be found in this setting when a unit reference \(f_0\)
is present, the factorization of \(q\) is given (or \(q\) is fixed),
and \(r\) is less than every irreducible factor degree of the modulus
modulo every \(p\mid q\). Anchor the same congruences (2).
For each prime power \(p^e\|q\), compute generators of the homogeneous
solution module for coefficient vectors of \(p_0\) modulo \(p^e\).
For example integer Smith normal form of the matrix reduces these
congruences to scalar divisibilities. Check whether their reduction
modulo \(p\) is nonzero, equivalently some generator has nonzero
reduction. If not, that prime rules out all units. Otherwise pick
one such generator at each prime and combine their coefficients by
CRT. The resulting \(p_0\) is a unit because each nonzero short
reduction is a unit modulo \(p\), and invertibility lifts through
nilpotent powers of \(p\). It is essential to take the reduction of
the full solution module modulo \(p^e\), not simply the kernel of
the equations computed modulo \(p\). For example take \(q=9,n=4,r=1\),
reference \(f_0=1\) and second entry \(3X^2\). The high-coefficient
constraints vanish modulo 3 but force both coefficients of \(p_0\) to
be divisible by 3 modulo 9, so no unit scaling exists.

For squarefree \(q\), independent uniform multiplier entries have
independent CRT components. Conditional on a unit reference, the
passing probability is the product of (3) for its component fields.
This last factorization concerns the multiplier ensemble used for
recognition, not the supplied weighted mass. No corresponding
prime-power counting formula is asserted.

## 4. Dense examples and relation to prior algorithms

As a simple dense example, take \(Q=1-X\) in odd characteristic.
Then \(Q^{-1}=(1+X+\cdots+X^{n-1})/2\) inside \(R\), since
\(X^n=-1\). Any collection of fixed short numerators multiplied by
this inverse has the certified width, though the result can have
support at every position in its given coefficient basis.
The computation (5)–(7) preserves all of the supplied nonuniform
coordinate weights in the source. The frequency in (3) also shows
why this certifiable width is exceptional among independent uniform
multipliers, not a generic simplification.

* [Rosenkilde–Storjohann, *Algorithms for Simultaneous Padé Approximations*](https://cs.uwaterloo.ca/~astorjoh/issac16.pdf)
  treats the standard common-denominator congruence problem. The
  homogeneous system (2) is an instance, and the usual Padé framework
  is not new. The use here permits arbitrary scaling units by
  anchoring one entry and obtains the exact projective-family count
  under a no-wrap and unit-degree promise.
* [Forney and Vontobel, *Partition Functions of Normal Factor Graphs*](https://arxiv.org/abs/1102.0316)
  treats general sum-of-products graph calculations. The related
  [Forney, *Codes on Graphs: Duality and MacWilliams Identities*](https://arxiv.org/abs/0911.5508)
  treats tail-biting convolutional realizations. Finite-state transfer,
  reachability, and weight aggregation are classical. Here the
  explicit negative wrap, exact mass without overcounting, and the
  recognition/rareness conditions are the coefficient-algebra
  specialization; no general new graph-counting algorithm is claimed.

The companion checks compare finite brute-force forward distributions
with the exact signed-boundary state recurrence on generated algebraic
tables. They involve no secret model or cryptographic targets.
