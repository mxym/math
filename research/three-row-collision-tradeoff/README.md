# Three-row collision energies: sharp infinite families

[Complete written proof](PAPER.md) · [Independent exact checker](check_exact.py) ·
[Frozen replay](results/check_exact.txt) · [Hashes](SHA256SUMS) ·
[Proof audit](AUDIT.md)

**Sharp six-row square-matrix theorem on a structured class.**
If the six rows can be divided into two triples, each containing
either a coordinate row or two flat-modulus rows, then for **every**
\(c\ge0\)
\[
|\operatorname{per}A|+c|\det A|
\le\max\{10/3,1+c\}\prod_{i=1}^6\|A_{i,*}\|_2.
\]
The constant is **sharp inside the stated class**, because the
parallel constant matrix and a permutation matrix both qualify.
Consequently the complete conjectured six-row inequality is proved
when there are four flat rows with two arbitrary rows, two coordinate
rows with four arbitrary rows, or one coordinate and two other
flat rows with the remaining three arbitrary. See PAPER.md,
Theorem 10. The unrestricted six-row conjecture remains open.

**New sharp six-column result:** If **any two** of the three
nonzero rows have constant coordinate moduli (with arbitrary complex
phases and independent row normalizations), **the third row can be
completely arbitrary**. The paper proves the sharp collision inequality
\[
\operatorname{per}(UU^*)-S_6(U)
\ge\frac83\Re(\langle u,v\rangle
\langle v,w\rangle\langle w,u\rangle)
\]
and hence the full critical
\(S_6+(7/3)\det(UU^*)\le(10/3)\prod\|u_i\|_2^2\)
on this two-flat-row locus, including exact equality.
The proof uses a positive diagonal-plus-rank-one quadratic form,
Jensen's inequality, and an **exact factored rational identity (36)**,
verified as a bivariate integer-polynomial identity by the checker.
No restriction on the third row's phases, magnitudes or zero entries
is imposed.

The other infinite-width results prove for complex 3-by-n matrices,
**all n >= 3**:

- The **exact phase-unrestricted flat-modulus Pareto envelope**, all
  nonnegative weights, and every equality class:
  \[
  S_n+cW_n\le\max\{6(n-1)(n-2)/n^2,\ 1-6/n+12/n^2+c\}.
  \]
  The two sharp classes are parallel flat rows and orthonormal flat rows.
- For **arbitrary row moduli** and every c >= 5, the sharp
  \(S_n+cW_n\le(1+c)\prod\|u_i\|_2^2\),
  with pairwise-disjoint-support equality.
- Complete coordinate-row reduction and an exact Johnson-incidence
  representation, including its complete all-n spectrum.

At the **six-row critical coefficient 7/3**, the two-flat-row and
coordinate-row cases are solved; the **unrestricted 3-by-6 inequality
remains open**. The paper isolates the precise sufficient unproved
collision deficit estimate and gives an exact counterexample to an
unsound stronger Gram shortcut.

To reproduce, from repository root:

~~~sh
python3 -B research/three-row-collision-tradeoff/check_exact.py
python3 -B -O research/three-row-collision-tradeoff/check_exact.py
(cd research/three-row-collision-tradeoff && sha256sum -c SHA256SUMS)
~~~

Theorems are established by the written analytic proofs;
finite rational checks are independent regressions, not universal proof.
No novelty/priority, external review, or full six-row theorem is claimed.
