# A sharp circular-sorting bound for the antipodal centralizer

**Yongxian Zhang (张永贤)**  
School of Computer Science and Engineering, South China University of Technology  
mxymmxym1@gmail.com · ORCID 0009-0000-3864-3536

## Abstract

For the circular sorting problem of Adin, Alon and Roichman, we give an exact
restricted extremal theorem in every twice-prime degree. If \(p\ge 3\) is prime,
then the largest circular sorting distance among permutations of
\(\mathbb Z_{2p}\) commuting with the antipodal half-turn is exactly \(2p-4\).
The universal upper bound underlying this result applies more broadly to
\(2m\) for every odd \(m\ge 3\). The proof uses the cycles of the quotient
permutation and parity of the monodromy of a two-sheeted cyclic cover.
This result does **not** determine the unrestricted sorting number \(t(2p)\),
which can be larger; it is not a solution of the general composite-degree
conjecture. A standalone exhaustive checker is supplied as a regression test.

## 1. Definitions and prior work

For \(n\ge 2\), write \(X_n=\mathbb Z/n\mathbb Z\), and let \(c_n(x)=x+1\).
For \(\pi\in S(X_n)\), let \(\kappa(\pi)\) denote its number of disjoint
cycles, **including fixed points**. Define
\[
 d_n(\pi)=n-\max_{0\le j<n}\kappa(\pi\circ c_n^j),
 \qquad t(n)=\max_{\pi\in S(X_n)}d_n(\pi).
\]
These are the circular sorting distance of a labelled circular arrangement
and the corresponding worst-case distance. A transposition exchanges any
two positions, and the target order is identified up to cyclic rotation.

Adin, Alon and Roichman [1] introduced the problem. Bastide, Bishnoi,
Groenland, Gijswijt and Joshi [2] established \(t(n)\le n-3\) for even
\(n\) (and also for \(3\mid n\)) and studied wreath-product constructions.
We prove a stronger bound for a natural *proper subgroup*. Nothing below
asserts that such a bound holds for the full symmetric group.

For \(n=2m\), let \(J=c_{2m}^{m}\), the fixed-point-free half-turn,
and define its centralizer
\[
 H_m=\{\pi\in S(X_{2m}):\pi J=J\pi\}
   =\{\pi:\pi(x+m)=\pi(x)+m\ \pmod {2m}\}.
\]
This group is naturally isomorphic to the wreath product \(C_2\wr S_m\)
and has cardinality \(2^m m!\).

## 2. Main results

**Theorem 1 (odd-half-size upper bound).** For every odd integer \(m\ge3\)
and every \(\pi\in H_m\), there is an integer \(j\), \(0\le j<2m\), such that
\[
               \kappa(\pi\circ c_{2m}^{j})\ge 4.
\]
Consequently \(d_{2m}(\pi)\le 2m-4\) for all such \(\pi\).

**Theorem 2 (exact twice-prime restricted extremum).** For every odd prime
\(p\),
\[
             \boxed{\max_{\pi\in H_p} d_{2p}(\pi)=2p-4.}
\]
In particular, any counterexample to the proposed stronger *unrestricted*
bound \(t(2p)\le 2p-4\) must break antipodal symmetry.

### Lemma 3 (cycle lifting)

Suppose \(m\ge 2\), \(\pi\in H_m\), \(0\le j<m\), and
\(r=j\pmod m\). Let \(f\in S(X_m)\) be the permutation induced by
\(\pi\) on antipodal pairs and put \(q_r=f\circ c_m^r\).
Each cycle \(O\) of \(q_r\) has either **one** or **two** cycles above it
under \(\pi\circ c_{2m}^j\). The number is two precisely when the total
fibre-switching parity (monodromy) \(M_j(O)\in\mathbb F_2\) is zero.
Moreover,
\[
                  M_{j+m}(O)=M_j(O)+|O|\pmod 2.
\]

*Proof.* Represent the elements of \(X_{2m}\) uniquely as \(x+me\),
\(0\le x<m\), \(e\in\{0,1\}\), and write the centralizing permutation as
\[
       \pi(x+me)=f(x)+m(e+g(x)\pmod2)
\]
for a unique \(f\in S(X_m)\) and \(g:X_m\to\mathbb F_2\).
For nonnegative \(j\) put \(y=(x+j)\pmod m\) and
\(k_j(x)=\lfloor(x+j)/m\rfloor\pmod2\). Then
\[
 (\pi\circ c_{2m}^{j})(x,e)
  =\bigl(f(y),\ e+k_j(x)+g(y)\pmod2\bigr).
\]
Iterating around a quotient orbit \(O\) switches the fibre exactly when
\(M_j(O)=\sum_{x\in O}(k_j(x)+g((x+j)\bmod m))\) is one.
If the parity is one, the two fibres form one orbit; if zero, they remain
two separate orbits. Replacing \(j\) by \(j+m\) adds one to every fibre
switch and leaves the quotient map unchanged, proving the formula.
\(\square\)

### Proof of Theorem 1

Fix an odd \(m\ge3\) and \(\pi\in H_m\). Use \(f,g\) from Lemma 3,
and let \(q_r=f\circ c_m^r\), \(r\in X_m\). Assume for a contradiction that
\[
       \kappa(\pi\circ c_{2m}^j)\le3\quad\text{for every }j.
       \tag{A}
\]
Every \(q_r\) has at most three cycles, since each quotient cycle lifts
to at least one upstairs. Because \(m\) is odd, all \(c_m^r\) are even
permutations. Hence all \(q_r\) have the same sign; equivalently their
numbers of cycles have the same parity.

For each \(x\in X_m\), precisely one \(r\in X_m\) makes
\(q_r(x)=f(x+r)=x\), because \(f\) is bijective. Consequently
\[
              \sum_{r\in X_m}\#\operatorname{Fix}(q_r)=m. \tag{B}
\]

**Case 1: all \(q_r\) have an odd number of cycles.**
Equation (B) gives some \(q_r\) with a fixed point. It cannot be a
single \(m\)-cycle because \(m\ge3\). Thus it has exactly three cycles.
Their lengths add to odd \(m\), so at least one has odd length.
By Lemma 3, that cycle lifts to two cycles at one of shifts \(j\) and
\(j+m\), while the other two quotient cycles lift to at least one each.
This gives four upstairs, contrary to (A).

**Case 2: all \(q_r\) have an even number of cycles.**
Every \(q_r\) has exactly two cycles. A permutation of \(m\ge3\) points
with two cycles has at most one fixed point. By (B), every \(q_r\) has
exactly one fixed point, so its cycle lengths are \((1,m-1)\).

For every \(y\in\{0,\ldots,m-1\}\), the element \(x=f(y)\) is fixed by
\(q_r\) for \(r\equiv y-f(y)\pmod m\). Choose the unique \(j\) with
\(0\le j<m\) and \(j\equiv y-f(y)\pmod m\), and write
\[
                 f(y)+j=y+km,\qquad k\in\mathbb Z.\tag{C}
\]
The fibre parity of the fixed quotient cycle is
\(F_j=g(y)+k\pmod2\). Thus \(F_{j+m}=F_j+1\).
The other quotient orbit \(O\) has even length \(m-1\), so Lemma 3
gives \(M_j(O)=M_{j+m}(O)\). If this common parity were zero,
we could choose from \(j,j+m\) the shift for which the fixed orbit
also has parity zero; both quotient cycles would then split in two,
giving four upstairs. Therefore (A) requires
\[
                         M_j(O)=1 \tag{D}
\]
for **every** \(y\).

Set \(S=\sum_{z=0}^{m-1}g(z)\in\mathbb F_2\).
Summing fibre-switching parities over all quotient cycles, and using
\(\sum_{x=0}^{m-1}\lfloor (x+j)/m\rfloor=j\) for every \(j\ge0\), gives
\[
        M_j(O)+F_j=S+j\pmod2.
\]
By (C) and oddness of \(m\),
\(j+k\equiv y-f(y)\pmod2\), and hence
\[
 M_j(O)\equiv S+j+g(y)+k
       \equiv S+y-f(y)+g(y)\pmod2.
\]
By (D), \(g(y)\equiv1+S+y-f(y)\pmod2\) for every \(y\).
Sum this equation over all \(y=0,\ldots,m-1\). Since \(f\) is a
permutation and \(m\) is odd, we obtain
\[
 S\equiv m(1+S)+\sum_y y-\sum_y f(y)
  \equiv1+S\pmod2,
\]
an impossibility. Both cases contradict (A), proving Theorem 1.
\(\square\)

### Proof of Theorem 2

Theorem 1 gives the upper bound \(2p-4\). For the reverse inequality,
choose an odd integer \(a\) whose residue modulo the odd prime \(p\)
is a primitive root. Such an \(a\) exists: a primitive root modulo \(p\)
can be replaced by its translate by \(p\) to make it odd.
Define \(\pi(x)=ax\pmod{2p}\). Because \(a\) is odd,
\(\pi\in H_p\).

Apply the Chinese remainder theorem to identify
\(X_{2p}\cong\mathbb F_p\times\mathbb F_2\).
For any shift \(j\), the map \(\pi\circ c_{2p}^j\) becomes
\[
      (u,e)\longmapsto(a(u+j),\ e+j\pmod2).
\]
Its first-coordinate permutation \(u\mapsto a(u+j)\) is conjugate to
multiplication by \(a\), and therefore consists of a fixed point and
one orbit of length \(p-1\).

If \(j\) is even, the second coordinate is unchanged, so **both**
quotient cycles split: \(\kappa=4\). If \(j\) is odd, the second
coordinate toggles: the fixed-point orbit lifts to one two-cycle,
while the even-length \((p-1)\)-orbit lifts to two cycles, so
\(\kappa=3\). Thus \(\max_j\kappa(\pi c_{2p}^j)=4\) and
\(d_{2p}(\pi)=2p-4\), proving sharpness. \(\square\)

## 3. Scope, verification, and open questions

- Theorems 1–2 are proved for actual permutations of \(\mathbb Z_{2m}\),
  not for a surrogate relaxation. Every quantifier and shift appears
  explicitly. There are no assumed classification inputs in the upper bound.
- The upper bound is established for all odd \(m\ge3\), but *attainment*
  is proved here only when \(m\) is an odd prime. The situation for
  composite odd \(m\) is not asserted.
- This is a restricted extremum in \(H_p\), not an evaluation of
  \(t(2p)\) over all permutations. In particular, there is **no**
  assertion that unrestricted \(t(22)=18\); the cited literature gives
  \(18\le t(22)\le19\).
- The checker `verify.cpp` performs an independent exhaustive enumeration
  for \(m=3,5,7\), of respectively \(48\), \(3840\), and \(645120\)
  centralizer permutations, and verifies the affine sharpness example for
  several larger odd primes. Computational tests are *regression checks*;
  the universal claim rests on the written proof above.
- No full Lean formalization is claimed, and no external human peer review
  has been performed. This work used AI assistance and independently
  reproducible mathematical/computational checks.

## References

[1] R. M. Adin, N. Alon and Y. Roichman, *Circular sorting*,
    arXiv:2502.14398 (2025). https://arxiv.org/abs/2502.14398

[2] P. Bastide, A. Bishnoi, C. Groenland, D. Gijswijt and R. Joshi,
    *Circular sorting, strong complete mappings and wreath product
    constructions*, arXiv:2510.18529 (2025, subsequent revisions).
    https://arxiv.org/abs/2510.18529

**Funding and acknowledgements:** No external funding; AI-assisted
research. No claim of external peer review or historical priority.

**Rights:** Copyright © 2026 Yongxian Zhang. All rights reserved for
this original note, without changing third-party rights or repository-wide
license/source notices.
