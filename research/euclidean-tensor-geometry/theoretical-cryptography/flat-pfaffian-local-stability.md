# Quantitative flatness of unit-entry principal Pfaffians

This note is a robustness theorem for an explicit skew matrix with unit
complex entries, not a claim about general tensors from noisy data.
It follows the exact flat affine chart in
[flat-affine-planar-pfaffian.md](./flat-affine-planar-pfaffian.md),
but does not require a finite alphabet of input phases, a quadratic phase
description, or inspection of any principal minor of order above four.

Let \(A\) be a \(k\times k\) complex skew matrix, \(k\ge2\), with
\(|A_{ij}|=1\) at every off-diagonal entry. Fix a pivot \(p\); diagonal
gauge allows one to assume \(A_{pi}=1\) for \(i\ne p\). A matrix is
**flat** if all of its even principal Pfaffians have modulus one
(the empty Pfaffian is 1). Put
\[
 E_4(A)=\max_{|S|=4}\left|\,|\operatorname{Pf}(A_S)|^2-1\,\right|
\]
with maximum zero if no four-set exists. Throughout, distance between
skew matrices is the largest off-diagonal absolute difference.

**Theorem.** If \(E_4(A)\le\varepsilon\), there is an exactly flat
unit-entry skew matrix \(A^*\) with the same pivot row and
\[
 \|A-A^*\|_{\max}\le \min\{2,\,27(k-1)(k-2)\sqrt{\varepsilon}\}.
 \tag{1}
\]
It can be obtained by grouping near-equal labels; a posteriori the
diameter of the largest label group can replace the dimensional factor.
If input labels are rationals in \(\mathbb Q(i)\) on the unit circle
and \(\varepsilon\) is rational, the comparisons and repair are
deterministic polynomial time in the bit size, without numerical
rounding. The output labels can all be taken from the normalized
input labels, apart from the pivot's fixed labels (or a trivial flat
fallback when the bound is 2).

The exponent \(1/2\) cannot be improved, even for \(k=5\); this
asserts sharpness of the error exponent, not of the dependence on \(k\).
If \(\eta=\|A-A^*\|_{\max}\) and \(k^2\eta\le1/2\), one also has
\[
 \max_{|S|\ {\rm even}}
   |\operatorname{Pf}(A_S)-\operatorname{Pf}(A^*_S)|\le 2k^2\eta .
 \tag{2}
\]
Thus the entrywise repair controls the whole flat signature with a
polynomial factor, rather than a factorial count of matchings.

The conclusions apply separately to each exact clique of nonzero
entries if \(A\) is a direct sum up to reordering; between cliques
zero entries are unchanged. There is no claim for approximately
affine support or approximately valid matchgate identities.

## 1. Approximate modules on triples and quartets

Write \(\delta=\sqrt{\varepsilon}\). A module in an arc-labeled complete
graph means that all outgoing labels from the outside port to its
members agree, for every outside port. In our skew setup, incoming
agreement is automatic once outgoing agreement holds. An
\(r\)-approximate module has those pair differences at most \(r\).
As usual a nontrivial module is proper and has at least two members.

On three off-pivot ports, use the order sign to write the Pfaffian with
the pivot as a sum \(u+v+w\) of the three successive directed labels
around that triangle. The exact identity
\[
 |\operatorname{Pf}|^2-1
 =|u+v+w|^2-1=\frac{(u+v)(v+w)(w+u)}{uvw}
\]
shows that the product of the three opposite-pair distances is at
most \(\delta^2\). Their squared sum is
\(3+|u+v+w|^2\), so at least one distance is at least 1; the minimum
is consequently at most \(\delta\). Thus every off-pivot triangle
has a \(\delta\)-approximate pair module.

Consider four off-pivot ports. By relabeling a triple, take upper
entries in order \(0,1,2,3\) of the form
\[
  A_{01}=a,\ A_{02}=a',\ A_{03}=b,\ A_{12}=c,\
  A_{13}=d,\ A_{23}=e,\qquad |a-a'|\le\delta .
\]
If \(|a-b|\le10\delta\), use the triple \(\{1,2,3\}\) as an
\(11\delta\)-approximate module. If \(|d-e|\le10\delta\), use
\(\{1,2\}\) as a \(10\delta\)-approximate module. Otherwise the
triangle \(\{0,1,3\}\) forces \(d\) within \(\delta\) of \(-a\) or \(b\),
and \(\{0,2,3\}\) forces \(e\) within \(\delta\) of \(-a'\) or \(b\).
(The alternative direct agreements with \(b\) in the pivot row
are already excluded.) The choices cannot both be of the same type
because then \(|d-e|\le3\delta\). Interchange 1 and 2 if necessary
so that \(|d+a|\le\delta\) and \(|e-b|\le\delta\).
The triangle \(\{1,2,3\}\) now gives \(|c-d|\le\delta\)
or \(|c+e|\le\delta\). In the first case \(\{0,2\}\) is a
\(2\delta\)-approximate module. For the remaining case,
\[
 |c+b|\le2\delta,\quad |d+a|\le\delta,\quad |e-b|\le\delta .
 \tag{3}
\]

The last case requires care: bounding the Pfaffian defect by a generic
Lipschitz estimate here would only give an error exponent \(1/4\).
In the ideal pattern in (3), with \(a'=a\), the three signed terms in
the Pfaffian, divided by \(ab\), are
\[
 v=(1,a/b,-b/a).
\]
The actual terms \(z=(ae,-a'd,bc)/(ab)\) are within \(2\delta\)
of these entrywise, and all are unit. Put
\(t=\min(|a-b|,|a+b|)\). There are signs \(s_i\) for which
\(|v_i-s_i|\le t\). For any pair \(i,j\), set \(s=s_i s_j\);
the complex units \(u=z_i\bar z_j\) and \(u_0=v_i\bar v_j\) satisfy
\[
 \begin{split}
 |u-u_0|&\le4\delta,\\
 |u_0-s|&\le2t,\qquad |u-s|\le2t+4\delta,\\
 |\Re u-\Re u_0|
  &=\tfrac12 \big|\,|u-s|^2-|u_0-s|^2\,\big|
    \le 8\delta t+8\delta^2 .
 \end{split}
\]
Here the exact middle equality uses both unit moduli and a real sign.
Summing the three pairs with factor 2 compares
\(|\sum z_i|^2\) and \(|\sum v_i|^2\) with error
\(48\delta t+48\delta^2\). But
\[
 |\textstyle\sum v_i|^2-1
   =|a-b|^2|a+b|^2\ge 2 t^2 .
\]
As the actual defect is at most \(\delta^2\),
\(2t^2\le48\delta t+49\delta^2\), which implies \(t\le25\delta\).
If the near pair is \(a,b\), use the triple \(\{1,2,3\}\) with
error at most \(26\delta\); otherwise \(|a+b|\le25\delta\)
gives \(|d-e|\le27\delta\), and \(\{1,2\}\) works. Hence every
four-set off pivot has a \(27\delta\)-approximate nontrivial module.

## 2. Repair and the error on full Pfaffians

Use all the directed labels of the nonpivot submatrix, including
their negatives, as vertices in a finite label graph. Join labels
whose distance is at most \(27\delta\). Each connected component
has diameter at most \(27(L-1)\delta\) for \(L\) total distinct labels,
and \(L\le(k-1)(k-2)\). If \(27 L\delta<2\), no component contains
an antipodal pair; moreover the graph involution \(z\mapsto-z\)
pairs disjoint components. Replace every label by one representative
of its component, choosing the representatives of paired components
as negatives. The resulting entries remain skew and unit. Each
approximate module exhibited above becomes an exact module on its
triple or quartet. The 2-structure small-obstruction theorem now
gives an ordered tree of labels on the nonpivot ports:
reversal of labels is negation and so all its internal quotients
are linear, not symmetric complete nodes. Add the pivot with
forward label 1, and the exact Pfaffian tree product yields the
flat matrix \(A^*\). For the empty nonpivot label graph there is
nothing to repair. When \(27L\delta\ge2\), also \(27(k-1)(k-2)\delta\ge2\), so an
arbitrary flat chart with the stated
pivot has distance at most 2, giving (1). More generally one may
check the actual label graph for antipodal collisions and use the
largest component diameter as an a posteriori bound whenever none
occurs. Over \(\mathbb Q(i)\) square distances are exact rationals,
and all intermediate quantities and graph operations are polynomial-bit.

For any even \(S\) of size \(m>0\), denote \(B=A^*_S\) and
\(F=A_S-B\). The Pfaffian cofactor formula gives
\(|(B^{-1})_{ij}|\le1\), as every complementary even Pfaffian
and \(\operatorname{Pf}(B)\) has modulus 1. Put \(H=B^{-1}F\),
\(\rho=m^2\eta\). Then \(\|H\|_F\le\rho\), \(\|H\|_{\rm op}\le\rho\),
and \(|\mathrm{tr}H|\le\rho\) by the entrywise bound on \(B^{-1}\).
For \(\rho\le1/2\), use the convergent logarithm
and the branch normalized along \(B+tF\), \(0\le t\le1\):
\[
 \log\frac{\operatorname{Pf}(B+F)}{\operatorname{Pf}(B)}
      =\tfrac12\mathrm{tr}\log(I+H).
\]
Every higher term satisfies
\(|\mathrm{tr}(H^r)|\le\|H\|_F^2\|H\|_{\rm op}^{r-2}\) for \(r\ge2\).
Hence the logarithm has modulus at most
\((\rho+2\rho^2)/2\le\rho\), which gives an absolute difference
at most \(e^\rho-1\le2\rho\). This proves (2); the empty Pfaffian
requires no estimate. When there are several cliques, use the
same inverse estimate on the block diagonal up to permutation;
a subset hitting some clique oddly has zero Pfaffian before and
after repair.

A consequence for an antipodally closed phase alphabet of minimum
pair separation \(\Delta>0\) is an exact gap:
if \(27\sqrt{\varepsilon}<\Delta\) then no repair is necessary
and all Pfaffians are already flat. For roots of unity of even
order \(M\), \(\Delta=2\sin(\pi/M)\).

## 3. The exponent is sharp

Use four nonpivot ports with upper entries, ordered as in Section 1,
\[
 (a,a',b,c,d,e)=(1,1,u,-u,-1,u),\qquad
 u=e^{i\theta},\quad 0<\theta\le\pi/2 .
\]
All triples have exact modules, so all four-port Pfaffians involving
the pivot have unit modulus. The one other four-port Pfaffian is
\(u+1-u^2\), giving \(E_4=4\sin^2\theta\).
Every proper nontrivial subset of the nonpivot four-set has an
outside port which distinguishes two of its members by at least
\(|u-1|\); this follows by inspecting the six pairs and four
triples, whose distinct labels are among \(1,-1,u,-u\).
In particular, the two classes \(u\) and \(1\) cannot be merged
without an entry change at least \(|u-1|/2\).
In any flat chart with the same normalized pivot a nontrivial
module is forced, so
\(\|A-A^*\|_{\max}\ge |u-1|/2\ge\sqrt{E_4}/4\).
For a comparison flat chart allowed a different pivot row of
unit labels, re-gauge it back to the normalized pivot using its
own pivot entries. Its distance to the original chart increases
by at most a factor of three by the triangle inequality on three
unit factors, yielding lower constant \(1/12\) in that case.
For even roots of unity, choosing \(u=e^{2\pi i/M}\) also shows
the inverse-square scale of the finite-alphabet gap is necessary
up to constants.

## Attribution and scope

The exact Pfaffian interpretation is classical:
[Cai–Gorenstein, *Matchgates Revisited*](https://theoryofcomputing.org/articles/v010a007/v010a007.pdf).
The use of nonprime triples and quartets to force the exact labeled tree
is the small-obstruction theorem of
[Engelfriet, Harju, Proskurowski and Rozenberg](https://www.sciencedirect.com/science/article/pii/030439759400272X),
as restated in [Hellmuth–Stadler–Wieseke,
Theorem 2.2](https://arxiv.org/pdf/1603.02467). Their editing problem
measures discrete changes; the statement here is a continuous sup
perturbation on a phase chart with every local defect controlled.
The connection between Wick relations and general Gaussianity
tests is not new, and this is not a replacement for such tests.
The particular estimate is for an already specified unit-entry
Pfaffian chart. It is not a stability statement for hidden tensors,
deployment models, or any cryptographic scheme.
