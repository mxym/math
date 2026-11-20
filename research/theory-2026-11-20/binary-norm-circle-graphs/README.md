# Punctured binary norm circles are not graphs

**Theorem.** Let $q=2^m$, $m\ge3$, $K=\mathbb F_q$, $E=\mathbb F_{q^2}$, and $C=\{x\in E:x^{q+1}=1\}$. Every rank-$m$ binary linear map $E\to\mathbb F_2^m$ misses a value on $C$. If $m$ is even it also misses a value on $C\cup\{0\}$. Equivalently, no deletion of one point from $C$ is affinely equivalent over $\mathbb F_2$ to the graph of a function on $m$ binary variables. For even $m$, no deletion of two points from $C\cup\{0\}$ is such a graph either.

Equivalence uses cardinality: a surjective projection of the larger set admits a selection of one representative per fibre. Conversely, a graph projects bijectively to its first coordinate, and an affine change of the output does not affect surjectivity. Any rank-$m$ projection becomes the coordinate projection after choosing bases. In particular, when $m=6$, none of the 64-point subsets of the familiar 66-point Sidon construction can give an APN graph in any binary affine coordinates. This is not a bound on arbitrary Sidon sets or a general maximality theorem for APN graphs.

## Proof

Write $T=\operatorname{Tr}_{E/\mathbb F_2}$, $t=\operatorname{Tr}_{K/\mathbb F_2}$, $N(x)=x^{q+1}$, and $\ell_a(h)=T(ah)$. Define the **integer Hamming weight** $w(h)=\sum_{x\in C}\ell_x(h)$, where bits are represented by 0 and 1. The sum of all elements of the multiplicative group $C$ is zero, so $w(h)$ is even. We first prove
$$
 P(h):=\binom{w(h)}2\pmod2 = Q(h):=t(N(h)).
$$
The left side is the sum of all distinct pairwise products of the bits $\ell_x(h)$. Its polar form $B_P(h,g)=P(h+g)+P(h)+P(g)$ is $\sum_{x\in C}\ell_x(h)\ell_x(g)$, since $\sum_x\ell_x=0$. Thus
$$
 B_P(h,g)=T\left(h\sum_{x\in C}xT(gx)\right)=T(hg^q).
$$
Indeed upon expanding the absolute trace, the inner powers of $x$ have exponents $1+2^j$ for $0\le j<2m$. Their sums over $C$ vanish unless $q+1\mid1+2^j$, and equal 1 in that case. Precisely $j=m$ qualifies: for $j<m$ the positive exponent is smaller than $q+1$; for $j=m+r$, $1\le r<m$, its residue is $1-2^r\ne0\pmod{q+1}$. By trace transitivity $B_Q(h,g)=t(hg^q+h^qg)=T(hg^q)$ as well. Hence $P+Q$ is binary linear. Both functions are invariant under $h\mapsto ch$ for every $c\in C$; choosing $c\ne1$ shows that the linear difference vanishes on $(c+1)E=E$.

The polar form $B_Q$ is nondegenerate by the trace pairing. The sign sum of $Q$ equals
$$
 \sum_{h\in E}(-1)^{Q(h)}
   =1+(q+1)\sum_{v\in K^*}(-1)^{t(v)}=-q,
$$
using the norm fibres. Since $B_Q(h,a^q)=\ell_a(h)$, translating $h$ by $a^q$ gives the sign sum of $Q+\ell_a$ as $-q(-1)^{t(N(a))}$. In particular, if $t(N(a))=0$, then $Q+\ell_a$ has no $m$-dimensional totally singular binary subspace. For if such a subspace $H$ existed, its being totally singular would give $H\subseteq H^\perp$ for the polar form; dimensions give equality. Summing $(-1)^{Q+\ell_a}$ by cosets of $H$ would then give $+q$: the coset $H$ contributes $q$ and all other cosets contribute zero by character orthogonality.

Suppose $S=(C\cup\{0\})\setminus\{a,b\}$ is a graph in some binary affine coordinates. Identify the dual of $E$ with $E$ through $T$. The first-coordinate projection supplies an $m$-space $H$ of characters whose nonzero members take the value 1 on exactly $q/2$ points of $S$; a translation only complements a balanced bit. For $0\ne h\in H$,
$$
 w(h)=q/2+\ell_a(h)+\ell_b(h).
$$
As $w(h)$ is even, $\ell_a(h)=\ell_b(h)$. Since $4\mid q/2$, the established identity gives $Q(h)=\binom{q/2+2\ell_a(h)}2\bmod2=\ell_a(h)$. This equality also holds at zero. For a deletion from $C$ take $a=0$, so $t(N(a))=0$. For arbitrary two deletions when $m$ is even, $a=0$ or $N(a)=1$ with $t(1)=0$. Both conclusions contradict the preceding sign sum. ∎

## Consequence for regular hyperovals

Let a regular hyperoval (a nonsingular conic together with its nucleus) in $\mathrm{PG}(2,q)$ be viewed in an affine chart. Among its affine $q$-point subsets, an APN graph up to binary affine equivalence occurs **exactly** when $m$ is odd and the line at infinity meets the conic in two points. In this case the affine part is the graph of the inverse function up to binary affine coordinates.

Here are the details. When the line at infinity is exterior, the affine conic is an ellipse and a $K$-affine change puts it at $N(x)=1$ with nucleus 0 (standard affine conic forms, as in Nagy below). For even $m$ apply the theorem. For odd $m$, a subset obtained by removing the nucleus is covered by its first part after one further deletion. If the nucleus remains, two points of $C$ were deleted. Since $3\mid q+1$, a primitive cube root $\omega$ partitions $C$ into $(q+1)/3\ge3$ triples $\{x,\omega x,\omega^2x\}$. One full triple remains and sums to 0. Together with the nucleus this prevents the subset from being Sidon and thus from being an APN graph.

The other lines at infinity meet the hyperoval in two points. Through the nucleus, such a line is tangent to the conic. The affine part is a parabola, $K$-affinely equivalent to the additive graph $y=x^2$, hence not Sidon. At two distinct conic points it yields a hyperbola with nucleus, $K$-affinely equivalent to $xy=1$ together with $(0,0)$. This is the graph of $I(x)=x^{-1}$ off zero and $I(0)=0$. For horizontal difference $a\ne0$, the derivative away from $0,a$ is $a/[x(x+a)]$, so a given output gives at most two solutions there. The exceptional output $a^{-1}$ already has solutions $0,a$; it gains two more exactly if $(x/a)^2+(x/a)+1=0$, i.e. when $m$ is even. Thus $I$ is APN precisely for odd $m$. Binary affine equivalence preserves the Sidon property, and a function graph is Sidon precisely when the function is APN. No statement about nonregular hyperovals is needed.

## Context and provenance

* G. P. Nagy, [*Sidon sets, thin sets, and the nonlinearity of vectorial Boolean functions*](https://doi.org/10.1016/j.jcta.2024.106001), JCTA 212 (2025), Theorem 2 and its conic normal forms; [arXiv:2212.05887, versions 1 and 2](https://arxiv.org/abs/2212.05887). This establishes completeness of the appropriate conic or conic-plus-nucleus Sidon sets, not the impossibility of a graph **inside** them.
* C. Carlet, [*On APN functions whose graphs are maximal Sidon sets*](https://eprint.iacr.org/2023/621), Proposition 4.1: maximality of all APN graphs is equivalent to the single-point modification conjecture. The theorem here rules out a particular candidate family, not that conjecture.
* Trace-weight congruences have classical antecedents in binary Kloosterman sums and Zetterberg codes: R. Schoof and M. van der Vlugt, [*Hecke operators and the weight distributions of certain codes*](https://reneschoof.github.io/vdvhecke.pdf), and van der Geer–van der Vlugt and Helleseth–Zinoviev on the mod-8 congruence (reviewed with both references in [this survey, Theorem 1](https://citeseerx.ist.psu.edu/document?doi=9637143f00e231ae8db58b149a2b08fdba414f68&repid=rep1&type=pdf)). The short trace-polarization proof above requires no estimate of a Kloosterman sum. No claim of priority for the trace congruence is made.
* A search through 2026-11-20 for punctured norm circles, APN graphs, affine projection, Zetterberg codes and Kloosterman subspaces did not locate this graph-exclusion formulation. The 2026 Carlet–Picek paper on Sidon and sum-free sets and APN exponents concerns different multiplicative subgroups; [Thornburgh's recent APN-distance paper](https://doi.org/10.1007/s12095-026-00908-9) concerns exclude distributions and distances. The repository duplicate check found no previous copy of the punctured-circle argument. These are search findings, not a proof of novelty.

The analytic proof is independent of computation. Run `python3 -O check.py` for finite arithmetic and projection controls.
