# An asymmetric Ramsey product bound for the induced-six-cycle Erdős–Hajnal exponent

**Yongxian Zhang.** AI-assisted derivation and internal verification; no external peer review or priority claim.

Let \(h_H(n)\) be the minimum of \(\max(\alpha(G),\omega(G))\) over all \(n\)-vertex graphs with no induced copy of \(H\). We prove
\[
h_{C_6}(n)=O\!\left(n^{4/13}(\log n)^{6/13}\right);
\qquad
c_{\rm EH}(C_6)\le 4/13.
\]
This is an upper obstruction on the admissible exponent, not a positive polynomial lower bound and not a disproof or resolution of the Erdős–Hajnal conjecture.

## Construction

Use the following two off-diagonal Ramsey lower bounds, valid for every sufficiently large integer \(t\):

1. [Mubayi–Verstraëte, *A note on pseudorandom Ramsey graphs*, Corollary 4 (published version, JEMS 26 (2024), pp. 153–161)](https://ems.press/content/serial-article-files/42561?nt=1) gives \(r(C_6,K_t)=\Omega(t^{5/4}/\sqrt{\log t})\) in the ordinary subgraph sense. Thus there is a graph \(A_t\) on at least \(a t^{5/4}/\sqrt{\log t}\) vertices with no six-cycle even as a noninduced subgraph and with \(\alpha(A_t)<t\), where \(a>0\) is absolute. Also \(\omega(A_t)\le 5\) because six mutually adjacent vertices contain a six-cycle as a subgraph.
2. [Kim, *The Ramsey number \(R(3,t)\) has order of magnitude \(t^2/\log t\)* (1995)](https://doi.org/10.1002/rsa.3240070302) gives a triangle-free graph \(B_t\) on at least \(b t^2/\log t\) vertices with \(\alpha(B_t)<t\). Its complement \(D_t=\overline{B_t}\) has \(\alpha(D_t)\le 2\) and \(\omega(D_t)<t\). Since the six-cycle has an independent triple, \(D_t\) has no induced six-cycle.

Form \(G_t=A_t\circ D_t\), the lexicographic product. A nontrivial proper module \(M\) of \(C_6\) would have an outside vertex adjacent to all of \(M\), by connectivity and the module property. As all degrees are two, \(M\) would then be exactly the two neighbors of that vertex. In \(C_6\) another outside vertex distinguishes these two neighbors, so no such \(M\) exists. In an induced six-cycle within the product, any intersection with a fiber is a module; hence the entire cycle would lie in one fiber, or use six distinct fibers and project to a six-cycle. Both possibilities are excluded. Independence and clique numbers multiply in a lexicographic product, so
\[
\alpha(G_t)<2t,\quad \omega(G_t)<5t,\quad
|V(G_t)|\ge ab\frac{t^{13/4}}{(\log t)^{3/2}}.
\]
To obtain a graph of any sufficiently large order \(n\), take \(t=\lceil Cn^{4/13}(\log n)^{6/13}\rceil\) for a large absolute constant \(C\) and take any \(n\) vertices of \(G_t\). For large \(n\), \(\log t\le\log n\), and the powers of \(\log n\) cancel in the lower bound on \(|V(G_t)|\). Taking \(C^{13/4}ab\ge1\) suffices. Heredity and monotonicity of both homogeneous numbers give the bound for all such \(n\). The logarithm can be absorbed in \(n^\varepsilon\) for every fixed \(\varepsilon>0\); thus no exponent larger than \(4/13\) is possible.

## Transfer principle and scope

This argument separates the clique and stable-set constraints into different factors instead of insisting that one finite base graph balance them. For any prime \(H\), put \(s=\alpha(H)\ge2\). The same reasoning gives order at least
\[
(r(H,K_t)-1)(r(K_s,K_t)-1)
\]
on induced-\(H\)-free graphs with homogeneous number at most \((|V(H)|-1)t\), with ordinary Ramsey numbers on the right. Indeed the first factor forbids \(H\) as a subgraph and has clique number less than \(|V(H)|\), while the complement of the second factor forbids induced \(H\) by independent-set size and has clique number less than \(t\). This transfer does not require the factors to be complementary. For comparison, using the disjoint union of order \(t\) of the \(D_t\) graphs already gives \(c_{\rm EH}(C_6)\le1/3\); the sparse cycle-Ramsey factor improves it to \(4/13\).

[Chudnovsky–Scott–Seymour–Spirkl, Theorem 1.9](https://doi.org/10.1112/plms.12504) gives the lower-bound Erdős–Hajnal property for graphs avoiding both \(C_6\) and \(\overline{C_6}\). This note instead concerns the single-exclusion exponent and does not assert either product factor excludes both. The [Erdős Problem a Day working report for #61](https://erdosproblemaday.com/report/61) uses only balanced Paley-17 powers for its displayed upper obstruction, \(\log_{17}3\approx0.38776\); the asymmetric product gives \(4/13\approx0.30769\). The product identities and ingredient Ramsey theorems are not new. Targeted searches for the precise \(4/13\) coefficient and use of the cycle-Ramsey construction in this coefficient did not locate an earlier statement; no claim is made that the bound is the best known in the entire literature.
