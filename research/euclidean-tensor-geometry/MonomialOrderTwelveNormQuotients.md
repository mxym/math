# Classifying four-colorability of twelfth-root norm quotients

**Yongxian Zhang.** AI-assisted mathematical development and internal verification; no external review or priority claim.

Let \(\zeta=e^{2\pi i/12}\), \(t=\zeta+\zeta^{-1}=\sqrt3\). For a nonzero nonunit \(\beta=A+Bt\in\mathbb Z[t]\), take the Cayley graph on \(\mathbb Z[\zeta]/\beta\mathbb Z[\zeta]\) with steps the signed powers of \(\zeta\). **Every such graph is four-colorable, except for the two real prime ideals above 11 and the two above 13.** Each of these four exceptional quotient graphs requires at least five colors. For a monomial direction graph in [Davidson's framework](https://arxiv.org/html/2610.09474v1), this provides a four-color certificate whenever its twelfth-root absolute norm is outside \(\{1,11,13\}\). For his explicitly unresolved degree-twenty polynomial \(f_\ast\), the twelfth-root target has norm 11 and falls among the exceptions. This gives no chromatic lower bound on the original monomial graph.

## 1. Large norm by explicit rounding

The real quadratic unit \(\varepsilon=2+\sqrt3\) in \(\mathbb Z[t]\) has norm one. Multiplying by powers of \(\varepsilon\) balances the absolute conjugate ratio of \(\beta\) into \([\varepsilon^{-1},\varepsilon]\), since one step multiplies the ratio by \(\varepsilon^2\). With \(D=|A^2-3B^2|\), every absolute conjugate of the balanced associate is at least \(\sqrt D/\sqrt\varepsilon\) and at most \(\sqrt D\sqrt\varepsilon\).

In the two complex embeddings \(\zeta\mapsto\zeta,\zeta^5\), use the real Euclidean scalar product given by their sum of Hermitian products. With \(i=\zeta^3,\omega=\zeta^4\) the integral basis \(1,\omega,i,i\omega\) has two diagonal Gram blocks \(\left(\begin{smallmatrix}2&-1\\-1&2\end{smallmatrix}\right)\). The inverse blocks are \(\frac13\left(\begin{smallmatrix}2&1\\1&2\end{smallmatrix}\right)\). Rounding in the dual basis thus has Euclidean error at most one: the squared error of each two-coordinate block with rounding errors bounded by \(1/2\) is at most \(1/2\).

Start with the additive character having label \(1/3\) on all four basis elements. The \(\omega\)- and \(i\omega\)-triples each sum to zero in \(\mathbb R/\mathbb Z\), hence every signed direction, a signed product \(i^j\omega^k\), has label \(1/3\) or \(2/3\). Approximate the vector for this character after multiplication by the balanced associate by a dual lattice point, and then divide by the associate as in the [fifth-root norm argument](MonomialOrderFiveNormQuotients.md). The resulting character annihilates the ideal and changes each direction's label by at most \(\sqrt{2\varepsilon}/\sqrt D\). If \(D\ge1600\), this is strictly below \(1/12\), so quarter arcs give four colors.

## 2. Exact small norm screen

In the same balanced choice, \(D<1600\) implies both absolute embeddings are below 80 since \(\varepsilon<4\). Therefore \(|A|\le80,\ |B|\le46\); for the second bound use \(80/\sqrt3<47\). With multiplication by \(\beta\) on the real basis \(1,t\) represented by
\[
M=\begin{pmatrix}A&3B\\B&A\end{pmatrix},
\]
use the image-lattice key \((D,g,r\bmod(D/g))\) from the fifth-root argument, where \(g\) is the gcd of the bottom row and \((r,g)\) is a Bézout combination of columns. The [standalone checker](verify-monomial-order-twelve-quotients.js) verifies exactly 1,217 distinct real ideals. For 1,206 of these, it gives two additive character rows \((a,b),(c,d)\) modulo \(D\) annihilating \(M\), and every signed direction has circular separation at least \(1/4\). For this test the labels of exponents \(0,\ldots,5\) are
\[
a,\ c,\ d-a,\ 2c-b,\ d-2a,\ c-b.
\]
Indeed successive powers use \(\zeta^2=t\zeta-1\), followed by \(t^2=3\), and \(\zeta^6=-1\).

The 11 remaining lattice keys are disposed of as follows.

- The six with norms \(2,4,22,26\) all have \(A+B\) even. Send \(t\) to 1 modulo two and \(\zeta\) to a root of \(z^2+z+1\) in \(\mathbb F_4\). The generator \(\beta\) is killed and all step images are nonzero. This is a coloring using the four additive values of \(\mathbb F_4\).
- The unique norm-25 key is the ideal \((5)\), as its computed generator has both coefficients divisible by five and index 25. The graph with 625 vertices, represented by the four basis coefficients modulo five, has a directly verified proper four-coloring. The checker generates its 625 labels deterministically and explicitly tests every edge.
- The two norm-11 keys and the two norm-13 keys correspond to \(t=\pm5\bmod11\) and \(t=\pm4\bmod13\), respectively. Changing \(t\) to \(-t\) replaces the generator \(\zeta\) by \(-\zeta\) and keeps the signed step set, so one graph per prime is enough. On the two-coordinate graph over \(\mathbb F_p\), the checker exhausts possible four-colorings in 2,305 and 170,202 search nodes, respectively. It chooses an uncolored vertex, branches on every available color already used, and branches once for the symmetric new colors. The choice of vertex is ordered by the number of different colors already present around it and then its uncolored degree; neither depends on the names of unused colors. Its recorded search runs terminate without reaching any budget and explicitly return non-four-colorability.

Finally, the \(Q_\ast(y)=y^5+y^4-4y^3-3y^2+3y+1\) in Davidson's example reduces to 1 modulo \(y^2-3\). Since \(P(t)=-2t\) and the sign for \(F_\ast\) is \(-1\), the twelfth-root generator is \(-2t-1\), of signed norm \(-11\). Its quotient is among the non-four-colorable cases. Although colorings in quotient targets lift to the monomial graph, quotient non-four-colorability does not exclude a four-coloring of the monomial graph itself.
