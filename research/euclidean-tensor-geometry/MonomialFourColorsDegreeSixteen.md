# Four colors for one-parameter monomial direction graphs through degree sixteen

**Yongxian Zhang.** AI-assisted proof development and internal verification; no external review or priority claim.

For \(|\alpha|=1\), define \(\Gamma_\alpha\) on the additive group \(\mathbb Z[\alpha]\) with allowed differences \(\pm\alpha^n\), \(n\ge0\). [Davidson, Conjecture 4.7](https://arxiv.org/html/2610.09474v1) proposes that \(\chi(\Gamma_\alpha)\le4\) for every \(\alpha\). His published preprint proves this for transcendental parameters, roots of unity, all algebraic nonintegers, and algebraic degree at most eight. It mentions undeveloped reductions to finite candidate collections for higher degrees. Here we prove the four-color bound for every algebraic parameter of degree at most **sixteen**. The number of coefficients tested in the last case is finite by an explicit analytic bound, not an assumed height cutoff. This does not determine the plane's chromatic number or exhibit its finite six-chromatic unit-distance graph.

## Trace reduction

Only noncyclotomic algebraic integers need be considered. The primitive minimal polynomial is monic and reciprocal, \(f(x)=x^r F(x+x^{-1})\), of degree \(2r\). As in Davidson §4.4, if any of \(F(-2),F(-1),F(0),F(1),F(2)\) has absolute value larger than one, his elementary trace evaluations give four colors; none is zero. By his Lemma 4.4, the other case is
\[
P(y)=y(y^2-1)(y^2-4),\qquad F(y)=P(y)Q(y)+s,\qquad s\in\{-1,1\},
\]
for monic \(Q\). Also the absolute norm \(D_8\) of \(F(\sqrt2)\) must equal one, or his Lemma 2.10 gives four colors.

If \(Q=1\) (degree ten for \(f\)), then \(P(\sqrt2)=-2\sqrt2\) and \(D_8=7\); this is Davidson's worked norm-7 example. If \(Q=y+c\) (degree twelve), the condition is \((s-4)^2-8c^2=1\), because this signed norm is \(1\bmod 8\). Thus \(s=1,c=\pm1\); replacing \(\alpha\) with \(-\alpha\) reduces to \(c=1\) without changing the allowed differences or graph. Modulo \(y^2+y-1\), \(P=2-y\) and \(F=2+2y\). Consequently \(\Phi_5\) divides \(f\) modulo two, and Davidson's Proposition 2.8 gives a homomorphism to the four-colorable Eisenstein quotient, in fact \(K_4\).

For \(Q=y^2+cy+d\) (degree fourteen), put \(v=d+2\). The signed eighth-root norm is \((s-4c)^2-8v^2\), so \(D_8=1\) implies \(v^2=2c^2-sc\) and \(d\equiv c\bmod2\). If \(c\) is even, \(Q\equiv y^2\); if odd, \(Q\equiv y^2+y+1\). The former gives \(\Phi_5\mid f\bmod2\), the latter \(\Phi_9\mid f\bmod2\). These divisions can be read in trace coordinates modulo \(y^2+y+1\) and \(y^3+y+1\), respectively, or by the included direct polynomial verifier.

## An explicit norm threshold for orders five and ten

Let \(\zeta=e^{2\pi i/5}\), \(t=\zeta+\zeta^{-1}\), so \(t^2+t-1=0\). For \(\beta=F(t)\) or \(F(-t)\), write \(D=|N(\beta)|\) in the real quadratic field. If \(D\ge1600\), the quotient of \(\mathbb Z[\zeta]\) by \((\beta)\), with steps all signed fifth roots, is four-colorable. This induces a four-coloring of \(\Gamma_\alpha\) by \(x\mapsto\zeta\) or \(x\mapsto-\zeta\). The latter order-ten powers have the same signed steps.

Here is an explicit constant in Davidson's norm argument. Let \(\varphi=(1+\sqrt5)/2\). Multiplication by a power of the real unit \(t\) balances the two absolute conjugates of \(\beta\) so their ratio lies in \([\varphi^{-2},\varphi^2]\). Each conjugate is then at least \(\sqrt D/\varphi\) in absolute value. In the two complex embeddings use the Euclidean scalar product \(\operatorname{Re}\sum_{i=1}^2 z_i\overline{w_i}\). The integral basis \((1,\zeta,\zeta^2,\zeta^3)\) has Gram matrix \((5I-J)/2\), where \(J\) is the all-ones matrix. Its inverse is \((2/5)(I+J)\), so rounding the four coordinates relative to the dual basis moves a vector by norm at most \(\sqrt2\): the squared bound comes from \((2/5)(\sum e_i^2+(\sum e_i)^2)\le2\) with \(|e_i|\le1/2\).

Start with the additive character sending the five consecutive fifth powers to \(1/3,1/3,1/3,1/3,2/3\) in \(\mathbb R/\mathbb Z\). Their sole integral relation is the zero sum of the powers, and the indicated values sum to \(2\); hence this character exists. Lift it to a Euclidean vector \(w_0\). Round \(\beta' w_0\) to a dual-lattice point \(w'\) using the balanced associate \(\beta'\), and divide by the two real embeddings of \(\beta'\). The resulting vector defines a character annihilating \(\beta'\mathbb Z[\zeta]\), hence \(\beta\mathbb Z[\zeta]\). Each fifth power has Euclidean norm \(\sqrt2\). Its circular label changes by at most \(2\varphi/\sqrt D\), which is strictly below \(1/12\) for \(D\ge1600\) since \(\varphi<5/3\). All labels then have distance at least \(1/4\) from zero; four half-open quarter arcs give the required coloring.

## Degree sixteen: finite reduction and exact replay

Let \(Q=y^3+cy^2+dy+e\). Put \(u=d+2\), \(v=e+2c\). The signed eighth-root norm is \((s-4u)^2-8v^2\), so the unscreened case has \(v^2=2u^2-su\) and \(e\equiv d\bmod2\). For \((c,d)\equiv(0,0),(1,0),(1,1)\bmod2\), direct division gives \(\Phi_{15},\Phi_9,\Phi_7\), respectively, as factors of \(f\bmod2\). The remaining parity is \(c\) even and \(d,e\) odd. In particular \(v\) is odd, \(u\ne0\), and we may assume \(v>0\) by replacing \(\alpha\) with \(-\alpha\), which takes \((c,d,e)\) to \((-c,d,-e)\) while preserving \(s\).

Write \(N(A,B)=A^2-AB-B^2\), the signed norm of \(A+Bt\). Define \(X=s-u-2,\ Y=3u+1,\ Z=2v-c,\ W=-2c-v\). Direct reduction modulo \(t^2+t-1\) gives the coefficients \((X+Z,Y+W)\) for \(F(t)\) and \((X-Z,Y-W)\) for \(F(-t)\). Denote their signed norms by \(N_+,N_-\). Only \(|N_+|,|N_-|\le1600\) need be tested. The difference identity is
\[
\frac{N_+-N_-}{10}=(3u+1)c+(s-2-u)v.
\]
With \(h=c-v/3\) and \(U=|u|\ge100\), we have \(|v|\le3U/2\), so \(|h|\le(320+4U)/(3U-1)<4\). Substituting \(v^2=2u^2-su\) in the sum gives
\[
\frac{N_++N_-}{2}
=5\left[\frac{u^2}{9}+\left(1-\frac{14s}{9}\right)u-\frac53 v h-h^2\right]+6-5s.
\]
For \(U\ge200\) this is at least \(5(U^2/9-13U-16)+1>1600\), a contradiction. For \(1\le U\le199\), use \(|v|\le2U\) and the same difference identity to obtain \(|h|<(320+6U)/(3U-1)+1\le164\). Thus \(|c|<300\). All remaining cases lie in a small exact enumeration, with no coefficient bound assumed before the norm cutoff.

The [standalone verifier](verify-monomial-four-colors-degree-sixteen.js) checks 38 cases after sign symmetry and the two norm cutoffs. Nineteen have a direct \(\Phi_m\mid f \bmod q\) certificate from Davidson Proposition 2.8. For the other nineteen, it finds exact quarter-circle characters in the order-five or order-ten quotient. To reproduce these characters, let \(\beta=A+Bt\), \(D=|N(A,B)|>1\), and choose two additive coordinate characters with numerator rows \((a,b)\), \((c',d')\) modulo \(D\) in the basis \(1,t\). Both rows must annihilate
\[
\begin{pmatrix}A&B\\B&A-B\end{pmatrix}\pmod D .
\]
The verifier enumerates exactly this kernel from the two rows of the adjugate matrix and independently checks the equations. Using the basis \(1,t,\zeta,t\zeta\), the five step labels are \(a,c',d'-a,-b-d',b-c'\) modulo \(D\). The verifier checks that each label has circular distance at least \(D/4\) from \(0\) before normalization. All 38 certificates are checked using only integer arithmetic, so no numerical graph embedding, optimization or probabilistic search is required to establish the degree-sixteen claim.

## Scope

The new increment is the finite-height certificate through degree sixteen. It does not settle Davidson's conjecture in higher degrees, his three-color conjecture for algebraic nonintegers, or the plane's chromatic number. In particular the unresolved degree-twenty polynomial explicitly singled out in Davidson §5 is outside this theorem; see the [binary quotient obstruction](MonomialBinaryQuotientObstruction.md) for a precise limit of that approach.
