# Small pure powers and a terminal mixed-row obstruction

Fix an even integer \(N\). The vertices are the odd primes \(x<N-1\) coprime to \(N\); include every arc \(x\to y\) with \(y\mid N-x\), with entry \(A_{xy}=v_y(N-x)\). An all-composite terminal means a factor-closed strongly connected component in which every \(N-x\) is composite. Unlike a Goldbach exception, such a component may occur at a represented center. A row is *pure* if \(N-x=y^e,\ e\ge2\); a *mixed* row has at least two distinct factors.

**Theorem.** Write \(k\) for the size of an all-composite terminal, \(t\) for its number of mixed rows, \(b\) for its number of pure inputs \(>\sqrt N\), and \(\nu=\operatorname{nullity}_{\mathbb Q}(I-A)\).

1. At **every** center, \(b+\nu\le t\). The inequality also holds for the entire all-composite forward closure of any nonempty set of seeds \(\le\sqrt N\), without irreducibility (for \(N\ge 10\)).
2. Fix a finite set of primes \(F\). At every sufficiently large even \(N\) supported on \(F\), the entire graph has at most one pure input \(x\le\sqrt N\). If it occurs, \(N-x\) is the square of a prime, and for each fixed \(\epsilon>0\) one has \(x>N^{1/2-\epsilon}\) at all sufficiently large such centers. There is no such input if \(N\) is a square. Consequently \(k+\nu\le2t+1\), or \(k+\nu\le2t\) in the square case, in both settings of part 1.
3. At every sufficiently large even \(F\)-supported \(N\), **every all-composite terminal has at least three mixed rows**, even without prescribing any seed in the terminal or capping \(k\). More generally, for each fixed \(T\), no nonsingular all-composite terminal has \(t\le T\) there. Thus if an all-composite terminal exists, three or more genuinely branching rows are unavoidable. This does not eliminate all terminals and does not establish binary Goldbach for smooth centers.

Thresholds with Subspace Theorem input are not asserted effective.

## 1. A dominant minor, independent of smoothness

Every terminal vertex is the target of an arc and hence is at most \(N/3\), since each complement is odd and composite. In an all-composite forward closure with small seeds the same bound follows by reachability, also for the seeds. Thus all complements are in \([2N/3,N)\). Distinct pure rows have distinct output primes: two distinct powers of the same odd prime differ in ratio by at least 3; equal powers give the same row. The output of any pure row is \(\le\sqrt N\).

Eliminate from the linear equations \((I-A)v=0\) only the \(b\) large pure coordinates \(H\), by substituting \(v_H=e_Hv_{u_H}\), where \(N-H=u_H^{e_H}\). These substitutions preserve nullity and leave \(t+a\) equations in as many variables, where \(a=k-t-b\) counts the small pure inputs. Choose a parent \(x_H\) for each \(H\); in the forward-closure version a large vertex is not an initial seed. The chosen parents are mixed, all distinct, and each chosen complement contains its prescribed \(H\) precisely once and no other large label, since two factors larger than \(\sqrt N\) cannot fit.

Select the \(b\) parent rows and all \(a\) small pure rows. As columns select the outputs of **all** \(a+b\) pure inputs, which are distinct and small. In the \(x_H\) row multiply the columns by their positive weights \(\log u\). The designated term in column \(u_H\) has size \(\log(N-H)\). Other physical terms have total size at most \(\log((N-x_H)/H)\); the identity term costs at most \(\log x_H\) if this column belongs to the minor and zero otherwise. If \(x_H\le\sqrt N\), strict domination follows from
\[
H(N-H)>x_H(N-x_H),
\]
by monotonicity of \(z(N-z)\) up to \(N/2\). If \(x_H>\sqrt N\), its identity column is absent and \(H(N-H)>N-x_H\). This comparison counts an identity term as a possible cancellation even in the designated column. For a small pure row \(x\to u^e\), the designated size \(\log(N-x)\) exceeds the only possible other size \(\log x\). After permuting columns, the scaled square minor is strictly row diagonally dominant, hence nonsingular. Thus \(\nu\le t+a-(a+b)=t-b\).

## 2. Only one possible short pure row on the smooth rail

Write \(N=\prod_{\ell\in F}\ell^{n_\ell}\), \(L=\log N\). Suppose \(3\le x\le\sqrt N\) is a unit prime and \(N-x=y^e,\ e\ge2\). In particular \(y\nmid N\). For the positive rational bases consisting of the primes actually dividing \(N\), followed by \(y\) as the **last** base, apply [Bugeaud, Theorem 2.2, p. 318](https://ocu-omu.repo.nii.ac.jp/record/2010686/files/00306126-55-2-315.pdf), the rational normalized corollary of [Matveev, Theorem 2.1 and (1.3)](https://www.mathnet.ru/links/11696330cc866d273c92c771a63da235/im314_eng.pdf). The product \(y^e/N\ne1\); its bases are multiplicatively independent. Use \(A_\ell=\max(\ell,\mathrm e)\), \(A_y=y\), coefficients \(-n_\ell,e\). The normalized parameter
\[
B=\max\{1,\max_j |b_j|\log A_j/\log y\}\ll_F 1+L/\log y\ll_F e,
\]
since \(e\log y=\log(N-x)=L+O(1)\). The theorem gives
\[
L/2\ \le\ -\log|1-y^e/N|\ \ll_F\ (\log y)\log(2e).
\]
It follows that \(e\ll_F\log(2e)\), hence that \(e\) is uniformly bounded. An unnormalized coefficient bound would not suffice here.

Fix \(e\) and write \(N=T u^e\) by reducing the valuations of \(N\) modulo \(e\). The positive integers \(T\) comprise a fixed finite list and \(u\) is \(F\)-supported. Put \(\alpha=T^{1/e}\); factor the difference of powers to see
\[
|y-\alpha u|\ll_{F,e} xN^{-1+1/e}.
\]
For \(e\ge3\) this is \(O_{F,e}(N^{-1/6})\). For \(e=2\) and \(x\le N^{1/2-\epsilon}\) it is \(O_F(N^{-\epsilon})\). Apply the [algebraic-coefficient \(p\)-adic Subspace Theorem, Evertse, Theorem 1.1](https://pub.math.leidenuniv.nl/~evertsejh/dio2011-padicsubspace.pdf) to the primitive integer vector \((y,u)\). The forms at infinity are \(Y-\alpha U,U\); those at the primes of \(F\) are \(Y,U\). Their absolute-value product is at most \(|y-\alpha u|\), since \(u\prod_{\ell\in F}|u|_\ell=1\). It is less than a fixed negative power of the height for large \(N\). The resulting finitely many rational lines cannot contain an unbounded sequence: with \(y/u\) fixed, the error either grows proportionally to \(u\) or vanishes, the latter forcing \(x=0\). This proves the assertions about exponents and sizes. At most one square is in \([N-\sqrt N,N)\) for large \(N\), by the gap between consecutive squares there. If \(N\) itself is a square, the preceding square lies below that interval. Combining \(a\le1\) (respectively \(a=0\)) with part 1 gives the claimed size/nullity bounds.

## 3. Bounded branching forces singularity

Suppose along an unbounded sequence of \(F\)-supported centers a terminal is nonsingular and \(t\le T\). Then \(k\le2T+1\); the entries of \(A\) are \(O(L)\), so \(D=|\det(I-A)|\ge1\) is \(O_T((1+L)^{2T+1})\). Let \(u\) be the smallest vertex. It is at most \(\sqrt N\): some prime factor of any composite row is at most \(\sqrt N\). Every vertex is a unit mod \(N\); the factorization relations in \((\mathbb Z/N)^\times/\{\pm1\}\), multiplied by the adjugate, give \(u^{2D}\equiv1\bmod N\). For each fixed odd \(\ell\mid N\), set \(d=\operatorname{ord}_\ell(u)\le\ell-1\). LTE gives
\[
v_\ell(N)\le v_\ell(u^d-1)+v_\ell(2D/d)\ll_F 1+\log u+\log(2D).
\]
For \(2\mid N\) use \(v_2(u^{2D}-1)=v_2(u^2-1)+v_2(D)\). Summing yields \(\log u\gg_F L\) for large \(N\). Thus all entries of \(A\) are bounded in terms of \(F,T\), and so is \(D\).

Pass to fixed \(D\). For each \(\ell\in F\), choose a nearest \(2D\)-th root of unity \(\zeta_\ell\) to \(u\) in the algebraic closure of \(\mathbb Q_\ell\). The roots are distinct; if one is closer than their minimum separation all the other distances are fixed up to bounded factors, and otherwise all distances are bounded below. Thus \(|u-\zeta_\ell|_\ell\ll_{D,\ell}|u^{2D}-1|_\ell\). Fix the choices by subsequencing. Apply the same Subspace Theorem to \((u,1)\), coordinates at infinity, and \(X-\zeta_\ell Y,Y\) at \(\ell\in F\). Its product is \(O_{D,F}(u/N)\le O(N^{-1/2})\). A rational line forces constant \(u\), contradicting its growth. This rules out every bounded-\(t\) nonsingular branch. The same argument applies to small-seed closures if needed.

## 4. The singular two-mixed case

In a terminal with \(t\ge1\), pure vertices cannot form a directed cycle, which would have no exit to a mixed vertex. Repeatedly replace each pure row by its one successor, multiplying the return exponents, to form the nonnegative integer first-return matrix \(M\) on the mixed vertices. The kernel of \(I-M\) is isomorphic to that of \(I-A\). \(M\) is irreducible, and each row sum is at least two because each starting mixed row has at least two distinct factors and multiplicities do not decrease upon following them. If \(t=0\), the terminal is itself a pure cycle and its \(I-A\) determinant is \(1-\prod e\ne0\). If \(t=1\), \(M\) has a single entry at least two and hence is likewise nonsingular.

For \(t=2\), suppose \(\nu>0\). Write \(p,q\) for the mixed vertices. The positive off-diagonal entries of \(M\) give
\[
(M_{pp}-1)(M_{qq}-1)=M_{pq}M_{qp}>0.
\]
Both diagonal entries must be at least two: if both are zero, the off-diagonal entries are both one, contradicting the row-sum bound. There are no physical loops (a prime vertex does not divide \(N\)). Each positive diagonal therefore needs a pure predecessor pointing to its own mixed vertex. The two pure predecessors are distinct. But \(b\le t-\nu\le1\), and part 2 gives \(a\le1\). Hence these are the only pure rows, one large \(R>\sqrt N\), one small \(S\le\sqrt N\); after interchanging \(p,q\),
\[
N-R=p^a,\quad a\ge2,\qquad N-S=q^2.
\]
Here the letter \(a\) now denotes the exponent. Both \(p,q\le\sqrt N\). Each mixed vertex must hit its own predecessor directly or its diagonal would vanish. Thus \(R\mid N-p,\ S\mid N-q\). We have \(R\ge q+2\) by oddness and \(S<2q\) from \(q^2=N-S\) for large \(N\), so \(Rq\ge q^2+2q>N\). The row of \(p\) cannot also use \(q\); its second distinct factor must be \(S\). By part 2, \(S>N^{1/3}\) for large \(N\), and \(RS^2>N\), so \(N-p=RS\).

Now \(S\mid N-q\) and \(N-S=q^2\) imply \(S\mid q(q-1)\); since \(S\ne q\), \(q\equiv1\bmod S\). Also \(S\mid N-p\), whence \(p\equiv q\equiv1\bmod S\) and \(p>S\). On the other hand, \(N-p=RS\) and \(N-R=p^a\) give
\[
R(S-1)=p^a-p.
\]
The distinct prime \(p\) does not divide \(R\), so \(p\mid S-1\), forcing \(S>p\). This contradiction completes the exclusion.

Every finite nonempty all-composite forward closure contains a terminal; the terminal conclusion therefore applies there as well, even when the starting seed need not itself lie in it. It does not imply that any specified orbit contains a prime complement.