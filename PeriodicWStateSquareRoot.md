# A uniform square-root upper bound for the periodic uniform W-state

**Yongxian Zhang.** Research note (AI-assisted proof development and verification).

Let \(d(n)\) be the least dimension of complex matrices \(A_0,A_1\) such that the trace of a length-\(n\) word is \(1/\sqrt n\) for words with exactly one \(A_1\) and zero for all other words. We prove
\[
 d(n)\le \sqrt n+O(n^{1/4+o(1)}).
\]
In the rank-one excitation model (\(\operatorname{rank}A_1=1\)), and also without a rank constraint when both matrices have real nonnegative entries, the minimal dimension is \((1+o(1))\sqrt n\). For \(\operatorname{rank}A_1=2\) we prove \(n\le 8D^2\), where \(D\) is the matrix dimension; this gives order \(\Theta(\sqrt n)\) in the rank-two model. The [companion lower-bound proof](PeriodicWStateOptimalAsymptotics.md) establishes the unrestricted bound \(d(n)\ge\sqrt n\), so the leading constant is also one without rank or positivity constraints.

[Klimov, Sengupta and Biamonte, arXiv:2306.16456v2](https://arxiv.org/abs/2306.16456) gave the bound \(\lfloor n/2\rfloor+1\). A [trureturing dossier](https://www.trureturing.org/research/klimov-2023-w-state-ti-mps-bond-dimension/) refutes its proposed exact optimality, records a periodic construction along \(n=D(D-1)+1\), and leaves the upper bound \(O(\sqrt n)\) for all \(n\) open. Our construction extends the same progression-of-walk-lengths mechanism to uniform \(n\). These proofs use trace and recurrence arguments, not an application of the Euclidean tensor geometry theorem.

## Construction

Suppose \(p>1\), \((p,n)=1\), \(1\le m\le n<(p+1)m\), and \(m\equiv n\bmod p\). On a directed \(p\)-cycle take start \(u\) and the vertex at distance \(m-1\) as endpoint \(v\) if \(m\le p\). If \(m>p\), attach a directed chain of length \(m-p\) at distance \(p-1\) from \(u\), with endpoint \(v\). Let \(A_0\) be the \(0/1\) adjacency matrix (row is source), and set \(A_1=E_{v,u}/\sqrt n\). The dimension is \(\max(p,m)\). The walks from \(u\) to \(v\) have exactly the lengths \(m-1+jp\), each with multiplicity one. Hence a word with \(k>0\) excitations has nonzero trace only when \(n\ge km\) and \(n\equiv km\bmod p\). Necessarily \(k\equiv1\bmod p\), and the length inequality forces \(k=1\). That word has the required trace. The all-zero word has zero trace because a closed walk lives on the cycle and \(p\nmid n\).

Put \(s=\lfloor\sqrt n\rfloor\) and set
\[
 p=s+h,\qquad m=n-(s+h)(s+1-h)=n-s(s+1)+h(h-1).
\]
The first nonnegative \(h_0\) with \(m\ge s+1\) is \(O(\sqrt s)\) and \(m=s+O(\sqrt s)\) there (the first crossing occurs by a step of size \(O(\sqrt s)\)). Within \(L=2\cdot4^{\omega(n)}\) consecutive \(h\)'s starting at \(h_0\) there is a coprime choice \((s+h,n)=1\): inclusion–exclusion counts at least \(L\phi(n)/n-2^{\omega(n)}>0\), using \(\phi(n)/n\ge 2^{-\omega(n)}\). Also \(\omega(n)=O(\log n/\log\log n)\), since the product of \(\omega(n)\) distinct primes is at least \((\omega(n)+1)!\). Consequently \(L=n^{o(1)}\), and \(p,m=\sqrt n+O(n^{1/4+o(1)})\). For all sufficiently large \(n\) we have \(m\le n\); the congruence is automatic and \((p+1)m\ge(s+1)^2>n\). Finitely many remaining \(n\) do not affect the estimate (use a directed path of length \(n-1\), with the excitation closing it).

## Rank-one and nonnegative lower bounds

Suppose \(A_1=xy^\top\). For positive \(j\) set \(c_j=y^\top A_0^{j-1}x\); a word whose successive cyclic gaps (including one excitation per gap) have lengths \(j_i\) has trace \(\prod_i c_{j_i}\). Since \(c_n\ne0\), Cayley–Hamilton gives a first supported \(m_0\le D\), and, applying it to \(A_0^{m_0}\), a supported \(m_1\le Dm_0\) in the residue class of \(n\bmod m_0\). If \(n>Dm_0\), the lengths \(m_1\) and \((n-m_1)/m_0\) copies of \(m_0\) give at least two excitations and a nonzero trace, a contradiction. Thus \(n\le D^2\). For nonnegative matrices one entry of \(A_1\) contributes positively to the single excitation. Retain only that entry and rescale it. Removing entries cannot turn a zero trace of a nonnegative word product into a positive trace, so the rank-one lower bound applies.

## Rank-two lower bound

Factor \(A_1=XY^\top\) with \(X,Y\) of shape \(D\times2\), and put \(C_j=Y^\top A_0^{j-1}X\) for \(j\ge1\). For positive gaps summing to \(n\), the corresponding trace is \(\operatorname{tr}(C_{j_1}\cdots C_{j_k})\). In particular \(\operatorname{tr} C_n\ne0\); every product with \(k\ge2\) and total weight \(n\) has trace zero, with weight \(\sum j_i\). Cayley–Hamilton implies that all \(C_j\) are in the span of \(C_1,\ldots,C_D\).

**Padding with idempotents.** Let \(E_i\) be idempotents each proportional by a nonzero scalar to a word in the \(C_j\)'s of weight \(w_i\); let \(w=\sum_i w_i\). Write \(n=r+Jw\) with \(1\le r\le w\). For every \(0\le j<J\),
\[
  \operatorname{tr}(C_{r+jw}E_1\cdots E_k)
 =\operatorname{tr}(C_{r+jw}E_1^{J-j}\cdots E_k^{J-j})=0.
\]
The second trace is proportional to a multi-excitation trace of total weight \(n\). The left sequence satisfies the recurrence of \(A_0^w\), of order at most \(D\). If \(n>Dw\) then \(J\ge D\), so the next value \(\operatorname{tr}(C_nE_1\cdots E_k)\) is zero.

**Invertible case.** If \(C_i\) is invertible for some \(i\le D\), write \(n=r+Ji\) with \(1\le r\le i\). The sequence \(\operatorname{tr}(C_{r+ji}C_i^{J-j})\) vanishes for all \(0\le j<J\). It is a linear observation of iterates under \(B\mapsto A_0^i B C_i^{-1}\), starting from \(B=A_0^{r-1} X C_i^J\) in dimension \(2D\). Thus \(n>2Di\) gives \(J\ge2D\) and forces \(\operatorname{tr}C_n=0\), impossible.

It suffices now to assume every nonzero \(C_i\), \(i\le D\), has rank one. If they have a common invariant line, use a common upper triangular basis. Each active diagonal coordinate has a corresponding \(C_i\) which is nonzero in that coordinate and zero in the other (rank one). This \(C_i\) rescales to an idempotent of weight \(i\le D\). Pairing with it via the trace isolates the corresponding diagonal entry of \(C_n\) and forces it to be zero when \(n>D^2\). Inactive coordinates of \(C_n\) are zero by linear span.

In the irreducible case write each nonzero short \(C_i=u_iv_i\), with \(v_i\) a row. For each \(i\), the rows \(\{v_i\}\cup\{v_i C_\ell:\ell\le D\}\) span the row plane, since otherwise their line and its column annihilator would be invariant. Therefore every endpoint product \(u_i v_j\) is proportional either to \(C_i C_j\) or to some \(C_i C_\ell C_j\). The columns \(u_i\) span the plane by irreducibility, and the same holds for the rows \(v_i\). For each column \(u_i\) there exists a row \(v_j\) with \(v_j u_i\ne0\), and conversely for each row. Rescale these endpoint products to rank-one idempotents of weight at most \(3D\); their images span the column plane and their rows span the row plane.

There is at least one rank-one idempotent \(E\) of weight at most \(2D\). Indeed some \(C_i\) either has nonzero trace, or two nilpotent rank-one \(C_i,C_j\) have distinct image lines and hence \(\operatorname{tr}(C_iC_j)=(v_i u_j)(v_j u_i)\ne0\). Fix a basis with \(E=E_{11}\). If the family of accessible idempotents contains a \(P\) with \(P_{22}\ne0\), then \(E_{22}\) is proportional to \(P-EP-PE+EPE\), in the span of \(P,EP,PE,E\). If every accessible idempotent has \((2,2)\)-entry zero, choose \(P_{21}\ne0\) and \(Q_{12}\ne0\) using the image and row spans. Then \((PQ)_{22}=P_{21}Q_{12}\ne0\), so \(E_{22}\) is in the span of \(PQ,EPQ,PQE,E\). In each case the identity is in the span of products of idempotents of weight at most \(8D\). If \(n>8D^2\), padding makes every pairing of \(C_n\) with those products zero, forcing \(\operatorname{tr}C_n=0\). This proves \(n\le8D^2\).

An exact-rank-two upper bound is the rank-one construction direct-summed with a two-dimensional block \(A_0=0,\ A_1=E_{12}\), whose length-\(n\) traces vanish for \(n\ge2\). More generally, in the invertible case the same argument for excitation rank \(a\) has recurrence order \(Da\); a nonsingular \(Y^\top A_0^{i-1}X\) gives \(n\le Dai\).
