# A second proof of the single-effect inequality

For $0<l<u$, put $C=lI+(u-l)B$ with $0\le B\le I$ and $b=\sqrt{lu}-l$. We show directly that every Hermitian $T$ satisfies
$$
 \lVert C^{1/2}TC^{1/2}\rVert_1\ \ge\ l\operatorname{Tr}|T|+2b\operatorname{Tr}(B|T|).
$$
This is (4) of the [main proof](PROOF.md) with $l=e$ and $u=e+s$. It suffices to consider projections, but the dilation must preserve the *trace norm*, not just the compression of $C$.

On two copies of the original space take the projection
$$
 Q=\begin{pmatrix}B&\sqrt{B(I-B)}\\
                  \sqrt{B(I-B)}&I-B\end{pmatrix}
$$
and let $Jv=(v,0)$. Write $\widehat C=lI+(u-l)Q$. Since $J^*\widehat C J=C$, the map $V=\widehat C^{1/2}JC^{-1/2}$ is an isometry. Therefore $\widehat C^{1/2}JTJ^*\widehat C^{1/2}=V C^{1/2}TC^{1/2}V^*$ has the same trace norm. The other side also remains unchanged because $|JTJ^*|=J|T|J^*$. It now suffices to take $B=Q$ a projection.

Let $S=\operatorname{sgn}T$, assigning either sign on the kernel so $S^2=I$, and $P=(I+S)/2$. The pair of projections $P,Q$ splits into simultaneous eigenlines and two-dimensional blocks. To see this, diagonalize $PQP$ on $\operatorname{ran}P$. For each orthonormal eigenvector $v$ of eigenvalue $0<x<1$, use the unit partner $(I-P)Qv/\sqrt{x(1-x)}$. The identity $Q^2=Q$ makes these partners orthonormal and gives, on each block,
$$
 S=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\qquad
 Q=\begin{pmatrix}x&\sqrt{xy}\\\sqrt{xy}&y\end{pmatrix},\qquad y=1-x.
$$
The eigenvalues $0,1$ give simultaneous eigenvectors; on the remaining subspace of $\ker P$ diagonalize $Q$. Although $T$ need not preserve these blocks, its compression to each two-dimensional block is $\operatorname{diag}(a,-c)$ with $a,c\ge0$ because $T$ has the specified signs on the two spaces of $S$. The compression of $|T|$ is $\operatorname{diag}(a,c)$.

We will produce a block-diagonal $D$ with $-C\le D\le C$ for which $\operatorname{Tr}(DT)$ equals the asserted lower bound. The support of this interval is $\lVert C^{1/2}TC^{1/2}\rVert_1$. Set $d_0=u-l$ and $\delta=\sqrt u-\sqrt l$. On a simultaneous eigenline of $Q$ of eigenvalue $q\in\{0,1\}$ take $D=S(l+2bq)$, feasible because $d_0-2b=\delta^2$.

On a nontrivial block, the entries of $C$ are $c_1=l+d_0x$, $c_2=l+d_0y$, and $t=d_0\sqrt{xy}$ off diagonal. Prescribe the diagonal of $D$ to be $(w_1,-w_2)$, where $w_1=l+2bx$ and $w_2=l+2by$. Its trace pairing on the block is exactly $aw_1+cw_2$. A real off-diagonal $z$ works if and only if
$$
 |t+z|\le\sqrt{(c_1+w_1)(c_2-w_2)},\qquad
 |t-z|\le\sqrt{(c_1-w_1)(c_2+w_2)}.
$$
Indeed the diagonal factors are nonnegative, so these are the two remaining determinant inequalities for $C\pm D$. The intervals in $z$ meet precisely when $2t$ is at most the sum of their radii. Divide by $\delta\sqrt{xy}>0$ and put $K=d_0+2b$; the required inequality becomes
$$
 2(\sqrt l+\sqrt u)\ \le\ \sqrt{K+2l/x}+\sqrt{K+2l/y}.
$$
The function $h(x)=\sqrt{K+2l/x}$ is convex for $x>0$: it is the Euclidean norm of $(\sqrt K,\sqrt{2l}\,x^{-1/2})$, a convex nondecreasing function of the nonnegative second coordinate composed with a convex function. Since $x+y=1$, Jensen's inequality gives the right side at least $2h(1/2)=2(\sqrt l+\sqrt u)$. Thus a feasible $D$ exists on each block. Traces against block-diagonal matrices see no off-block entries, proving the inequality after summation. The degenerate cases $l=u$ and $l=0$ are immediate. ∎
