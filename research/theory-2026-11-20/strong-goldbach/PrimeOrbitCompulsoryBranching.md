# Compulsory genuinely branching prime-factor rows

Let \(N\) be even, let \(L=\log N\), and in the directed unit-prime factor graph use vertices the odd primes \(3\le z\le N-3\) coprime to \(N\), with arc \(z\to y\) of multiplicity \(e=v_y(N-z)>0\). The actual contribution is the integer \(y^e\), not just its prime base. "Mixed" means the complete row has at least two **distinct** prime bases; "pure" means a composite prime power row \(N-z=y^e,\ e\ge2\). A non-Goldbach terminal component below is a factor-closed strongly connected set all of whose complements are composite (an EAC in [Bożek's terminology](https://arxiv.org/abs/1909.09900)). Such components may exist even at represented centers. Signed orders refer to quotienting the unit group by simultaneous sign.

## One actual root feeding many branching rows, at every center

For any \(\epsilon>0\) and all sufficiently large even \(N\), there exists a unit prime \(x\le N^\epsilon\) with \(m\gg_\epsilon L/\log L\) distinct one-step unit prime successors \(q\in[L,4L]\), each with exact incoming multiplicity one, and **all but \(O(L/(\log L)^2)\)** of these \(q\) have either a true prime complement or genuinely mixed rows. In every such mixed row **every nontrivial divisor of \(N-q\)** has order greater than two in the full signed group \(G_N\). In particular if this root does not reach a genuine pair, it reaches \(\gg_\epsilon L/\log L\) distinct true branching rows after one step, with two or more surviving actual contributions apiece. This does not assert the outputs of different rows are all distinct, or that \(x\) can be prescribed.

At a center with \(P=2^{v_2(N)}\) or \(P=3^{v_3(N)}\), every nontrivial divisor from these rows even has signed local order \(\ge P/(2\sqrt N+1)\) when \(P>1\). So on \(P\ge N^{1/2+\delta}\) every one of their actual output contributions has order \(\gg N^\delta\). The two prime bases in a mixed row are not assumed to have equal orders.

**The short-interval count.** Over the **whole** fixed center, the number \(k\) of prime inputs \(z\le\sqrt N\) with composite prime-power complements is
\[
                            k\ll {L\over(\log L)^2}.                 \tag{1}
\]
All complements lie in \([N-\sqrt N,N)\). Distinct prime-power rows in this interval have distinct bases: two different powers of the same odd prime differ by at least a factor 3. Their exponents \(e_i\ge2\) are pairwise coprime, since a shared prime exponent \(h\) would give distinct \(h\)-th powers with gap at least \(2(N-\sqrt N)^{1-1/h}>\sqrt N\). This is the power-gap observation of [the pure-cycle theorem](EACPureCycleHeight.md) and does not require a cycle. For \(k\) large at least \(k/2\) exponents are \(\ge c k\log k\): the smaller ones must have distinct prime divisors \(\le c k\log k\), of which there are fewer than \(k/2\) by the usual prime-count upper bound. Their distinct corresponding bases are all \(\le\exp(L/(c k\log k))\), hence \(k\log^2 k\ll L\). If \(k\ge\sqrt L\) this implies (1), and otherwise (1) is automatic.

Use the actual one-root CRT/Linnik construction of [the preceding packing theorem](PrimeOrbitSingleRootPacking.md) to obtain the stated fan. It is important here that its size is of order \(L/\log L\), rather than an unspecified growing number. Estimate (1) disposes of only a vanishing fraction. If an immediate successor has a prime complement then the orbit has reached a genuine pair; otherwise the surviving successors are genuine mixed rows.

**The full-group square test.** Take *any* unit prime input \(z<\sqrt{N/2}\) and any divisor \(d>1\) of \(N-z\). Suppose that the signed order of \(d\bmod N\) divides two. Then \(d^2\equiv\pm1\bmod N\) implies \(d\ge\sqrt{N-1}\). Thus \(b=(N-z)/d<\sqrt N\). In the plus case \(b^2\equiv z^2\bmod N\) gives \(b=z\), forcing \(z\mid N\), impossible. In the minus case \(b^2+z^2\equiv0\bmod N\) gives \(b^2+z^2=N\), since both are positive and their sum is less than \(2N\). As \(b\mid N-z\), it follows that \(b\mid z(z-1)\). The unit condition gives \((z,b)=1\), so \(b\mid z-1\). But \(b^2=N-z^2>z^2\). This contradiction needs no primality of \(b\).

**The dyadic and triadic divisor test.** Let \(P=\ell^a\mid N\) for \(\ell=2\) or \(3\), \(P>1\). For any odd unit \(d>1\) dividing \(N-z\), if \(r\) is its order in \((\mathbb Z/P)^\times/\{\pm1\}\) and \(B=P/r\), then \(d\equiv\pm1\bmod B\). For \(\ell=2\), choose the sign of \(d\) congruent to 1 modulo 4 (the cases \(a\le2\) are automatic); for \(\ell=3\), choose that sign modulo 3. Lifting the exponent gives \(r=\ell^{\max(0,a-v_\ell(\pm d-1))}\) in each case. If \(B>z+\sqrt N+1\), then \(d\ge B-1>\sqrt N\), so \(0<b=(N-z)/d<\sqrt N\), and \(b\equiv\pm z\bmod B\). As \(B>b+z\), this forces \(b=z\), forbidden by \(z\nmid N\). Therefore
\[
                    r\ \ge\ {P\over z+\sqrt N+1}.                 \tag{2}
\]
This applies to entire divisors, not merely prime factors or the exponent-free base. Formula (2) is useful when \(P\) exceeds the square-root scale and does not contradict maximal-channel traps in the lower-depth regime.

## Inside an actual terminal component

Let \(t\) be the number of its genuinely mixed rows and \(A=(v_{p_j}(N-p_i))\) its full exponent matrix on the \(k\) distinct prime labels. There are at most \(t\) labels larger than \(\sqrt N\): each must occur as a target by strong connectivity, each such target comes from a mixed row (a pure output is \(\le\sqrt N\)), and one row cannot have two distinct such large prime factors. Thus the number of pure input labels is at most \(O(L/(\log L)^2)+t\) by (1). It follows that
\[
 k\ll L/(\log L)^2+t,\qquad
 \log|\det(I-A)|\ll L/\log L+t\log L\quad\text{if }\det(I-A)\ne0. \tag{3}
\]
Indeed every row of \(I-A\) has Euclidean norm \(\le1+L/\log3\) by the row sum of exponents, so (3) follows from Hadamard. The signed residues of component labels obey \([p_i]=\prod_j[p_j]^{A_{ij}}\). The adjugate identity therefore shows that \(D=|\det(I-A)|\) annihilates all of them when \(D\ne0\); in ordinary unsigned residues \(N\mid p_i^{2D}-1\).

Some label \(u\le\sqrt N\) occurs as a factor of any composite row. For \(P=2^{v_2N}\) or \(3^{v_3N}>1\), its signed local order is at least \(P/(u+1)\), by the same local formula (here simply \(P/r\mid u\pm1\)). If \(P\ge N^{1/2+\delta}\), (3) yields the **all-size terminal alternative**
\[
      \det(I-A)=0\qquad\hbox{or}\qquad
      t\gg_\delta {\log N\over\log\log N}.                       \tag{4}
\]
No component size or prescribed seed is assumed. The singular alternative is genuine and has not been eliminated. This refines the [dyadic order/Smith mechanism](EACDyadicSmith.md) by counting genuine *mixed rows* rather than total labels.

**No pure components on centers with substantial small-prime part.** For \(t=0\) the component is a directed cycle with every exponent \(\ge2\); thus \(\det(I-A)=1-\prod_i e_i\ne0\). The effective [pure-cycle height theorem](EACPureCycleHeight.md) guarantees a label \(u\) satisfying \(\log u\ll L/\log L\), uniformly without a size bound. By (3), also \(\log(2D)\ll L/\log L\). For \(Y\ge2\) write \(N_{\le Y}=\prod_{\ell\le Y}\ell^{v_\ell N}\) over primes. For each odd \(\ell\mid N\), ordinary lifting the exponent applied to \(N\mid u^{2D}-1\), using the order of \(u\bmod\ell\) which divides both \(2D\) and \(\ell-1\), gives
\[
 v_\ell(N)\log\ell\ \le\ (\ell-1)\log u+v_\ell(2D)\log\ell .
\]
At two use \(v_2(u^{2D}-1)=v_2(u^2-1)+v_2(D)\le 2\log u/\log2+v_2(D)\). The contributions from the valuations of \(2D\) cost at most \(\log(2D)\) **in total**. Since \(\sum_{\ell\le Y}(\ell-1)\ll Y^2/\log(2Y)\), we obtain
\[
           \log N_{\le Y}\ll
       \left(1+{Y^2\over\log(2Y)}\right){L\over\log L}             \tag{5}
\]
with an absolute constant, uniformly in \(Y\). In particular, along any unbounded sequence admitting a pure EAC, even \(N_{\le\sqrt{\log\log N}}=N^{o(1)}\). Thus an actual closed nongoldbach component at sufficiently large centers with that smooth part \(\ge N^\delta\) must have a genuine branch.

**Two branches for a fixed smooth alphabet.** If exactly one row is mixed, delete its vertex. The remaining pure subgraph is acyclic: a surviving cycle would already be factor-closed and could not communicate with the mixed vertex. Every pure row has one successor, and following such successors returns to the mixed vertex. Eliminate the pure coordinates in \(I-A\); the pure block has determinant 1 by acyclicity, and the one-by-one Schur complement is \(1-E\), where \(E\) is the sum of multiplicity products over first returns from the mixed vertex. Each of its at least two initial arcs supplies a return of positive weight, so \(E\ge2\). Hence \(D\ne0\), and \(\log(2D)\ll L/\log L\) by (3). [The one-mixed-row theorem](EACOneMixedProjector.md) proves \(\log u=o(L)\) for the minimum label along any unbounded sequence, with no cardinality bound. Apply the preceding valuation inequalities at a **fixed** finite set \(F\) of primes: \(\log N_F\ll_F\log u+\log(2D)=o(L)\). Consequently at all sufficiently large \(N\) with \(N_F\ge N^\delta\), **every** genuinely closed non-Goldbach component has at least two mixed rows. This use of the qualitative one-mixed result does not supply its moving-\(Y\) analogue.

**From a prescribed small input.** On the \(2\)- or \(3\)-primary rail \(P\ge N^{1/2+\delta}\), take any unit prime \(z\le\sqrt N\), not a center-dependent choice. Follow the unique output as long as the row is a composite prime power; the successor stays \(\le\sqrt N\). No repeats can occur before a genuine pair or a mixed row: a repeat would create a closed pure-power cycle, excluded by (5). By (1) there are only \(O(L/(\log L)^2)\) such steps. Thus this actual seed either reaches a genuine prime complement or reaches a mixed small input with at least two distinct contributions, **all** of whose signed local orders are \(\gg N^\delta\) by (2). This is compulsory high-order branching, not compulsory prime-pair existence.

## A related exact check on unary rows after removing two-torsion

For arbitrary even \(N\), keep just arcs with \([y]^{2e}\ne1\) in the *full* signed group. The exact identity \([z]^2=\prod_{\rm kept}[y]^{2e}\) guarantees a successor from every active \([z]^2\ne1\), and kept targets remain active. An all-composite row with exactly one kept arc of multiplicity one must be \(N-z=yd\), with one discarded prime-power contribution \(d>1\): there must be one since otherwise the complement is prime; none can repeat as separate bases, because each discarded contribution is at least \(\sqrt{N-1}\) and two do not fit. Hence \(y<\sqrt N\) and \([y]^2=[z]^2\). If \(z<\sqrt N\) too, the plus sign gives \(z=y\), impossible as \(z\nmid N\); the minus sign forces \(z^2+y^2=N\), and \(y\mid z(z-1)\) forces \(y\mid z-1\), hence \(y<z\).

In particular **three consecutive** unary multiplicity-one rows with composite complements are impossible. After the first step the next three labels \(u,v,w\) are all \(<\sqrt N\); the last two steps would force \(u^2+v^2=v^2+w^2=N\), hence \(u=w\), while each forces strict decrease. Every all-unary cycle without a prime complement therefore has product of live multiplicities \(E>1\); around it, each signed square has order dividing \(E-1\le (L/\log3)^k-1\) for cycle length \(k\). As a separate trichotomy, start at a *fixed* unit odd prime \(p\) at targets with \(a=v_2N\to\infty\): \([p]^2\) has dyadic signed order \(\gg_p2^a\). Until a reached row has a genuine prime complement or at least two retained full-group outputs, its unique successor has at least its predecessor's dyadic signed-square order by the exact row identity. If such rows continue forever, their eventual cycle has \(k\gg_p a/\log\log N\), by the preceding divisibility. This trichotomy alone does not exclude its long-cycle alternative. In particular the proof does not identify different large primes merely because their signed squares agree.