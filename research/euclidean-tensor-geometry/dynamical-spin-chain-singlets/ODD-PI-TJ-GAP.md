# The odd \(\pi\)-twisted t–J gap: weak and strong coupling and the three-site transition

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review claimed.

Use the deformed spin-one \(t\)–\(J\) chain in [Hagendorf §4.2](https://arxiv.org/pdf/1207.0357#page=36). In the [preceding kernel and gap proof](DEFORMED-TJ.md) the only missing equality regime was odd \(N\ge3\), twist \(\pi\), and \(|\zeta|>1\). The gap \(\Delta_N(\zeta)\) here is the smallest nonzero eigenvalue of the **full** local Hamiltonian, without projection to a special momentum sector. Set
\[
t=\zeta^2-1>0,\quad c=\zeta^2+1,\quad L=N-1,\qquad
P_N(t)=4+2t(1-\cos(\pi/N)).
\]

- At each fixed odd \(N\), \(\Delta_N=P_N(t)\) for \(0<t\le1/(16N^2)\).
- At each fixed odd \(N\), for all sufficiently large \(|\zeta|\) the first excitation has one hole and one minority spin among the remaining spins. Its exact gap is the smallest eigenvalue of the size-\(L\) matrix \(tA_1+\operatorname{diag}(6+2\zeta,8,\ldots,8,6-2\zeta)\), with \(A_1\) the cycle Laplacian whose edges have weight 2 on the path \(1,\ldots,L\) and weight 1 on the closing edge. Keep the closing edge even at \(L=2\), where it is parallel to the path edge.
- For all \(|\zeta|>1\), \(\Delta_N\le8-4/(N-1)\). For fixed odd \(N\), \(\Delta_N=8-8/N+O_N(|\zeta|^{-2})\) in the strong limit. For fixed finite \(|\zeta|>1\), the odd-length limit is instead \(4\). The two iterated limits are \(4\) and \(8\).
- At \(N=3\) the exact answer is
\[
\Delta_3(\zeta)=
\min\!\left(\zeta^2+3,\ 3(\zeta^2+1)-\sqrt{4\zeta^2+9(\zeta^2-1)^2}\right).
\]
The crossover is at \(\zeta^2=9/5\). An all-coupling formula at general odd \(N\) is not asserted.

## One-hole gauge and finite matrix

Use the basis \(X,Y,h\) and two-site blocks of the [preceding proof](DEFORMED-TJ.md). A mixed particle bond \(XY,YX\) has diagonals \(c-2\zeta,c+2\zeta\), respectively, and swap entry \(+t\). Particle–hole bonds have diagonal \(c\) and hop amplitude \(-t\); at the \(\pi\) seam the hole swap changes to \(+t\). Hole number and particle content are conserved.

In a one-hole sector with \(k\) spins \(Y\) among the \(L\) particles, fix a linear ordering at the seam, delete the hole, and multiply each configuration by \((-1)^{I}\), where \(I\) counts \(X/Y\) inversions. For an ordinary particle swap the parity changes once. For an unlike particle swap across the seam it changes by \(L-1\), odd; this follows because the two endpoints pass all the internal particles of opposite type plus each other. Thus all particle swaps become \(-t\). Ordinary hole hops do not change the order. When the hole crosses the seam, the particle order rotates by one, moving either an \(X\) across \(k\) opposite letters or a \(Y\) across \(L-k\), the same parity as \(k\), since \(L\) is even. For odd \(k\), this cancels the seam sign, so every off-diagonal entry is nonpositive. The configuration graph is connected by first moving the hole and then sorting by particle swaps in an open segment. The matrix in this gauge is invariant under ordinary spatial translation: the bond diagonals repeat by orientation, and all swap signs now agree. By Perron–Frobenius (applied to a large scalar minus the Hamiltonian), the lowest vector is strictly positive and unique, hence translation invariant in this gauge.

Read the relative particle word \(s=(s_1,\ldots,s_L)\) beginning after the hole, where \(s_i={\bf1}_{Y}\). Let \(w(s)\) count the unequal bonds inside the open word and \(d(s)=s_1-s_L\). On words of fixed \(k\) the relative Hamiltonian is
\[
t A_k+4+2w(s)+2\zeta d(s).
\]
Here \(A_k\) is the graph Laplacian from all open-word adjacent unequal swaps and from the two cyclic shifts (one for each hop direction). Multiple edges count. The diagonal of the full Hamiltonian in these coordinates is \(2c+cw+2\zeta d\), and the Laplacian diagonal is \(t(2+w)\); their difference is \(4+2w+2\zeta d\). The sole one-hole no-hop transitions would come from constant relative words, absent at odd \(k\). For \(k=1\), each interior path edge gets one adjacency swap and one hop, while the closing edge gets only the hop. Thus \(A_k=A_1\) as specified, with one-wall endpoints and two-wall interior states. Uniform constant coordinates have expectation \(8-4/L\) at \(k=1\), proving the all-coupling upper bound.

## Strong perturbation and sector exclusion

In the uniform probability inner product on \(k\)-subsets, the kernel of \(A_k\) is the constants. After division by \(\zeta^2\), expand in \(\epsilon=1/\zeta\) as \((1-\epsilon^2)A_k+2\epsilon d+\epsilon^2(4+2w)\). The simple eigenvalue at zero is analytic. The first-order term vanishes by symmetry. At second order, solving the first-order eigenvector correction on the orthogonal complement of constants gives
\[
4+2\mathbb E w-4\langle d,A_k^+d\rangle.
\]
All odd orders vanish under reversing the relative word, which conjugates the matrix at \(\epsilon\) to that at \(-\epsilon\).

On linear occupancy functions \(\sum_i u_i s_i\), \(A_k\) acts on the coefficient vector by the weighted cycle \(A_1\): each local exchange acts as its coefficient transposition, and the two shifts add the usual cycle Laplacian. For zero-sum \(u,v\), their occupancy functions have covariance \(k(L-k)/(L(L-1))\) times \(u\cdot v\), using \(\Pr(s_i=s_j=1)=k(k-1)/(L(L-1))\) for \(i\ne j\). Hence
\(\langle d,A_k^+d\rangle=\frac{k(L-k)}{L(L-1)}(e_1-e_L)^\top A_1^+(e_1-e_L)\).
The last quadratic form is the endpoint effective resistance: the closing unit resistor is in parallel with the path of resistance \((L-1)/2\), giving \((L-1)/(L+1)\). This also applies at \(L=2\). The mean \(w\) is \(2k(L-k)/L\). The lowest energy in odd \(k\) therefore tends to
\[
4+\frac{4k(L-k)}{L+1},
\]
with error \(O_N(\zeta^{-2})\). All other eigenvalues of the relative block diverge as the leading Laplacian has a simple kernel. The global lowest in that odd-\(k\) sector remains the relative one by positivity at each coupling. This limit is minimal at \(k=1,L-1\); both have exactly the same spectrum by reflection followed by exchanging \(X,Y\).

For the other sectors inspect the leading Hamiltonian divided by \(\zeta^2\). For a signed-swap Laplacian every edge imposes equality of its endpoint amplitudes up to a sign in a null vector, so a connected sector with a negative closed walk has strictly positive smallest eigenvalue.

- In the even-\(k\) one-hole sector the same inversion gauge leaves a negative seam sign on hole hops, all other edges having positive transport sign. Move the hole once around the ring, then restore the rotated particle word by ordinary swaps with the hole fixed, using the open ordering away from the seam. This makes a negative closed walk.
- In a mixed no-hole sector the leading matrix is the signless binary-swap Laplacian. A negative walk can be obtained by executing one clockwise occupied-to-empty move on each bond and returning to the original state. For each site initially occupied, require its outgoing move before its incoming move; for each initially empty site require the opposite. These comparisons orient the cycle on move events acyclically, because both site types occur. In a topological order the outgoing site is occupied and the incoming site is empty at every executed move, by the two local precedences. Each edge sign is negative, and the length \(N\) is odd. The binary adjacent-swap graph is connected.
- Two or more holes have energy at least \(4\) times their number by the existing gap argument, hence at least \(8\), already greater than \(8-8/N\).

It follows that at sufficiently strong coupling the gap is precisely the size-\(L\) eigenvalue stated above. The fixed-\(\zeta\) thermodynamic limit follows from \(4\le\Delta_N\le P_N(t)\); the strong-coupling limit taken first follows from the proved asymptotic. The two orders do not commute.

## Weak edge of the missing regime

Spectrum is invariant under \(\zeta\mapsto-\zeta\), by exchanging \(X,Y\), so take \(\zeta=\sqrt{1+t}\). At \(t=0\) the mixed-particle bond is diagonal, vanishing on \(XY\) and equal to \(4\) on \(YX\). In every one-hole mixed-content sector the minimum diagonal value is \(4\), attained exactly on the open words \(XX\cdots XYY\cdots Y\) starting after the hole. An adjacent particle swap cannot preserve such a word, and a hole hop rotates it by one and also cannot preserve it. Thus the coefficient of \(t\), compressed to this minimum eigenspace, is \(2I\): the hole diagonal \(2c\) contributes \(2\) and \((\zeta-1)^2=O(t^2)\) on the single \(XY\) bond has no linear contribution. In a mixed no-hole sector with each count at least two, the minimizers at \(t=0\) are the two-wall words of energy \(4\). A mixed-bond swap creates four walls, so again the first-order compression is \(2I\), from the symmetrized diagonal \(cw\). Each of these sectors therefore has minimum \(4+2t+O_N(t^2)\), by the usual first-order finite-matrix perturbation across the positive gap at \(t=0\) (equivalently use the Schur complement on the minimum eigenspace). The sectors with two or more holes stay at least \(8\). The one-flipped-spin and pure-background one-hole waves both have exact minimum \(P_N(t)\), with strictly smaller linear coefficient since \(\cos(\pi/N)>0\). One explicit common window is \(0<t\le1/(16N^2)\). On each competing mixed sector the absolute row-sum bound gives \(\|H(t)-H(0)\|\le4Nt\) (at most \(N\) swaps in any row, hole diagonal change \(2t\), and \(2|\sqrt{1+t}-1|\le t\)). The minimum-space diagonal compression is at least \(E_0=4+2t\), as above, while its orthogonal complement has lower bound \(8-4Nt\). Put \(g=8-4Nt-E_0>3\). Completing the square in the two-block Rayleigh quotient with off-diagonal norm at most \(4Nt\) gives the lower bound \(E_0-(4Nt)^2/g\). The loss is at most \(t/3\), smaller than \(2t\cos(\pi/N)\) for every odd \(N\ge3\). This proves the stated explicit weak-coupling branch.

## Three sites

At \(N=3\) there are no other mixed no-hole sectors, and the odd-\(k\) one-hole sector has only \(k=1\). Its size-two matrix has diagonal \(3c\pm2\zeta\) and off-diagonal \(-3t\), so its smallest eigenvalue is \(3c-\sqrt{4\zeta^2+9t^2}\). The other one-hole or one-flipped candidates give \(\zeta^2+3\). Multiple holes have bound \(8\), whereas the size-two branch is at most \(6\) by the constant trial. Equating the two candidates for \(u=\zeta^2>1\) gives \(4u+9(u-1)^2=4u^2\), or \((5u-9)(u-1)=0\), and the smaller branches are as stated.

The [independent numerical checker](verify-odd-pi-gap.js) uses untransformed Hamiltonian blocks. It is supplementary and not part of the proofs. For related (distinct) periodic exclusion spectra see [Nakerst–Prosen–Haque](https://arxiv.org/abs/2402.00662); no priority claim is made.
