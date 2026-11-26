# The odd \(\pi\)-twisted t–J gap: weak and strong coupling and the three-site transition

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review claimed.

Use the deformed spin-one \(t\)–\(J\) chain in [Hagendorf §4.2](https://arxiv.org/pdf/1207.0357#page=36). In the [preceding kernel and gap proof](DEFORMED-TJ.md) the only missing equality regime was odd \(N\ge3\), twist \(\pi\), and \(|\zeta|>1\). The gap \(\Delta_N(\zeta)\) here is the smallest nonzero eigenvalue of the **full** local Hamiltonian, without projection to a special momentum sector. Set
\[
t=\zeta^2-1>0,\quad c=\zeta^2+1,\quad L=N-1,\qquad
P_N(t)=4+2t(1-\cos(\pi/N)).
\]

- For every coupling in this regime the gap is attained in a **one-hole** sector, by the [shortest-cycle argument](CIRCULAR-EXCLUSION-CYCLES.md#consequence-for-the-odd-pi-twisted-deformed-tj-chain). Its exact finite-block reduction is below.
- For **every** odd \(N\ge5\), \(\Delta_N=P_N(t)\) throughout \(0<t\le1\), i.e. \(1<|\zeta|\le\sqrt2\). At \(N=3\), this branch holds through \(t=4/5\) below.
- At each fixed odd \(N\), for all sufficiently large \(|\zeta|\) the first excitation has one hole and one minority spin among the remaining spins. Its exact gap is the smallest eigenvalue of the size-\(L\) matrix \(tA_1+\operatorname{diag}(6+2\zeta,8,\ldots,8,6-2\zeta)\), with \(A_1\) the cycle Laplacian whose edges have weight 2 on the path \(1,\ldots,L\) and weight 1 on the closing edge. Keep the closing edge even at \(L=2\), where it is parallel to the path edge.
- For all \(|\zeta|>1\), \(\Delta_N\le8-4/(N-1)\). For fixed odd \(N\), \(\Delta_N=8-8/N+O_N(|\zeta|^{-2})\) in the strong limit. For fixed finite \(|\zeta|>1\), the odd-length limit is instead \(4\). The two iterated limits are \(4\) and \(8\).
- At \(N=3\) the exact answer is
\[
\Delta_3(\zeta)=
\min\!\left(\zeta^2+3,\ 3(\zeta^2+1)-\sqrt{4\zeta^2+9(\zeta^2-1)^2}\right).
\]
The crossover is at \(\zeta^2=9/5\).
- At \(N=5\) the gap equals the smaller of \(P_5(t)\) and the smallest eigenvalue of the four-dimensional one-minority matrix above, at **every** coupling. The two branches cross just once, at \(t\approx5.67570853\), equivalently \(|\zeta|\approx2.58373925\). The exact cubic for the crossover is below. 
- At \(N=7\) the same two-branch description holds with the six-dimensional one-minority matrix. Its unique crossover is at \(t\approx13.79749431\), equivalently \(|\zeta|\approx3.84675114\). 
- The [finite rational certificate](ODD-PI-TJ-FINITE-CERTIFICATES.md) extends the same exact two-branch formula to all odd \(N\le41\), at every coupling. At arbitrary length, [all even mixed contents are excluded analytically](ODD-PI-TJ-FINITE-CERTIFICATES.md#analytic-even-content-exclusion-at-every-odd-length); and [the higher odd contents are excluded in the all-length theorem](ODD-PI-TJ-ALL-LENGTHS.md).

The [all-length theorem](ODD-PI-TJ-ALL-LENGTHS.md) now proves the exact two-branch formula \(\Delta_N=\min(P_N,\lambda_{\min}(M_N))\) in this entire odd \(\pi\)-twisted regime. The perturbation results below explain the limiting mechanisms independently; their earlier restrictions are not the scope of the final formula.

## One-hole gauge and finite matrix

Use the basis \(X,Y,h\) and two-site blocks of the [preceding proof](DEFORMED-TJ.md). A mixed particle bond \(XY,YX\) has diagonals \(c-2\zeta,c+2\zeta\), respectively, and swap entry \(+t\). Particle–hole bonds have diagonal \(c\) and hop amplitude \(-t\); at the \(\pi\) seam the hole swap changes to \(+t\). Hole number and particle content are conserved.

In a one-hole sector with \(k\) spins \(Y\) among the \(L\) particles, fix a linear ordering at the seam, delete the hole, and multiply each configuration by \((-1)^{I}\), where \(I\) counts \(X/Y\) inversions. For an ordinary particle swap the parity changes once. For an unlike particle swap across the seam it changes by \(L-1\), odd; this follows because the two endpoints pass all the internal particles of opposite type plus each other. Thus all particle swaps become \(-t\). Ordinary hole hops do not change the order. When the hole crosses the seam, the particle order rotates by one, moving either an \(X\) across \(k\) opposite letters or a \(Y\) across \(L-k\), the same parity as \(k\), since \(L\) is even. For odd \(k\), this cancels the seam sign, so every off-diagonal entry is nonpositive. The configuration graph is connected by first moving the hole and then sorting by particle swaps in an open segment. The matrix in this gauge is invariant under ordinary spatial translation: the bond diagonals repeat by orientation, and all swap signs now agree. By Perron–Frobenius (applied to a large scalar minus the Hamiltonian), the lowest vector is strictly positive and unique, hence translation invariant in this gauge.

Read the relative particle word \(s=(s_1,\ldots,s_L)\) beginning after the hole, where \(s_i={\bf1}_{Y}\). Let \(w(s)\) count the unequal bonds inside the open word and \(d(s)=s_1-s_L\). On words of fixed \(k\) the relative Hamiltonian is
\[
t A_k+4+2w(s)+2\zeta d(s).
\]
Here \(A_k\) is the graph Laplacian from all open-word adjacent unequal swaps and from the two cyclic shifts (one for each hop direction). Multiple edges count. The diagonal of the full Hamiltonian in these coordinates is \(2c+cw+2\zeta d\), and the Laplacian diagonal is \(t(2+w)\); their difference is \(4+2w+2\zeta d\). The sole one-hole no-hop transitions would come from constant relative words, absent at odd \(k\). For \(k=1\), each interior path edge gets one adjacency swap and one hop, while the closing edge gets only the hop. Thus \(A_k=A_1\) as specified, with one-wall endpoints and two-wall interior states. Uniform constant coordinates have expectation \(8-4/L\) at \(k=1\), proving the all-coupling upper bound.

### Exact one-hole reduction at all couplings

The [circular exclusion cycle partition](CIRCULAR-EXCLUSION-CYCLES.md) shows all mixed no-hole sectors have least energy at least \(P_N(t)\) at every \(t>0\). Pure one-hole waves attain that value, and the one-hole trial of energy at most \(8-4/L\) is strictly below the many-hole lower bound \(8\). Thus restrict the comparison to the one-hole sectors.

The inversion gauge described above uses only the seam sign of the hole when distinguishing even and odd \(k\); its particle swaps are \(-t\) in both cases. Consequently a Fourier transform in hole position reduces each \(k\) to relative-word matrices of order \(\binom{L}{k}\). In each block:
* The diagonal potential is \(c(2+w(s))+2\zeta d(s)\).
* Each allowed adjacent unlike swap within the relative word contributes \(-t\).
* A clockwise or counterclockwise hole hop contributes \(-t e^{iq}\) or \(-t e^{-iq}\), respectively, multiplying its one-step rotation of the word. Sum coincident transitions, including from a rotation that fixes the word.

Here \(q=2\pi j/N\) for odd \(k\), and \(q=(2j+1)\pi/N\) for even \(k\), \(0\le j<N\). In fact writing the wave at hole position \(h\) as \(e^{iqh}f(s)\) represents the periodic or antiperiodic seam by \(e^{iqN}=+1\) or \(-1\), respectively; a clockwise hop cyclically shifts the relative word in one direction and a counterclockwise hop reverses that shift. The sign assignment uses \(L\) even, so the inversion change when a seam hop rotates the word has parity \(k\) irrespective of which spin moves. For odd \(k\), only \(q=0\) need be tested by Perron–Frobenius. At \(k=0,L\) this formula gives \(P_N\) as its least value. This gives an exact block expression for all couplings but not a closed comparison of its competing mixed-content eigenvalues.

### Two even-content momentum blocks excluded exactly

In even mixed content \(0<k<L\), the blocks \(q=\pm\pi/N\) are strictly above \(P_N(t)\) at every \(t>0\). Indeed write
\[
H_k(q)=4I+S_k+t(2I-e^{iq}R-e^{-iq}R^{-1}),
\]
where \(S_k\) is the sum of positive semidefinite particle-bond blocks on the open word in the inversion gauge, and \(R\) is the cyclic shift. Since \(R^L=I\), and \(|q|=\pi/N<\pi/L\), the nearest rotation phase to \(-q\) is zero. The hopping term is therefore bounded below by \(2t(1-\cos(\pi/N))I\) with equality only on \(R\)-invariant vectors. The kernel of \(S_k\) is a single line whose nonzero amplitude ratios are fixed by adjacent unlike swaps, giving the positive inversion-weighted vector with ratio \((\zeta-1)/(\zeta+1)\) or its reciprocal. Its magnitudes change upon rotating a first letter past a nonzero number of opposite letters, because the ratio does not have modulus one. Thus this line is not \(R\)-invariant and equality in the sum is impossible. The other even-content momenta are not excluded by this argument.

### Uniform analytic interval for even mixed contents

The even mixed blocks are all bounded below by \(P_N(t)\) for every odd \(N\ge5\) when
\[
t\le \frac{4}{\alpha_0(1+2/\cos\theta)},\qquad
\theta=\pi/N,\quad \alpha_0=2(1-\cos\theta).
\]
In particular this holds whenever \(\alpha_0t\le1\). This does not yet exclude the odd mixed contents. To prove the claim, use the [kink rank-one comparison](ODD-PI-TJ-FINITE-CERTIFICATES.md#even-mixed-sectors), with \(g=4+\gamma t\), \(\gamma=2(1-\cos(\pi/L))>\alpha_0\).

For a nontrivial rotation phase, the kink overlap \(p\) is at most \(1/2\): nonreal phases come in conjugate pairs of equal squared overlap, and on a rotation orbit contributing at phase \(-1\), the squared projection is \((\sum_{\mathrm{even}}\phi-\sum_{\mathrm{odd}}\phi)^2/\ell\), for even orbit length \(\ell\). Nonnegativity of the entries bounds its numerator by the larger squared half-sum, and Cauchy–Schwarz bounds that by \(\ell/2\) times the norm squared on the orbit. Summing proves the claim. The rank-one condition with \(p\le1/2\) therefore follows from \((c-b)(\gamma+4/t)\ge2bc\), with \(b,c\) the kinetic deficiency and next gap as in the linked note; it also requires \(g>bt\), immediate since \(b\le\alpha_0\).

Write the closest angle as \(\theta-s\) with \(0<s\le\theta\); the next closest angle is \(2\pi/L-(\theta-s)>\theta+s\). Thus \(c\ge c_0=2(\cos\theta-\cos(\theta+s))\), while \(b=2(\cos(\theta-s)-\cos\theta)\). The difference of reciprocals obeys
\[
\frac{c-b}{bc}\ge \frac1b-\frac1{c_0}
=\frac{\cos\theta}{2(\sin^2\theta-\sin^2(s/2))}
\ge\frac{\cos\theta}{\alpha_0(1+\cos\theta)}.
\]
With \(\gamma\ge\alpha_0\) the displayed upper bound on \(t\) is sufficient. The two smallest antiperiodic momenta were already treated separately.
 
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

## A uniform weak-to-moderate coupling interval

By exchanging \(X,Y\) take \(\zeta=\sqrt{1+t}>0\). Take odd \(N\ge5\) and \(0<t\le1\), and write \(P=4+\alpha t\), with \(\alpha=2(1-\cos(\pi/N))<2/5\). We prove that every block apart from the one-flip and pure-background one-hole waves is bounded below by \(P\). Blocks with at least two holes have energy at least 8 by the preceding proof, and the two waves attain \(P\).

For the remaining blocks, split off the span of certain low-wall configurations and write the matrix as \(\begin{pmatrix}E I&B\\ B^*&D\end{pmatrix}\). If \(D\ge d I\), \(d>P\), and \(\|B\|^2\le (E-P)(d-P)\) with \(E\ge P\), the Schur complement gives \(H\ge P\). To bound \(\|B\|\) it suffices to bound the absolute row and column sums, since their product bounds \(\|B\|^2\) by Cauchy–Schwarz. To bound \(D\), we subtract from the full diagonals the sum of the absolute **full** off-diagonal entries, which is valid also in the compression. These estimates ignore the signs, so they apply even in the frustrated sectors.

**No holes, and each spin count at least two.** Let the low configurations be exactly the two-wall words. Both boundary swaps lead to four walls, so \(E=2c=4+2t\) and the low-to-high absolute row sum is \(2t\). For a high configuration to lead to low by a swap, it must have four walls and the two runs meeting at the exchanged boundary must both have length one. In fact flipping these two adjacent unequal sites leaves their shared wall unchanged and removes the other two walls only if the neighboring symbols on both outside sites are opposite to their respective old symbols. Among four circular runs at most two consecutive run pairs can both be singletons since \(N\ge5\). Thus the absolute column sum is at most \(2t\), and \(\|B\|^2\le4t^2\). All high words have full diagonal minus absolute off-diagonal sum at least \(2w\ge8\). Hence \((E-P)(d-P)\ge (8/5)t(18/5)>4t^2\).

**One hole, with both spin types.** Use the relative word after the hole and put \(a=\#X\), \(b=\#Y\). Take \(X^aY^b\) at every hole position as the low configurations. The matrix on them is \(E I\) with \(E=4+2t+(\zeta-1)^2\): the sole particle swap and both hole moves leave the low set. For a high word with \(w\) open walls and \(d_0=s_1-s_L\), its diagonal minus full absolute off-diagonal sum is \(4+2w+2\zeta d_0\). This is at least \(8\) for even \(w\) (necessarily \(w\ge2,d_0=0\)) and at least \(6+2\zeta\) for the non-low word with one wall. For odd \(w\ge3\) it is at least \(10-2\zeta\).

If \(a,b\ge2\), the three possible relative words reached from low have the explicit forms \(X^{a-1}YXY^{b-1},\,YX^aY^{b-1},\,X^{a-1}Y^bX\). They are distinct. Each move type from a prescribed hole position has a specified new hole position, either unchanged or shifted by one. Consequently any high configuration is adjacent to at most one low configuration. The bound is \(\|B\|^2\le3t^2\); use \(d\ge10-2\sqrt2>7\). Then \((E-P)(d-P)>(8/5)t(13/5)>3t^2\).

If one of \(a,b\) equals one, the other is at least three. Among the three written outputs the two rotations are distinct, so each high configuration is adjacent to at most two low configurations and \(\|B\|^2\le6t^2\). There are no words with three or more open walls, so \(d\ge8\). Using \((\zeta-1)^2/t=t/(\sqrt{1+t}+1)^2\ge t/6\), the Schur product divided by \(t\) is at least
\[
(8/5+t/6)(4-2t/5)=32/5+(2/75)t-t^2/15>6.
\]
This beats \(6t\). The stated uniform interval follows.

## Three sites

At \(N=3\) there are no other mixed no-hole sectors, and the odd-\(k\) one-hole sector has only \(k=1\). Its size-two matrix has diagonal \(3c\pm2\zeta\) and off-diagonal \(-3t\), so its smallest eigenvalue is \(3c-\sqrt{4\zeta^2+9t^2}\). The other one-hole or one-flipped candidates give \(\zeta^2+3\). Multiple holes have bound \(8\), whereas the size-two branch is at most \(6\) by the constant trial. Equating the two candidates for \(u=\zeta^2>1\) gives \(4u+9(u-1)^2=4u^2\), or \((5u-9)(u-1)=0\), and the smaller branches are as stated.

The [independent numerical checker](verify-odd-pi-gap.js) uses untransformed Hamiltonian blocks. It is supplementary and not part of the proofs. For related (distinct) periodic exclusion spectra see [Nakerst–Prosen–Haque](https://arxiv.org/abs/2402.00662); no priority claim is made.


## Five sites: exact two-branch formula and crossover

Take \(\zeta>1\) without loss, and \(L=4\). The only mixed even content is \(k=2\); the odd contents \(k=1,3\) have the same smallest energy, given by the four-dimensional one-minority matrix \(M(t)\) stated above. The \(k=0,4\) sectors supply \(P_5(t)\). By the one-hole reduction it suffices to prove the \(k=2\) blocks are all at least \(P_5(t)\).

Put \(\alpha=2(1-\cos(\pi/5))=(3-\sqrt5)/2\). By the [finite kink gap of Koma–Nachtergaele, Proposition 2](https://arxiv.org/pdf/cond-mat/9512120#page=8), the open spin operator satisfies \(S_2\succeq g(I-|\phi\rangle\langle\phi|)\), with \(g=4+(2-\sqrt2)t\) and \(\phi\) its normalized kink vector. To see the normalization, their Hamiltonian (1.1) scaled by \(2c\), with anisotropy \(\Delta=c/t\), has off-diagonal \(-t\) on unlike swaps and diagonal \(c\) on unlike bonds plus the telescoping boundary field of strength \(c\sqrt{1-(t/c)^2}=2\zeta\) (use reflection for the opposite orientation). Its gap formula becomes \(2c-2t\cos(\pi/4)\). The fixed-content kernel line was described above.

It remains to test \(q=\pm3\pi/5,\pi\), because \(q=\pm\pi/5\) were already excluded. Write \(a_q(R)=2I-e^{iq}R-e^{-iq}R^{-1}\). In each of the remaining blocks there is exactly one rotation eigenphase at which \(a_q<\alpha\). Let \(b=\alpha-a_{\rm bad}>0\), \(d=\min_{\rm other}(a_q-\alpha)>0\), and let \(p\) be the squared norm of the projection of \(\phi\) to the bad eigenspace. From the lower bound for \(S_2\), it suffices that
\[
gI+t(a_q-\alpha)-g|\phi\rangle\langle\phi|\succeq0.
\]
Its first two terms give a positive definite operator (since \(g>bt\)). Conjugating by the inverse square root of that operator reduces the sufficient condition to \(g(p/(g-bt)+(1-p)/(g+dt))\le1\), or
\[
p\le \frac{d}{b+d}(1-bt/g).
\]
At \(q=\pm3\pi/5\) the bad rotation eigenvalue is one of \(\pm i\), \(b=\alpha-2(1-\cos(\pi/10))<1/3\), and \(d=1\). At \(q=\pi\) it is \(-1\), \(b=\alpha\), and \(d=2-\alpha\). The bound on \(b\) at \(q=\pm3\pi/5\) follows from \(\alpha<2/5\) and \(\cos(\pi/10)<29/30\). There \(2-\sqrt2>1/2\) gives a threshold \(>(1-2/3)/(1+1/3)=1/4\). At \(q=\pi\) use \(2-\sqrt2>7/12\), \(\alpha<2/5\), and \(b+d=2\) to obtain a threshold \(>(4/5)(1-24/35)=44/175>1/4\).

For the projection, take \(\nu=(\zeta-1)/(\zeta+1)\); the kernel amplitudes are proportional to \(\nu^{\mathrm{inv}}\) up to reversing the order, which does not change the projection norms here. The contiguous rotation orbit has amplitudes \((1,\nu^2,\nu^4,\nu^2)\), and the alternating orbit has \((\nu,\nu^3)\), with total squared norm \(Z=1+\nu^2+2\nu^4+\nu^6+\nu^8\). On a bad \(\pm i\) the squared projection before normalization is \((1-\nu^4)^2/4\). For bad \(-1\) it is \((1-\nu^2)^4/4+(\nu-\nu^3)^2/2=(1-\nu^2)^2(1+\nu^4)/4\). Both are at most \(Z/4\), using \(0<\nu<1\). This proves the needed strict estimate on \(k=2\). In particular \(\Delta_5(t)=\min\{P_5(t),\lambda_{\min}(M(t))\}\).

For the crossover let \(u=2-\alpha=(1+\sqrt5)/2\). In the symmetric and antisymmetric bases for reflection of the four-site relative word, each parity block has an endpoint and an interior coordinate. After subtracting \(P_5(t)\) the two interior diagonals are \(4+ut,4+(u+4)t\), both positive; both endpoint-to-interior entries are \(-2t\). The parity endpoint diagonals are \(2+ut,2+(u+2)t\), with off-diagonal \(2\zeta\) between them (sign irrelevant). Eliminating the interiors, the resulting two endpoint diagonals are
\[
U=2+ut-\frac{4t^2}{4+ut},\qquad
V=2+(u+2)t-\frac{4t^2}{4+(u+4)t}.
\]
Here \(V>0\) for \(t\ge0\). Multiplying \(UV-4(1+t)\) by the two positive denominators gives \(t\) times
\[
64u+(144u-16)t+(56u-4)t^2-(9u+8)t^3.
\]
The cubic has one sign change and hence exactly one positive root (it is positive at zero and tends to \(-\infty\)). Below that root \(M(t)-P_5(t)I\) is positive definite by the Schur complement, at it the lowest eigenvalue is \(P_5(t)\), and above it the determinant sign gives a negative direction. This identifies the winning branch everywhere.


## Seven sites: exact two-branch formula and crossover

For \(N=7\), \(L=6\), the one-hole content sectors are the pure backgrounds, the one-minority sectors, mixed even \(k=2,4\), and mixed odd \(k=3\). The first two groups give \(P_7(t)\) and the lowest eigenvalue of the six-dimensional matrix \(M_7(t)\). We rule out the last two groups from improving the minimum. The nonlinear polynomial signs below use only exact integer coefficient tests, with a [reproducible checker](verify-seven-site-gap.js).

**Even mixed contents.** By symmetry take \(k=2\). Apply the five-site rank-one reduction with the same normalized kink line \(\phi\) but \(g=4+(2-\sqrt3)t\) from the finite XXZ gap for \(L=6\). Let \(\alpha=2(1-\cos(\pi/7))\). The \(q=\pm\pi/7\) blocks are covered above. For each remaining \(q\), the bad rotation eigenspace (where \(a_q<\alpha\)) has a single eigenphase. For \(q=3\pi/7,5\pi/7,\pi\), the smallest angular distances to a rotation phase are \(2\pi/21,\pi/21,0\), and the next smallest distances are \(5\pi/21,2\pi/7,\pi/3\), respectively. Negative momenta give conjugate phases. For \(b=\alpha-a_{\rm bad}\) and \(d=\min_{\rm good}(a_q-\alpha)\), the threshold \(d(1-bt/g)/(b+d)\) exceeds \(1/5\) in all three cases. For example the elementary cosine bounds \(x^2-x^4/12\le2(1-\cos x)\le x^2-x^4/12+x^6/360\) for \(0\le x\le1\), together with \(3.14<\pi<22/7\), give \(\alpha<199/1000\). For the first two momenta they give \(b<0.12,d>0.3\) and \(b<0.18,d>0.54\), respectively. Using \(2-\sqrt3>0.267\) makes both thresholds \(>1/5\); at \(q=\pi\) the threshold is \(>(1-0.199)(1-0.199/0.267)>1/5\).

For the overlap set \(x=\nu^2\) and \(Z=\sum_w\nu^{2\mathrm{inv}(w)}\) over all fixed-content words. The three nontrivial rotation phase types have arguments \(\pm\pi/3,\pm2\pi/3,\pi\), and the coefficient lists of \(12Z(1-5p_r)\), where \(p_r\) is the squared projection of \(\phi\) on the corresponding eigenspace, are respectively
\[
\begin{split}
&(2,-8,14,44,76,44,14,-8,2),\\
&(2,12,34,24,36,24,34,12,2),\\
&(2,22,14,44,16,44,14,22,2)
\end{split}
\]
in ascending powers of \(x\). Indeed a rotation projector is the character average over the six rotations; multiplying its cosines by 2 yields integers, and rotation changes inversion number by an even integer at \(k=2\). The first list is positive on \([0,1]\) by grouping the two end quadratics \(2-8x+14x^2\) and \(x^6(14-8x+2x^2)\), both positive when their prefactor is nonzero; the rest have positive coefficients. Thus \(p_r\le1/5\) and the even mixed blocks exceed \(P_7\).

**Odd content \(k=3\).** Positivity reduces this sector to \(q=0\). Here the hopping \(2I-R-R^{-1}\) has gap at least 1 above the invariant subspace; let \(\Pi_0\) project onto that subspace. With \(x=\nu\), so \(t=4x/(1-x)^2\), put \(A=15-26x+15x^2\) and \(g=t A/(15x)=4+4t/15\). Since \(2-\sqrt3>4/15\), this \(g\) is a lower bound for the kink gap, and hence
\[
H_3(0)-4I\succeq g(I-|\phi\rangle\langle\phi|)+t(I-\Pi_0).
\]
For \(0<T<\min(g,t)\), the operator on the right exceeds or equals \(TI\) whenever
\[
g t(1-p_0)\ge T(g+t-T),\qquad p_0=\|\Pi_0\phi\|^2.
\]
This follows by the same positive diagonal minus one rank-one operator criterion, splitting into \(\Pi_0\) and its orthogonal complement. Let \(Z=\sum_w x^{2\mathrm{inv}(w)}\) on the 20 words, and \(D=6 Z(1-p_0)=6Z-\sum_{w,j}x^{\mathrm{inv}(w)+\mathrm{inv}(R^j w)}\), with \(0\le j<6\). For \(0<x\le5/8\), take \(T=t/5\), which exceeds \(\alpha t\) and is below \(g,t\). The criterion becomes
\[
p(x)=5AD-6Z(A+12x)>0.
\]
For \(5/8\le x<1\), take \(T=10/3\), again below \(g,t\). It is an upper bound on the excess of \(\lambda_{\min}(M_7)\) above 4 by the constant trial on the one-minority matrix. The criterion now becomes
\[
q(x)=2xAD-ZB(2A+30x-5B)>0,\qquad B=5(1-x)^2 .
\]
For an exact sign certificate, substitute \(x=5y/(8+8y)\) in \(p\) and multiply by \((8+8y)^{20}\); all coefficients are positive. Substitute \(x=(5+8y)/(8+8y)\) in \(q\) and multiply by \((8+8y)^{22}\); the coefficients in degrees 0 through 20 are positive and the two above are zero. These are the integer identities checked by the attached script, which explicitly enumerates each word and its rotations and applies the binomial expansion. For \(x=5/8\) the second certificate applies at \(y=0\). This proves \(H_3(0)\) is strictly above at least one of the two candidate branches at every coupling.

**Unique crossover.** Write \(a=2\cos(\pi/7)\), so \(a^3=a^2+2a-1\) and \(1<a<2\). In the even and odd reflection bases, the two tridiagonal blocks of \(M_7(t)-P_7(t)I\) have diagonals
\[
(2+at,\,4+(a+2)t,\,4+at),\qquad
(2+(a+2)t,\,4+(a+2)t,\,4+(a+4)t)
\]
and subdiagonal \(-2t\). Their two endpoint coordinates are joined by \(2\zeta\) up to sign. The interior \(2\)-by-\(2\) blocks are positive since their diagonal entries are positive and the determinant coefficients are respectively \((16,8+8a,-4+2a+a^2)\) and \((16,24+8a,4+6a+a^2)\) (here \(a>9/5\)). The determinant of the odd isolated \(3\)-by-\(3\) block has positive coefficients \((32,80+32a,40+52a+10a^2,-9+14a+9a^2)\), so its effective endpoint diagonal is positive. Expansion using the minimal polynomial gives the determinant of the whole matrix as \(t\) times the quintic with coefficients
\[
(1024a,\,-1024+2560a+1280a^2,\,-2688+1792a+3200a^2,\,
-1888+288a+2208a^2,\,-188+68a+272a^2,\,-6+43a-51a^2)
\]
in ascending order. Its signs are \(+,+,+,+,+,-\). Descartes and continuity give exactly one positive root. The Schur complement has a positive odd endpoint diagonal, so the determinant sign decides whether \(\lambda_{\min}(M_7(t))\) is above or below \(P_7(t)\), with equality at the root. This establishes the full seven-site claim.
