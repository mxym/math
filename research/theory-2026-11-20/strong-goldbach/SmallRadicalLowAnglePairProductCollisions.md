# Genuine short pair-product transfers in a broad low-slope sector are globally sparse

Research note, 2026-11-24. This addresses total products of two actual reflected vertices, not just transfers already given by coordinatewise short ratios. The direct cross-clique collision bound is polynomially below the true low-angle intra-clique moment. It does not establish Liouville cancellation or control multi-step quotient-clique closure.

## 1. Actual rows and what counts as a short total-product link

Use the fixed \(G_{23}\) target \(P\), \(L=\log P\), \(\operatorname{rad}(P)\le L^B\), \(I=[uP,vP]=PJ\) with fixed \(0<u<v<1\), \(y=e^{L^\delta}\) for \(0<\delta<.1\), \(z=e^{L^{.24}}\), \(H=L^{3/5}\). Fix \(0<\sigma<\mu<1/4\) (in particular \(\mu=1/5\) is allowed), and restrict actual slopes to true primes in \((P^\sigma,P^\mu]\). The upper cutoff is inside the original \(D=P^{1/2}e^{-H}\). The labeled clique \(k\) has vertices \(m_p=P-pk\) for actual \(pk\in I\), \(P^-(k)>z\), \(P^-(m_p)>y\).

Write
\[
F_{p,q}(k)=(P-pk)(P-qk)
\]
for an unordered **two-distinct-slope** pair. We may require the two reflected vertices to be coprime for the dense core; the sparsity upper bounds below actually hold without that extra restriction. For \(T\le e^H/2\), a short pair-product link from \(k\) to \(k'\) is a physical unordered pair \(p,q\) in \(k\), another unordered pair \(r,s\) in \(k'\), and the unique reduced positive ratio \(a/b\) such that
\[
bF_{r,s}(k')=aF_{p,q}(k),\qquad 1\le a,b\le T,\quad(a,b)=1 .
\tag{1}
\]
No coordinatewise short ratio is assumed, and a common slope alone does not supply one. Complete multiplicativity of actual \(\lambda\) makes this edge's true sign multiplier \(\lambda(a)\lambda(b)\), irrespective of how prime factors are distributed among the two coordinates.

All result statements below count **cross-clique** links \(k'\ne k\); the trivial identical data are not part of that count. We fix an orientation when comparing or counting links. The bound \(T^2P^{4\mu}<P\) and separation \(T<P^\sigma\) both hold for all sufficiently large \(P\).

## 2. Two repeated short links: complete treatment of the shared-slope case

Suppose two different links between the same \(k,k'\) have source unordered slope pairs \(A_1,A_2\), target slope pairs \(B_1,B_2\), and reduced ratios \(a_i/b_i\). Reducing (1) modulo \(P\) and eliminating \(k^2,k'^2\) (they are units by \(P^-(k),P^-(k')>z\) and the small radical) gives
\[
P\mid a_1 b_2\prod_{p\in A_1}p\prod_{p\in B_2}p-
       a_2 b_1\prod_{p\in A_2}p\prod_{p\in B_1}p.
\]
Both positive products are \(<P\), so this is integer equality. The true slope primes all exceed \(T\), while \(a_i,b_i\le T\), so the equality separately identifies the large-prime multisets and the short factors. Thus the ratios are equal (write \(a/b\)), and the signed slope multiplicity differences \(A_1-A_2=B_1-B_2\) agree.

If the source pairs are identical the target pairs are identical, so this was not a second link. If the source pairs are disjoint, the signed multiset equality forces \(B_1=A_1,\ B_2=A_2\): both links preserve their own slope pairs. The remaining possibility is exactly one common slope. Write
\[
A_1=\{p,t\},\quad A_2=\{q,t\},\quad
B_1=\{p,t'\},\quad B_2=\{q,t'\},\qquad p\ne q .
\]
The slope \(t'\) need not equal \(t\). The equality of the two product ratios nevertheless permits **true** cancellation of the shared positive factor \((P-t'k')/(P-tk)\), after which
\[
\frac{P-pk'}{P-pk}=\frac{P-qk'}{P-qk}.
\]
Cross multiplication gives \(P(p-q)(k-k')=0\), impossible. This rules out the shared-slope branch without inferring any coordinatewise short arithmetic ratio.

Consequently whenever there are at least two links, all links between this \(k,k'\) are at the same reduced ratio and preserve their own slope pairs, and the slope pairs are pairwise disjoint. In fact their closed slope intervals are strictly nested: the single-coordinate real positive ratio \(r(p)=(P-pk')/(P-pk)\) is strictly monotone in \(p\) on the common physical interval when \(k\ne k'\), so equal values \(r(p)r(q)\) for disjoint pairs \(p<q\) cannot have both coordinates strictly ordered in the same direction across pairs.

### A further exact limit on a repeated preserving family

If a link preserves \(\{p,q\}\), write
\[
Z=(b k'^2-a k^2)/P\in\mathbb Z,\quad
\Delta=bk'-ak,\quad W=(b-a)P .
\]
The integrality of \(Z\) follows from reducing (1) modulo \(P\) and canceling the true \(pq\), a unit. Expanding the real product gives
\[
Z p q-\Delta(p+q)+W=0,\qquad
(Zp-\Delta)(Zq-\Delta)=ab(k'-k)^2 .
\tag{2}
\]
Here \(Z\ne0\): otherwise \(a/b=(k'/k)^2\), which is greater than one when \(k'>k\) and less than one when \(k'<k\), while the actual same-slope central product ratio has the opposite inequality since both reflected factors are positive and decrease in \(k\). Thus for fixed \(k,k'\) and \(a/b\), each allowed factorization of the nonzero integer \(ab(k'-k)^2\) determines at most one ordered actual slope pair; there are \(P^{o(1)}\) choices by the divisor bound. This bounds all repeated links for each clique pair even though no coordinatewise ratio is assumed.

For reference, the proposed divisibility obstruction for two preserved pairs works for any such \(P\), not only \(P=2^j\). Set \(S_i=p_i+q_i,\ T_i=p_iq_i\). Eliminating \(\Delta\) in \(T_i Z-S_i\Delta+W=0\) gives \(P\mid (T_1S_2-T_2S_1)Z\). Since all the physical preserved slopes at the same clique have scale \(X\asymp_J P/k\) and \(k'\asymp_J k\), we have \(|Z|\ll_J TP/X^2\). Thus \(d=P/\gcd(P,Z)\gg_J X^2/T\gg X\) divides the determinant. In the disjoint-pair notation \(p,q\) and \(r,s\), that determinant is
\[
pqr+[pq-r(p+q)]\,s .
\]
If a solution exists modulo this \(d\mid P\), its bracketed coefficient must be a unit modulo \(d\), because the constant \(pqr\) is a target unit. So at fixed \(p,q,r,d\) at most one integer \(s\) in its physical slope range is possible. This yields an \(O_J(X^3\tau(P))\) bound on candidate slope quadruples in a fixed physical scale for this repeated situation, not a claim that every such candidate exists.

## 3. A global bound for every short pair-product link, without repetition or coordinatewise assumptions

A separate completion of squares gives a stronger count over the whole low-angle band. Fix the four actual slope primes \(p,q,r,s\), with \(p\ne q\), \(r\ne s\), and the short ratio \(a/b\), allowing all cross-slope coincidences. Define
\[
x=2pq\,k-P(p+q),\quad Y=2rs\,k'-P(r+s),\quad A=bpq,\ \ B=ars.
\]
Then (1) is equivalent, for these actual variables, to
\[
A Y^2-Bx^2=P^2\bigl[A(r-s)^2-B(p-q)^2\bigr].
\tag{3}
\]
This follows by writing \(F_{p,q}(k)=(x^2-P^2(p-q)^2)/(4pq)\), and the analogous target identity. The right hand side cannot vanish on any cross-clique link. Indeed if it does, compare valuations **modulo two** at each true slope prime, all \(>T\), in the equality \(bpq(r-s)^2=ars(p-q)^2\). The squares contribute zero parity and the short factors have no such prime. Since \(pq,rs\) are products of two distinct primes, this forces \(\{p,q\}=\{r,s\}\), even if some slopes happened to coincide across the two pairs from the outset. Then \(a=b\), because the slope difference is nonzero, and hence \(k'=k\) by strict decrease of the actual positive central product \(F_{p,q}(k)\). This contradicts the cross-clique requirement.

For every remaining link, multiply (3) by \(A\), set \(U=AY,\ \mathfrak D=AB>0\), and obtain the exact norm equation
\[
U^2-\mathfrak D x^2=N,\qquad
N=A P^2\bigl[A(r-s)^2-B(p-q)^2\bigr]\ne0 .
\tag{4}
\]
All variables and coefficients, as well as their real expressions \(U\pm x\sqrt{\mathfrak D}\), are bounded by a fixed power of \(P\); this follows already from \(k,k'\le P\), the polynomial slope bounds, and \(a,b=P^{o(1)}\). We do not need a bound on the discriminant sharper than this.

Here is a uniform integer-solution count for (4), including the nonsquare case. If \(\mathfrak D\) is a square, factor the left into \(U-\sqrt{\mathfrak D}\,x\) and \(U+\sqrt{\mathfrak D}\,x\); the signed divisor choices of \(N\) give \(O(\tau(|N|))\) solutions. If nonsquare, work in the ring of integers of the real quadratic field \(\mathbb Q(\sqrt{\mathfrak D})\), in which \(\xi=U+x\sqrt{\mathfrak D}\) is an algebraic integer of norm \(N\). The principal ideal \((\xi)\) has norm \(|N|\). By unique factorization of ideals, the number of ideals of norm \(|N|\) is at most \(\tau(|N|)\): above any rational prime there are at most two prime ideals and for a specified norm exponent \(j\) at most \(j+1\) choices. This bound is uniform even if \(\mathfrak D\) is not squarefree and invokes no class-number estimate. For a fixed ideal, any two generators differ by a real quadratic unit. If a unit has real absolute value \(t>1\), the conjugate absolute value is \(1/t\) and its integer trace implies \(t\ge(1+\sqrt5)/2\): equal signs give \(t+1/t\ge3\), and opposite signs give \(t-1/t\ge1\). Distinct absolute values of generators for that ideal are therefore separated by this fixed multiplicative factor; at most two generators share an absolute value. The allowed \(\xi\)'s have \(P^{-C}\le|\xi|\le P^C\) for some fixed \(C\), by the stated upper bounds for both conjugates and \(\xi\bar\xi=N\ne0\). So there are \(O(\log P)\) generators per possible ideal and \(O(\tau(|N|)\log P)=P^{o(1)}\) solutions uniformly. Extra congruence or sign requirements for \(x,Y\) to come from physical \(k,k'\) only reduce this bound, and the formulas are injective for fixed slopes.

There are at most \(P^{4\mu}\) choices of the four slopes (even before imposing true primality in the count), and \(T^2=P^{o(1)}\) choices of reduced ratio. Thus the **entire direct cross-clique short pair-product relation** in this low-angle range, even with arbitrary factor redistribution, has at most
\[
P^{4\mu+o(1)}
\tag{5}
\]
labeled links. For \(\mu=1/5\) this is \(P^{4/5+o(1)}\). With a weight \(k\) or \(k'\), which is at most \(P^{1-\sigma}\), its absolute count is \(P^{1+4\mu-\sigma+o(1)}\). Moreover the preserving-slope subfamily alone needs only two slope labels, so its direct count is \(P^{2\mu+o(1)}\); all repeated links of §2 lie there. Combining with the per-clique-pair \(P^{o(1)}\) multiplicity in (2), even the count of ordered pairs of different parallel links is at most \(P^{2\mu+o(1)}\). These are counts for actual direct relations, not an assumption about signs of the remaining unpaired terms.

## 4. The low-angle arithmetic sector is dense for the genuine weighted target

To compare (5) with [the existing \(G_{23}\) normalization](SmallRadicalWeightedCoprimeDispersion.md) on a genuine region, choose any fixed \(\sigma<u_0<v_0\le\mu\) with \(\log(v_0/u_0)<1\), and take all true primes \(P^{u_0}<p\le P^{v_0}\). On the \(k\)-interval \([vP/P^{v_0},uP/P^{u_0}]\), the actual \(I/k\) interval lies in the entire angular window. Retain \(R_z(k)\) and, if disjoint cliques are desired, require \(k\) to have no prime from that window. On any fixed-factor box for these \(k\)'s the latter deletes at most the relative \(\sum_{p\text{ in window}}1/p=\log(v_0/u_0)+o(1)<1\), by integer rough counts after dividing by each true prime on polynomial quotient scales. This is just a union bound; several such prime factors need not be excluded by an inaccurate exact single-factor assumption.

For fixed genuine \(k\) in this retained region, the true prime-BV normalization from the previous weighted-dispersion result gives unsigned slope mass \(\asymp_J (P/k)V_y(P)/L\), retaining the actual \(R_y(P-pk)\) range. There are \(\asymp \kappa_z L\) harmonic \(k\)-mass across this **positive width** log interval, even after the no-window-prime condition. Thus the actual unequal weighted intra-clique square on this region is of order \(P^2\kappa_z V_y(P)^2/L\); subtracting the diagonal and the old \(O(P^2L/y)\) shared-gcd bill does not change that order. The weighted link count following (5) is polynomially smaller. Hence short direct pair-product transfers cannot pair off substantial low-angle internal mass, although this proof cannot rule out effects from their multi-step closure, from products of taller ratios, or from different arithmetic cancellation mechanisms. No estimate for the signed coprime moment itself is asserted.
