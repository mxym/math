# Pay the entire genuinely first-base-covered part of a near-full-prime chamber

This removes the **fixed family** restriction of [the whole cofactor theorem](SmallRadicalShiftedFullPrimeCofactor.md), but not the need to have a real base cover somewhere. The remaining uncovered mass is bounded on the real prime rows but has no adequate signed estimate.

## 1. The actual chamber and results

Let \(P\) be sufficiently large even with \(\operatorname{rad}(P)\le L^B\), \(L=\log P\), and let \(I=PJ\) be fixed interior, \(y=e^{L^\delta}\), \(0<\delta<.1\), \(z=e^{L^{.24}}\). Fix
\[
\tfrac12<\rho<1,\qquad \tfrac14<a<b<\rho/2 .
\]
Take the same \(O(L)\) narrow rectangles of area \(\asymp P\) as in the prior proofs, now with smaller prime \(p\in[P^a,P^b]\). Their source products \(n=pq\) have both primes above \(P^{1/4}\). The complement chamber consists of true
\[
m=P-pq=w r,\qquad r>P^\rho\text{ prime},\qquad m\text{ squarefree},\qquad P^-(m)>y.
\tag{1}
\]
The prime \(r\) is uniquely identifiable. The exact weighted high summand on (1) is \(\lambda(w)\log(pq)\).

Use the full packet grid on \([.105,.195]\) and all its admissible \(K\)-sets, with fixed sufficiently large **even** \(K\), ordered once. Call a row base-covered if \(m\) meets an admissible family, and use the first such family to assign an exact normalized selector. This is the offset \(j=1\) cover only; the true shifted marked budget instead uses the \(j\ge2\) selector.

Denote \(V_y(P)\asymp S(P)L^{-\delta}\). The conclusions are:
1. The whole **base-covered** subchamber has signed sum \(O(PV_y(P)L^{-1.3})\). Its unsigned magnitude is \(\asymp PV_y(P)\).
2. The genuinely base-uncovered absolute weight is \(O(PV_y(P)L^{-1/200})\). Thus the whole chamber has a proved signed bound at that weaker rate, but it is not paid at \(o(PV_y/L)\).
3. Intersect the base-covered subchamber with the actual translated selector across any fixed \(M\ge2\) offsets as in the earlier notes. The marked signed bound is \(O(PV_y(P)(L^{-1.3}+L^{-M/200}))\), sufficient for this subchamber if \(M>200\). In particular all of the base-covered union of (1), not merely a fixed family, is now paid.

## 2. Exact first-base selector is a one-variable residual

Let \(\mathcal B_*\) be the union of all full prime packets. For each admissible family \(H\), \(\mathcal T_H\) is its true tag set. At a true squarefree row \(m=w r\), the prime \(r>P^\rho\) never belongs to a packet. For \(u\in\mathcal T_H\) dividing \(w\), set \(v=w/u\). If \(c_i(v)\) are the packet occupancies of \(v\), then the exact occupancies of \(w\) are \(c_i(v)+1_{i\in H}\), since \(m\) is squarefree. Set
\[
A_H(v)=\frac{1_{\{H\text{ first admissible family in }(c_i(v)+1_{i\in H})_i\}}}
{\prod_{i\in H}(c_i(v)+1)}.
\]
This depends only on \(v\)'s packet primes and \(H\), not on which actual tag primes of \(u\) were chosen. For a fixed row the sum over all \(H,u\mid w\) of these weights is exactly 1 if it is base-covered, 0 otherwise. The product in the denominator is precisely the number of tags for its selected family. Also \(\lambda(w)=\lambda(v)\) here because \(K\) is even.

Thus for each \(H\) the actual signed contribution can be written using the single residual
\[
b_H(h)=\lambda(v)A_H(v)\quad
(h=v r\le P,\ v\text{ squarefree and }y\text{-rough},\
 r>P^\rho\text{ true prime})
\]
as in the previous exact \(\log(pq)\) two-branch model; set it zero if no such decomposition, or when \(h>P\). The decomposition is unique. In the comparison this formula permits a square in \(uv\) if \(u,v\) happen to share a packet prime. This changes the true prime-input contribution only on actual \(m\le P\) divisible by \(\ell^2\) for a packet prime \(\ell\), at total integer count
\[
\sum_{\ell\in\mathcal B_*}\lfloor P/\ell^2\rfloor
\ll P e^{-L^{.105}}.
\]
An \(n=pq\) has a unique short prime and box and fixed \(n\) carries at most \(O_K((\log L)^K L^K)\) choices of \(H,u\), so all true weighted errors remain \(O_A(PL^{-A})\). Conversely \(v\) and \(u\) are each \(y\)-rough, so all allowed outputs satisfy this roughness. In the arithmetic model we may keep the relaxed repeated factors: the real progression and local factors depend only on coprimality with \(uv\), and all its primes exceed \(y\). We have never invoked the projection against a translated tag-dependent residual.

## 3. Actual prime replacements and precise arithmetic model with a variable cofactor cutoff

For each admissible \(H\) and source rectangle, use the genuine prime-centered projected comparison twice, with \(\alpha=w_{\rm pr}-\kappa_z^{-1}R_z\) and its \(1/\log\)-weighted versions (here \(w_{\rm pr}(t)=1_{t\ {\rm prime}}\log t\)). As before the \(\log(pq)\) source amplitude is exactly the sum of the two branches, and the true \(r\) is unaltered. This costs \(O_A(PL^{-A})\), uniformly per \(H\) for sufficiently large fixed \(K\).

Fix \(a_0=uv\). Possible \(v\le P^{1-\rho}\) since \(r>P^\rho\); we can simply sum over all such \(v\). The last-prime endpoint \(P/a_0\) is at least \(P^{\rho-o(1)}\), and modulus \(xd\le P^{b+o(1)}\) remains below the ordinary maximal BV range with a fixed margin since \(b<\rho/2\). Restrict to \((x,a_0)=1\) as forced by the true equation; even if \(v\) shares a prime \(>z\) with \(x\), a previous integer bound \(O(XL/z+L)\) pays removing those \(x\), uniformly at short scale \(X\). The small squarefree roughness modulus \(d\) is on primes \(\le z\) avoiding \(Pa_0\); \(r\equiv Pa_0^{-1}\bmod xd\) is reduced. For each fixed \(a_0\) the \((x,d)\) are recovered from their modulus. All rough tests and the uniform local factor \(S(P)(1+O(L/y+1/z))\) are as in the earlier actual BV calculation.

The additional \(r>P^\rho\) condition just changes one endpoint in the maximal BV step, possibly making an empty interval. After changing variables \(r=(P-xq)/a_0\), its exact indicator is \(P-xq>a_0P^\rho\). In the subsequent pure-integer rough \(x\) count, fix \(q\) in the \(q\)-integral: this indicator restricts \(x\) to a single initial interval, and all earlier uniform prefix and smooth amplitude bounds apply. Thus the signed model is
\[
S(P)\sum_{u\in\mathcal T_H}\frac1u
 \iint_{I_1\times I_2}
 \left(\frac1{\log x}+\frac1{\log q}\right)
 \sum_{\substack{v<V(x,q,u)\\v\ {\rm squarefree},\,P^-(v)>y}}
  \frac{\lambda(v)A_H(v)}
       {v\log((P-xq)/(uv))}\,dx\,dq
 +O_A(PL^{-A}),
\tag{2}
\]
where \(V(x,q,u)=(P-xq)/(uP^\rho)\). The endpoint is polynomial of order \(P^{1-\rho-o(1)}\) but bounded by \(P^{1-\rho}\), uniformly. The prime threshold is strictly \(>\); using strict prefixes throughout does not affect the estimates (one endpoint at polynomial \(v\) has reciprocal \(P^{-(1-\rho)+o(1)}\)). All per-\(a_0\) arithmetic errors apply absolutely after summing by \(\sum_{u,v}1/(uv)\ll L^{1-\delta}\). There is no count-of-\(v\) error in the earlier single-residual comparison.

## 4. Uniform signed reciprocal bounds for every first-family occupancy weight

Write \(\kappa=.04\). The packet count is \(.09\log L/\log4+O(1)\), each full packet has reciprocal mass \(\le1/2\), and hence
\[
\sum_{\ell\in\mathcal B_*}1/\ell\le\kappa\log L+O(1).
\tag{3}
\]
The maximum logarithm of these primes is \(\le 2L^{.2}\). Decompose any squarefree \(y\)-rough \(v=t s\), with \(t\) its exact packet-prime part. Then \(A_H(v)=A_H(t)\), \(0\le A_H(t)\le1\).

Define the unweighted signed \(s\)-prefix
\[
G(X)=\sum_{\substack{s\le X\\p\mid s\Rightarrow p>y,\ p\notin\mathcal B_*}}\mu(s)/s .
\]
Apply the exact reciprocal Möbius convolution from the whole cofactor theorem, now excluding all of \(\mathcal B_*\) and the primes \(\le y\). Its unrestricted inverse Euler mass is \(O(L^{\delta+\kappa})\), by (3) and Mertens. Consequently \(|G(X)|\ll L^{\delta+\kappa}\) for all \(X\), and \(|G(X)|\ll_A L^{-A}\) if \(X\ge e^{L^{.35}}\). The proof is unchanged: inverse-smooth divisors \(d\le\sqrt X\) use the unconditioned reciprocal Möbius bound, those \(d>\sqrt X\) use Rankin with exponent \(L^{-.25}\), since all excluded primes have logarithm \(\le2L^{.2}\). The extra \(L^\kappa\) is consumed by increasing the requested log power.

The signed prefix of the \(v\)-sum with \(A_H\) is
\[
H_H(X)=\sum_{\substack{t\le X\\t\ {\rm squarefree,\ packet\text{-}smooth}}}
  \frac{\lambda(t)A_H(t)}t G(X/t).
\]
Its magnitude for all \(X\) is \(O(L^{\delta+2\kappa})\), since the unsigned \(t\)-reciprocal mass is \(O(L^\kappa)\). For \(X\ge e^{2L^{.35}}\), \(H_H(X)\ll_A L^{-A}\): \(t\le\sqrt X\) uses the strong \(G\)-bound, while \(t>\sqrt X\) is exponentially small by the same Rankin trick and (3). This proof treats all bounded first-family weights together; no sign assumption on either class is used.

In (2), partial summation in \(v\) keeps the actual \(1/\log((P-xq)/(uv))\). Its size is \(O(L^{-1})\) and derivative \(O(1/(vL^2))\) on \(v<V(x,q,u)\). The endpoint term is arbitrary-log small since this endpoint is polynomial. The integral over \(\log v\le2L^{.35}\) is \(O(L^{-2+.35+\delta+2\kappa})\), and the rest is arbitrary-log small. Summing \(\sum_u1/u\asymp1\), \(O(L)\) rectangles with extra \(O(L^{-1})\) source factor, and at most \(O_K((\log L)^K)\) families, we get
\[
\ll PV_y(P)L^{-2+.35+2\delta+2\kappa}(\log L)^K=O(PV_y(P)L^{-1.3}).
\]
The fixed margin holds for all \(\delta<.1\) and \(\kappa=.04\). The unsigned lower bound follows from one fixed full base family in the whole cofactor theorem, using a cutoff \(v\le P^{\eta_0}\) with any fixed \(0<\eta_0<1-\rho\) so the true \(r\)-cut is automatic, and excluding that family's own base packet primes. The unsigned upper bound even for all of (1) follows from the two-affine baseline sieve below.

## 5. Actual uncovered-mass proof and exact obstruction to further use of the comparison

Fix \(p,w\), with \(m=w r\) and \(r>P^\rho\). True rows require \((p,w)=1\), since \(w\) is \(y\)-rough and a target unit. The same two-affine Selberg baseline from [the natural-scale note](SmallRadicalShiftedNaturalScaleReservoir.md) gives at most
\[
O\left(\frac{P S(P)}{p w L^2}+P^{.15+o(1)}\right)
\]
true \(q,r\) on the physical lattice, because the two root densities coincide precisely at target primes except the harmless deleted \(w\)-primes. Its lost local cost is \(\exp(O(L/y))\); \(p,q,r\) exceed the sieve horizon. The floor over \(p,w\) is \(P^{.15+b+(1-\rho)+o(1)}<P^{.9+o(1)}\). Sum source weights via \(\log(pq)\ll L\) and \(\sum_{p\in I_1}1/p\ll1/L\) for each rectangle.

For a base-uncovered row, the greedy witness forces at least \(.04\log L/\log4-O_K(1)\) packet centres empty; there are \(O_K((\log L)^{K-1})\) witness choices. Since \(r\) lies above every packet, the forced emptiness is an exact exclusion on \(w\), not a probabilistic independence claim about \(r\). For each such witness the reciprocal sum of squarefree allowed \(w\le P^{1-\rho}\) is bounded by the unrestricted squarefree product over \(y<\ell\le P^{1-\rho}\) excluding those forced-empty packets. Its upper bound is \(O(L^{1-\delta}\exp(-(\#\text{forced empty})/4))\) up to an absolute factor, since each empty packet has reciprocal mass at least \(1/4\) and \(\sum_{\ell>y}1/\ell^2=o(1)\). Sum the witness polynomial using \(.04/(4\log4)>1/200\). Along with the genuine upper sieve this bounds uncovered weight by \(O(PV_y(P)L^{-1/200})\). Without those exclusions the same computation bounds the whole absolute weight by \(O(PV_y(P))\).

For the optional real shifted selector the fixed-\(p,w\) two-affine upper sieve with offsets \(j\ge2\) applies independently of the base cover condition, and loses at most \(O(PV_y(P)L^{-M/200})\) in absolute weight by the same genuine-root argument. Intersecting with that coverage therefore preserves the paid bound of this note, and its exact unit selector weight.

There is still a genuine missing estimate on the base-uncovered portion. Decomposing by the switched \(u'\mid jP-n\) does not produce the same one-variable residual: the near-full prime and signed cofactor now come from \(m=u'h'-(j-1)P\), not from \(h'\), and cannot be read off from \(h'\) alone. At the most basic \(w=1\) slice, fixing \(p\) yields two true affine primes \(q,r=P-pq\); the upper sieve only gives the ordinary dimension-two size \(O(PS(P)/L)\) across the boxes, which is not below \(PV_y/L\). This is a statement about the insufficiency of these estimates, not a lower bound on this slice or a claim that it cannot be paid by different means.
