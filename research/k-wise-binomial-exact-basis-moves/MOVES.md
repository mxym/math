# Exact single-site and simultaneous moves of optimal bases

Consider the Berend–Ernst–Kontorovich–Kumar (BEKK) count moment problem with even 2≤k=2m≤n−2, and its consecutive positive-length phases in 0<p<1. At every transition there are distinct sites t₁,…,tᵣ such that the left basis loses exactly those sites and the right basis adds exactly t₁+2,…,tᵣ+2. All these 2r sites are distinct. In the paired decomposition each {tᵢ,tᵢ+1} changes to {tᵢ+1,tᵢ+2}, and every other pair stays fixed.

This proves BEKK's simultaneous-replacement Conjecture 5.5 and the single-departure move described in their Conjecture 5.4 in the range k≤n−2. It does not estimate what fraction of breakpoints are exceptional. The general §5 setup also mentions k=n−1: this boundary has a different single-departure move for k≥4, described below. The theorem concerns phase changes, not all isolated feasible bases or general rationality of breakpoints.

## Proof

Set N=n−1, q=N−k≥1, and let p be an interior transition. We use the following facts from the [phase-order theorem](../k-wise-binomial-optimal-bases/PROOF.md). Each phase basis has a distinguished count n and k other sites in adjacent pairs. At a transition the two bases share the same positive reduced quadrature on {0,…,N}, of mass vₛ at s. It matches the moments of the binomial masses πₛ=binom(N,s)p^s(1−p)^(N−s) through degree k−1. Write H={s:vₛ>0}, T={0,…,N}∖H. In the left basis every upper member of a pair is positive; in the right every lower member is positive. A maximal consecutive run [u,v] of H with even length tiles identically by pairs in both bases. An odd such run is tiled with u−1 on the left and v+1 on the right. In particular no odd run touches 0 or N. There are exactly r=k−|H| odd runs; r≥1 at a transition of distinct phases.

**An alternating polynomial.** Put z=p/(1−p). There is a real polynomial P of degree at most q such that, on the entire grid,
  
  vₛ=πₛ [1−P(s)/(−z)^s].                                      (1)

Indeed the sequence πₛ−vₛ annihilates polynomials of degree at most k−1. The space of all such sequences has dimension N+1−k=q+1 by the Vandermonde rank. Every sequence (−1)^s binom(N,s)R(s), deg R≤q, belongs to the space, since the Nth finite difference of a polynomial of degree ≤q+k−1=N−1 is zero. These sequences form a space of dimension q+1 by evaluation injectivity. This proves (1) on dividing R by (1−p)^N. In particular P(t)=(−z)^t for all t∈T, and P(s)/(−z)^s<1 for s∈H.

List T in increasing order. Consecutive t<t' have the same parity precisely when the H-run strictly between them is odd. This is a bijection by the endpoint observation, so exactly r consecutive gaps have agreeing signs of P at their ends. On the others there are exactly |T|−1−r=(N+1−k+r)−1−r=q sign changes. Hence P has degree exactly q, with q distinct real simple roots, one in each of these open sign-changing gaps and none elsewhere.

**Contacts are isolated pairs at distance two.** On any root-free interval define L(x)=log|P(x)|−x log z. For roots ρ₁,…,ρ_q,
  
  L''(x)=−Σⱼ (x−ρⱼ)^(−2)<0.                                    (2)

For a same-parity gap t<t', L(t)=L(t')=0 and the whole closed interval is root-free. If t'≥t+4, the intermediate site s=t+2 is in H, has the same parity, and P(s) has the same sign as (−z)^s. Thus (1) requires L(s)<0, contrary to strict concavity. Every same-parity gap therefore has t'=t+2. Moreover, two successive gaps cannot both have equal endpoint parity. If t,t+2,t+4 were three consecutive such contacts, their entire span would be root-free but L would vanish at all three, again contrary to (2).

All odd H-runs are therefore singletons t+1. Across that run the old pair {t,t+1} changes to {t+1,t+2}; other runs with even length do not change. No two odd runs use the same exterior partner, because this would require two successive same-parity gaps just excluded. All exterior partners lie outside H, so no even run can use them. This proves the exact site-transfer theorem.

**Phase count.** Let b be the number of positive-length phases and rⱼ the number of departures at each of the b−1 transitions. The first basis has starts 0,2,…,k−2 and the last has starts n−k,n−k+2,…,n−2, as in BEKK Theorems 2.2–2.3. The sum of the ordered starts increases by exactly rⱼ at transition j, hence
  
  Σⱼ rⱼ=m(n−k),      b=1+m(n−k)−Σⱼ(rⱼ−1).

In particular the equality statement of BEKK Proposition 5.8 when there are no exceptional transitions now follows unconditionally. This counts extra simultaneous moves, not the arithmetic nature or frequency of the locations.

## Boundary k=n−1

Here N=k is even and q=0. A paired J of size N omits precisely one even site e: the sites on either side of the omission must have even lengths in order to tile the grid by pairs. By the same finite-difference calculation, (1) holds with P constant; vanishing at e requires P=z^e. All odd weights are positive. At even s the weight is πₛ(1−z^(e−s)), so a basis is feasible precisely when z^e is the minimum of z^s over even s. The one positive-length phase for p<1/2 thus omits N, and the one for p>1/2 omits 0. At 1/2 all such bases are feasible and H is exactly the odd sites. The actual single-site replacement is 0→N, which is a +2 move only for N=2. The ordered starts nevertheless all advance by one, in agreement with the previous phase-order theorem. No exceptional point in the sense of two or more actual departures occurs at this boundary.

BEKK's tested ranges and Proposition 5.8 assume n≥k+2. Their Conjecture 5.4's introductory quantifier about the number of breakpoints is not a precise frequency target for the present proof; we establish what happens whenever just one site departs and separately identify the k=n−1 boundary.
