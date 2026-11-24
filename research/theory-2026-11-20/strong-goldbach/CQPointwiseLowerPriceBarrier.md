# Pointwise obstruction to the lower-price-only positive-receiver plan

Written research note, 2026-11-24. Use the [audited fixed-target CQ setup](CQCompleteNegativeReceiver.md) and the variables \(Y\), \(K_\pm\), \(B_N\), ordinary \(y=m(Y)\), \(k_\pm=m(K_\pm)\), \(w=m(T_\beta)\), \(g=m(\Gamma_-)\), and \(c=.125999484645652\). Thus \(k_+-k_-=1-w+g+y\) and \(r_0=.0378\) is the old paid reserve. Write \(p_\pm=B_N(Y,K_\pm)\), \(v=B_N(Y,Y)\), with normalization \(M\). The exact isolated \(Y\) increment is \(\Delta_Y/M=v+2p_--2p_+\). The earlier known lower prices are \(v\ge c y+o(1)\), \(p_-\ge c k_-+o(1)\).

**New pointwise result.** Without making any no-pair hypothesis, on the actual targets
\[
 p_+-\left(c k_-+\frac{r_0+c y}{2}\right)>.08330+o(1).
                                                               \tag{1}
\]
So the previously proposed sufficient positive upper using only the certified known lower prices is not merely too low on a dyadic mean: it fails targetwise in the asymptotic range. This does not say that the exact Y ledger cannot be paid on a no-pair target. It says that any such isolated payment must use additional **actual** negative-pair or both-Y excess, quantitatively
\[
 (p_--c k_-)+\tfrac12(v-c y)>.08330+o(1).                       \tag{2}
\]
The upper on the rest of the exterior is unchanged.

## 1. The real two-tag receiver works when the source least prime is at most N^.40

Retain exactly the old accepted B_0 and C receiver cells and genuine quotient cutoff; their fixed parameters are \(v_1=v_0+.001\le.170\), \(\mathcal B=.499+v_0/2\), \(E=\mathcal B-t_1-v_1\), \(D=N^E\), \(P_+=N^{t_1}\). The original proof is a direct application of [Lichtman, Proposition 5.2](https://arxiv.org/html/2309.08522v1#S5) to the actual physical moduli \(pqd\le N^{\mathcal B}\), residue \(a=N\), with the actual receiver \(q\) in the middle modulus slot. On the source side it first takes the smallest true prime as its Siegel–Walfisz factor, at a dyadic scale \(H_0\); the other genuine source factors are thereby an independently named bounded cofactor coefficient on each rectangular interior source cell. The proof of the source rectangle, its ordinary mass approximation and Mellin handling of the central spatial interval remains the same even for rank two. Rank two here means an actual semiprime product of two distinct true primes, not a sieve criterion or a model. The remaining cofactor coefficient needs no SW property. Both source factors have fixed positive floor (use \(\beta\)); the small-source prime is genuinely rough above the analytic subpower \(z_0\) and SW holds on its fixed angular intervals/dyadic subintervals as before. Both orientations again follow by reflecting the real interval.

The former use of rank at least three was the bound \(H_0\ll N^{1/3}\). Replace it by the literal source support \(P^-\le N^{.40}\), which gives \(H_0\ll N^{.40}\) even at the new rank-two source. At \(A_0=H_0 N^{-10^{-6}}\), the factor splits used in the proof remain:
* If \(A_0\ge P_+\), use two-way levels \(A_0/P_+\) and \(DP_+/A_0\) and slots \((p d_1,q,d_3)\).
* If \(A_0<P_+\), use \(A_0,D/A_0\) and slots \((d_1,q,p d_3)\).

In addition to the unchanged \(D>P_+\) and \(A_0>1\), the only previously needed upper on \(H_0\) for these scales is \(A_0\le DP_+\). It holds strictly because
\[
 \log(DP_+)/L=\mathcal B-v_1=.498-v_0/2\ge .4135>.40 .
\]
All powers in Prop. 5.2 remain unchanged: \(Q_1\le A_0\), \(Q_2\in[N^{v_0}/O(1),N^{v_1}]\), \(Q_3\ll N^{\mathcal B-v_1}/A_0\), so the same factor \(H_0/A_0=N^{10^{-6}}\) yields the same checked first inequality and the same three exponent maxima \(.997002,\ 1.895751,\ 1.7839701875\) for the remaining modulus/tested-residue inequalities. The proof's \(H_0<N^{1-\epsilon}\) margin also remains strict. No prime factors are identified across arms, and no shared divisor is imported into the principal: target units and the already verified reciprocal mask error remain valid for these fixed-floor sources. The true receiver cell counts and only their true angular lower amplitudes are unchanged. This proves the same lower \(B_N(U,Y)\ge c m(U)+o(1)\) for nonnegative compact composite \(U\) with actual least factor at most \(N^{.40}\), including rank two.

## 2. Apply it to the actual positive score

Let \(U=K_+1_{\{P^-\le N^{.40}\}}\). This is a genuine nonnegative fixed-floor composite source; prime and squareful inputs have \(H=0\) and the positive score uses the original angular amplitude. The omitted \(K_+\) source has literal least factor \(>N^{.40}\); any three true factors would already have product \(>N^{1.20}\), impossible in the central interval, so its only possible nonzero rank is two. Its ordinary mass is at most
\[
 \int_{.40}^{.50}\frac{du}{u(1-u)}=\log(3/2)<.406
\]
because the exact true rank-two amplitude is \(1-\psi(u)\le1\) on the sorted least widths. The inward/outward own-log versus target-log collars have zero ordinary cost, as before. The bound uses a single sorted density and no factor of two. An outward elementary logarithm bound follows by putting \(z=1/5\) in the positive atanh series: \(2(z+z^3/3+z^5/[5(1-z^2)])<.406\). Nonnegativity on the omitted actual products now gives
\[
 p_+\ge B_N(Y,U)\ge c(k_+-.406)+o(1).
\]
Subtract the proposed sufficient lower-price gate \(c k_-+(r_0+c y)/2\). By the exact mass difference the result is at least \(c(1-w+g+y/2-.406)-r_0/2+o(1)\). Insert the already audited \(-w>.006388,\ g\ge(2/3)(.475)^4,\ y>.3537083851\). Exact rational lower with these numbers is .08330825602868423, establishing (1). From the exact physical payment condition \(p_+\le p_-+(r_0+v)/2\) derive (2). Neither sign rules out higher true negative compensation or coupling with other unestimated sectors.

This is one obstruction to a specific proof path, not a reverse upper for \(p_+\), not a conclusion about the genuine no-pair subsequence, and not a total Goldbach bound. It replaces the need to cite a dyadic counterargument for this particular lower-price-only gate.

Exact replay (Node BigInt):

```js
"use strict";
const Q=(n,d=1n)=>[BigInt(n),BigInt(d)];
const a=([n,d],[m,k])=>Q(n*k+m*d,d*k);
const s=([n,d],[m,k])=>Q(n*k-m*d,d*k);
const f=([n,d],[m,k])=>Q(n*m,d*k);
const div=([n,d],[m,k])=>Q(n*k,d*m);
const lt=([n,d],[m,k])=>n*k<m*d;
const show=([n,d])=>Number(n*10n**15n/d)/1e15;
function ok(p,msg){if(!p)throw Error(msg);}
const dl=Q(4135,10000),u=Q(40,100),v0=Q(169,1000);
const minSlot=s(Q(498,1000),div(v0,Q(2)));
ok(!lt(minSlot,dl)&&!lt(dl,minSlot)&&lt(u,dl),"all receiver physical split levels");
const logUpper=f(Q(2),a(a(Q(1,5),Q(1,375)),div(Q(1,15625),Q(24,25))));
ok(lt(logUpper,Q(406,1000)),"outward log 3/2");
const y=Q(3537083851n,10000000000n),wabs=Q(6388,1000000);
const g=Q(2n*475n**4n,3n*1000n**4n),c=Q(125999484645652n,10n**15n),r0=Q(378,10000);
const central=s(a(a(a(Q(1),wabs),g),div(y,Q(2))),Q(406,1000));
const gap=s(f(c,central),div(r0,Q(2)));
ok(lt(Q(8330,100000),gap),"strict actual pricing gap");
console.log(JSON.stringify({minD_times_Pplus_exponent:show(minSlot),logThreeHalvesUpper:show(logUpper),minimumActualGap:show(gap)}));
```
