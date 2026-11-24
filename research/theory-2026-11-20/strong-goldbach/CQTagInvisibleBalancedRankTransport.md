# A balanced rank-three transport passes every affordable tagged prime-axis test

Written research note, 2026-11-24. The earlier calibrated angular toy's one-unit insertion concentrated in balanced rank two was [excluded by genuine prime/Bombieri–Vinogradov tagged rough counts](CQPrimeTaggedRoughAxisObstruction.md). The construction here is a different explicit **relaxed prime marginal** on actual compact angular shapes. It restores \(+1\) total positive amplitude and count, including \(>.507\) extra near-balanced rank-two count, by placing matching deficits in genuine rank-three angles. It preserves every affordable nonempty tagged rough histogram, including all the new \(q+r\) tests. It does not pair actual integers at any fixed \(N\), does not claim that a no-prime-pair target exists, and leaves the actual signed composite–composite problem unchanged.

## 1. The transport on genuine angular shapes

Use the same ordinary squarefree composite angular law \(\mu\) as the previous prime-axis notes: on each ordered simplex it has harmonic density \(du_1\cdots du_{r-1}/\prod_i u_i\). On a genuine compact balanced rank-three subdomain put
\[
 \mathcal B=\{1/8\le u_1<u_2<u_3<1/2,\ u_1+u_2+u_3=1\}.
\]
Null ties and boundary faces are immaterial. Set \(m=\mu(\mathcal B)\), \(\lambda=(2m)^{-1}\). For each coordinate \(u_i\) define the genuine rank-two daughter \(D_i(u)=(u_i,1-u_i)\); since \(u_i<1/2\), the order is already correct. Use the following signed change of marginal:
\[
  \Delta=\lambda\left(
     \sum_{i=1}^3 (D_i)_*(\mu|_{\mathcal B})
                         -\mu|_{\mathcal B}\right),\qquad
  \nu=\mu+\Delta .
\]
There is a strict elementary directed certificate
\[
 .53361595394968\le m\le .54049918606245,
\]
given below. Thus \(0<\lambda<1\), removing at most the ordinary density on rank three, and the daughters are positive added mass on disjoint rank two. Although the original \(\mu\) is not finite when angles approach zero through all ranks, this change has finite compact support; all count changes and the previously justified signed integrals are well defined.

The genuine signed sharp angular amplitudes satisfy
\[
 h_2(u_i,1-u_i)=1-F(u_i),\qquad
 h_3(u)=1-\sum_iF(u_i),\qquad
 \sum_i h_2(D_i(u))-h_3(u)=2 .
\]
For rank three, all two-angle sums are \(1-u_i>1/2\), so they lie outside the support of the original \(F\), and \(h_3>0\) also follows from its exact \(16u_1u_2u_3(3-5\sum u_i^2)\), since \(\sum u_i^2<1/2\). Each daughter has positive rank-two score and both parent and daughters have true least \(>.123\), within the actual positive block \(P\). Consequently \(\Delta\) adds **exactly one unit** of ordinary count and of \(h\), and exactly one unit of \(P\). In particular the relaxed law still has \(\int h\,d\nu=2\), \(\int P\,d\nu=m(P)+1\), and \(\int Y\,d\nu=m(Y)\). Neither \(Y\) nor any other true negative angular type has been changed.

## 2. Exact cancellation on every affordable tagged rough histogram

An affordable genuine test has a nonempty list of disjoint tag bands \((a_i,b_i]\) and rough floor \(\eta>0\), with \(a_i>\eta\) and \(\sum b_i+10\eta<1/2\). Every used tag has width \(<1/2\), and every such \(\eta<.05<1/8\), so the outer rough condition is true on all parents and daughters in this transport. Every parent has its three visible singleton tags \(u_1,u_2,u_3\), which appear precisely once each across its daughters, whose larger widths are all \(>1/2\). Hence the total value of every singleton tag test is **identical**, pointwise before averaging, on the three daughters and the removed parent. For a test with two or more disjoint bands, any two parent tags sum to \(>1/2\), so they cannot appear simultaneously in the affordable bands; and a daughter only has one tag below \(1/2\). Thus both sides have exactly zero contribution for every such test. There is no finite mesh or error in this moment cancellation, and no choice of the bands or of \(\eta\) has to be fixed in advance. In particular the true below-root \(q+r\) restrictions do not force the extra angular mass to disappear when balanced rank-three tagged deficits are allowed.

The untagged least-factor survival change is also exact:
\[
 \Delta(1_{\{u_{\min}>\alpha\}})
 =\lambda\int_{\mathcal B}
      \bigl(1_{\{u_2>\alpha\}}+1_{\{u_3>\alpha\}}\bigr)\,d\mu .
\]
Indeed the \(u_1\) daughter and the donor have the same least tag. Both remaining daughters have minima \(>1/4\), since \(u_1+u_2=1-u_3>1/2\) and \(u_2>u_1\). Thus the change is \(+1\) for every \(\alpha\le1/4\), and between 0 and 1 for larger \(\alpha\). This retains the ordinary full rough count center, including the ordinary prime unit, at all previously quoted ordinary below-root positive rough lower thresholds; above \(1/4\) it stays below that center for the quoted upper bounds. For other specialized higher-floor constraints not stated in those inputs, no correctness is inferred from this sentence. At the explicit prime high-positive threshold .156, the added moment is nonnegative before averaging: if the parent is above the floor all daughters are above and its score change is 2, while if it is below the floor only nonnegative daughter contributions can survive. The ordinary score at .156 itself exceeds 1.82 by the same ordinary rank-two/three formula already used for \(P\), so the published lower \(1.31\) remains valid. The middle joint .080–.105 test and all genuine negative-tag rebates keep their baseline ordinary moments. The separate scalar \(P\)-prime constraint is met by the same old \(m(P)+1\) choice. These checks are on the prime-axis data only; no composite correlation or joint extension is constructed.

## 3. Density and genuinely high balanced added mass

The sum of the three coordinate pushforwards of the symmetric ordered measure has density
\[
 t\ \mapsto\ \frac1{2t}
 \int_{\max(1/8,\,1/2-t)}^{\min(1/2,\,7/8-t)}
 \frac{dv}{v(1-t-v)}
\]
on \(t\in[1/8,1/2)\). This follows by representing the ordered simplex as the unordered one with \(1/3!\) and summing its three symmetric coordinate pushforwards. Compare to the genuine rank-two density \(1/[t(1-t)]\). The interval of integration is symmetric under \(v\mapsto1-t-v\), so where nonempty the density ratio is \(\log(v_{\max}/v_{\min})\le\log 4<1.5\); if empty it is zero. This bounds **the sum** of the three inserted daughter densities, not each separately. With \(\lambda<1\), the marginal obeys \(0\le d\nu/d\mu<2.5<3.446\) everywhere. In particular all upper constraints that came solely from that compact angular domination are simultaneously respected.

On the original old balanced rank-two band \(.39<t<.5\) the actual added mass of this relaxed law is
\[
 \lambda\int_{\mathcal B}\bigl(1_{\{u_2>.39\}}+1_{\{u_3>.39\}}\bigr)d\mu >.507 .
\]
The exact grid proves the integral \(>.5491409957174\), and the mass upper above gives the comparison after dividing by \(2m\). This is not the old entire \(+1\) insertion supported on that high band; it proves that more than half a unit can actually be restored there with compensating tagged deficits, while still obtaining the full \(+1\) total count and \(+1\) signed amplitude. The unmodeled actual \(Y\)–positive partner cross cannot be priced from these prime-axis data alone.

## Directed arithmetic (standalone Node BigInt)

In each rectangular cell in \((u_1,u_2)\), the third width lies between the opposed endpoints used in the denominator. The upper includes every cell meeting the sorted and cutoff inequalities, and the lower includes only cells wholly inside them. The high count uses only each indicator valid on a full cell; ticks round outward or inward. Thus no numerical quadrature assumption is used.

```js
const G=4000n,Q=10n**14n;
let lo=0n,hi=0n,hilo=0n;
const ceil=(a,b)=>(a+b-1n)/b;
for(let i=G/8n;i<G/3n+1n;i++)for(let j=i;j<G/2n;j++){
 const w0=G-i-j-2n,w1=G-i-j;
 if(w0>G/2n || j>w1)continue;
 hi+=ceil(G*Q,i*j*w0);
 if(i+1n>j||j+1n>w0||w1>G/2n)continue;
 const x=G*Q/((i+1n)*(j+1n)*w1);
 lo+=x;
 hilo+=x*((100n*j>=39n*G?1n:0n)+(100n*w0>=39n*G?1n:0n));
}
if(lo*2n<=Q||hilo*1000n<=1014n*hi)throw Error("mass or high-angle gain");
console.log(JSON.stringify({lo:String(lo),hi:String(hi),hilo:String(hilo)}));
```