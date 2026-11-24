# Tested-modulus obstruction for direct three-/four-tag CQ lower sieving

Written research note, 2026-11-24. The present CQ program needs more actual compensation in \(Y,K_-\) or both-\(Y\). This note tests the next obvious opposite-arm strategy via literal moduli, not bounds on actual no-pair targets. It does not reject signed, switched or differently supported estimates, nor assert that a target's true negative compensation falls short. The [separate note on reflected both-Y](CQReflectedBothYYIncrement.md) contains the actual positive advance.

## 1. Hard ceiling for all three-slot scale choices at the original residue

Work on the original central length \(x\asymp N\), actual residue \(a=N\) and a real source SW factor at scale \(H_0\), whether one opens the left or right original arm. In a direct use of [Lichtman's Proposition 5.2](https://arxiv.org/html/2309.08522v1#S5), literal progression moduli split among scale parameters \(Q_1,Q_2,Q_3\). With \(\theta=7/32\), the first three rails are
\[
 Q_1<H_0/x^\epsilon,\qquad H_0^2Q_2Q_3^2<x^{1-8\epsilon},
 \qquad |a|^\theta H_0Q_1Q_2^5Q_3^2<x^{2-15\epsilon}.
\]
Dropping the fourth only weakens a necessary condition. Set \(\mu=\log H_0/\log N,\ q_i=\log Q_i/\log N,\ B=q_1+q_2+q_3\). Fixed scale constants \(x/N\asymp1\) contribute only \(o(1)\) to exponents, absorbed by a strict margin. The first rail says \(\mu-q_1>\epsilon\). Thus the remaining logarithmic rails require
\[
 2B-q_2+2(\mu-q_1)<1-8\epsilon,\qquad
 \theta+2B+3q_2+\mu-q_1<2-15\epsilon.
\]
It follows that \(q_2>2B-1+10\epsilon\), \(\theta+2B+3q_2<2-16\epsilon\), and
\[
         8B<5-\theta-46\epsilon,\quad B<153/256=.59765625.
\]
This limiting exponent appears from optimizing the known proposition at the original large residue; the new audit is its application to the required genuine CQ factor rank. The ceiling above does not assume a particular choice of SW factor or a fixed set of true tags assigned to the middle slot. It applies even if a general factorization moves additional sieve factors there.

## 2. Consequences for true quotient shapes

Open \(j\) true distinct tags on the actual receiving arm, whose combined target-log angle is \(s\), leaving a quotient of length \(\asymp N^{1-s}\). To use the ordinary positive linear lower, the quotient cutoff \(N^z\) and physical sieve level \(N^E\) need \(E>2z\). To ask that this proposition control the **whole tested level** for the physical modulus (all named tags times the sieve divisor) requires \(B\ge s+E\). Forcing total rank \(\le r\) by product size and roughness alone requires cutoff at least \((1-s)/(r-j+1)\) (allow inward fixed strict collars); below that cutoff an extra factor is geometrically possible. Hence this direct lower-price strategy needs
\[
                  B>s+\frac{2(1-s)}{r-j+1}.
\]
This tests a full-level proof, not proofs that cancel high moduli, use a different sieve, apply another estimate to some moduli, or bound the wrong-rank sector separately.

For \(j=3,r=6\), the needed condition is \(B>(1+s)/2\), which at the original residue contradicts the ceiling as soon as \(s\ge25/128=.1953125\). For \(j=4,r=6\) the requirement \(B>2/3+s/3\) already exceeds the ceiling at \(s=0\). In addition, **at any \(s\)** with three tags and rank-six cap, the combined first rail forces \(q_2> s+10\epsilon\). If the middle slot contains tags of total angle \(b\le s\), it must therefore also contain sieve mass of exponent \(>s-b+10\epsilon\). The old two-tag splitting, with only named prime tags in the middle slot and no such positive-power sieve factor, cannot just be reused. The smaller three-tag cases are not excluded solely by these exponents: \(s=.18,B=.592,q_2=.185,z=.2055\) satisfy the inequalities and all four rails with small fixed \(\epsilon\) and \(H_0/Q_1=N^{2\epsilon}\). That numerical check is not a factorization or estimate for the actual weights.

One may lower the cutoff and allow rank seven. With three tags the positive-count requirement is then \(B>.4+.6s\), still impossible for \(s\ge253/768=.329427\ldots\). At lower sums one cannot merely take the smallest negative amplitude of the enlarged support: rank seven is exactly zero for sharp CQ, since the odd-rank complement identity reduces the sum to seven finite differences of a signed polynomial of degree five. A separately controlled true rank-seven population, or a genuine signed weighting that removes it, is necessary for this route. More specifically, under the ceiling, any positive linear lower with three tags at \(s\ge25/128\) leaves exponent slack for four quotient factors \(1-s-4z>1+s-2B\ge s-25/128\); this angular width is not a lower on the population at any given fixed target.

## 3. Actual CQ support affected

All true squarefree middle rank-five inputs with least angle \(.066<t\le.105\) belong to the genuine negative \(B_0\); any three of their true tags have total \(>.198\). Thus the three-tag rank-six barrier affects their whole ordinary negative mass
\[
 (2/3)\big((1-5(.066))^4-(1-5(.105))^4\big)=.10040304625 .
\]
This is the exact sorted rank-five angular simplex volume times its \(-h_5=1920\prod u_i\) harmonic cancellation, not a count of fixed-target pairs. In the [previously analyzed deep exterior \(D\)](CQExternalRankFiveYBlock.md) case \(v>.170\) (true second tag), the three least sum to \(>.34>253/768\), so even permitting rank seven cannot salvage that subcase by the same positive sieve.

The suggested alternative of putting the **product of the last two true primes** into the source SW slot fails in another actual sector before any discussion of semiprime Siegel–Walfisz. In the true third-rejection rank-five sector of deep \(D\), \(\beta<t\le.04,\ .005<v\le.17,\ w\le(1-t-v)/5\). Its known exact ordinary negative mass is \(.255137824363929\ldots\). The actual last two prime widths sum to
\[
 \log(n)/\log N-t-v-w
 \ge\tfrac45(1-t-v)+O_J(1/\log N)\ge .632+O_J(1/\log N).
\]
If grouped as \(H_0\), this alone violates \(H_0^2Q_2Q_3^2<x^{1-8\epsilon}\) since \(Q_2,Q_3\ge1\). This does not exclude using one last prime individually on a different shape, or a switch to a different source length and actual residue. It identifies the exact obstruction to the proposed transparent terminal-factor transfer on this real band.

The next viable input of this style would need an actual signed cofactor calculation or uniform wrong-rank subtraction after the smaller tags, or different modulus distribution at the true residue/source. No conclusion from these rails about the size of true \(Y,K_-\) or both-Y excess is made.

Exact Node replay:

```js
"use strict";
const Q=(n,d=1)=>{n=BigInt(n);d=BigInt(d);return d<0n?[-n,-d]:[n,d];};
const a=([n,d],[m,k])=>Q(n*k+m*d,d*k), s=([n,d],[m,k])=>Q(n*k-m*d,d*k);
const f=([n,d],[m,k])=>Q(n*m,d*k), div=([n,d],[m,k])=>Q(n*k,d*m);
const pow=([n,d],j)=>Q(n**BigInt(j),d**BigInt(j));
const lt=([n,d],[m,k])=>n*k<m*d, eq=(a,b)=>!lt(a,b)&&!lt(b,a);
const show=([n,d])=>Number(n*10n**16n/d)/1e16;
const ok=(c,m)=>{if(!c)throw Error(m);};
const one=Q(1),theta=Q(7,32),cap=div(s(Q(5),theta),Q(8));
const maxS3=s(f(Q(2),cap),one), maxS3Rank7=div(s(cap,Q(2,5)),Q(3,5));
ok(eq(cap,Q(153,256))&&eq(maxS3,Q(25,128))&&eq(maxS3Rank7,Q(253,768)), "tested level and s bounds");
const b0lo=Q(66,1000),b0hi=Q(105,1000);
const mass=f(Q(2,3),s(pow(s(one,f(Q(5),b0lo)),4),pow(s(one,f(Q(5),b0hi)),4)));
ok(lt(maxS3,f(Q(3),b0lo))&&eq(mass,Q(10040304625n,100000000000n)), "actual B0 rank-five obstructed mass");
const lastTwo=f(Q(4,5),s(s(one,Q(4,100)),Q(17,100)));
ok(eq(lastTwo,Q(632,1000))&&lt(Q(1,2),lastTwo),"actual D last-two SW source rail");
ok(lt(maxS3Rank7,f(Q(2),Q(17,100))),"D upper second-bank shape fails even allowing rank seven");
const sumTags=Q(18,100),B=Q(592,1000),b2=Q(185,1000),z=Q(2055,10000),gap=Q(1,1000000);
ok(lt(div(s(one,sumTags),Q(4)),z) && lt(f(Q(2),z),s(B,sumTags)),
   "small three-tag window is geometrically feasible");
ok(lt(a(s(f(Q(2),B),one),f(Q(10),gap)),b2) &&
   lt(a(a(a(theta,f(Q(2),B)),f(Q(3),b2)),f(Q(16),gap)),Q(2)),
   "first two combination rails for the illustrative exponent point only");
const last=a(a(f(a(Q(2),f(Q(2),theta)),B),f(s(Q(3),f(Q(4),theta)),b2)),
             f(f(a(one,f(Q(2),theta)),gap),Q(2)));
ok(lt(a(last,f(Q(15),gap)),Q(2)), "fourth rail for the illustrative exponent point only");
console.log(JSON.stringify({cap:show(cap),threeTagsRank6:show(maxS3),threeTagsRank7:show(maxS3Rank7),failedB0Mass:show(mass),lastTwoSourceFloor:show(lastTwo)}));
```
