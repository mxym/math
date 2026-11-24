// Fixed prime-axis perturbation certificate. Run with standard Node.
// All inequality decisions use rationals, not floating binary arithmetic.
function gcd(a,b){a=a<0n?-a:a;while(b)[a,b]=[b,a%b];return a;}
function Q(n,d=1){n=BigInt(n);d=BigInt(d);if(d<0n){n=-n;d=-d;}let g=gcd(n,d);if(!g)throw Error("zero denominator");return [n/g,d/g];}
const dec=s=>{const i=s.indexOf(".");return i<0?Q(s):Q(s.slice(0,i)+s.slice(i+1),10n**BigInt(s.length-i-1));};
const add=([a,b],[c,d])=>Q(a*d+c*b,b*d),neg=([a,b])=>[-a,b],sub=(a,b)=>add(a,neg(b));
const mul=([a,b],[c,d])=>Q(a*c,b*d),div=([a,b],[c,d])=>Q(a*d,b*c);
const pow=([a,b],k)=>Q(a**BigInt(k),b**BigInt(k));
const lt=([a,b],[c,d])=>a*d<c*b,show=([a,b])=>Number(a)/Number(b);
function require(q,w){if(!q)throw Error(w);}
const one=Q(1);
const qp=(...xs)=>xs.reduce((s,x)=>add(s,pow(x,2)),Q(0));
const w2=t=>{const j=sub(one,mul(Q(2),t));return add(sub(one,mul(Q(2),pow(j,3))),pow(j,5));};
const h3Hi=(t0,t1,v0,v1,x0,x1)=>mul(Q(16),mul(mul(t1,mul(v1,x1)),sub(Q(3),mul(Q(5),qp(t0,v0,x0)))));
const beta=dec(".39"),gamma=dec(".61"),aLo=dec(".44");
const z=div(sub(gamma,beta),add(gamma,beta));
require(!lt(mul(Q(2),z),aLo),"log first term");
const densityUpper=add(one,div(one,aLo));
require(lt(densityUpper,dec("3.446")),"uniform source domination on high rank two");
const deltaHi=div(pow(dec(".22"),4),mul(Q(4),mul(beta,mul(gamma,aLo))));
const A=[dec(".13"),dec(".15"),dec(".15"),dec(".18"),dec(".67"),dec(".72")];
const a3=h3Hi(...A), wA=w2(A[0]),gapA=sub(wA,a3);
const massA=div(mul(sub(A[1],A[0]),sub(A[3],A[2])),mul(A[1],mul(A[3],A[5])));
const moveA=mul(gapA,massA);
require(lt(deltaHi,moveA)&&lt(qp(A[1],A[3],A[5]),dec(".6")),"H can be calibrated with positive P reshuffle");
const ratio=div(mul(sub(one,A[0]),sub(A[3],A[2])),mul(A[2],A[4]));
require(lt(add(one,ratio),dec("1.26")),"P replacement density cap");
const D=[dec(".09"),dec(".10"),dec(".29"),dec(".30"),dec(".60"),dec(".62")];
const gapD=sub(w2(D[0]),h3Hi(...D));
require(lt(Q(0),gapD)&&lt(qp(D[1],D[3],D[5]),dec(".6")),"outside P positive toggle");
const R=[dec(".06"),dec(".07"),dec(".200"),dec(".205"),dec(".220"),dec(".225"),dec(".240"),dec(".245")];
const xMin=sub(one,add(add(R[1],R[3]),add(R[5],R[7])));
require(lt(R[7],xMin)&&lt(dec(".17"),R[2])&&lt(R[1],dec(".105")),"genuine untagged ordered rank-five Y patch");
console.log(JSON.stringify({deltaHi:show(deltaHi),moveGap:show(moveA),replacementDensity:show(add(one,ratio)),highDensity:show(densityUpper),outsidePgap:show(gapD)}));
