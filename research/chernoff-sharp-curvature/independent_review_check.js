// Independent 352-bit checker for the sharp Chernoff curvature bound.
// Run with node independent_review_check.js . BigInt is used throughout the proof decisions.
// JavaScript Numbers are used for small loop/phase indices (bounded integers) and approximate display only.
const p=352n,D=1n<<p, abs=x=>x<0n?-x:x;
const fl=(a,b)=>{if(b<=0n)throw Error('den');return a>=0n?a/b:-((-a+b-1n)/b)},ce=(a,b)=>-fl(-a,b);
const z=[0n,0n], one=[D,D], Q=(a,b=1n)=>[fl(a*D,b),ce(a*D,b)],I=n=>Q(BigInt(n));
const add=(a,b)=>[a[0]+b[0],a[1]+b[1]],neg=a=>[-a[1],-a[0]],sub=(a,b)=>add(a,neg(b)),min=(...a)=>a.reduce((x,y)=>x<y?x:y),max=(...a)=>a.reduce((x,y)=>x>y?x:y);
const mul=(a,b)=>{const q=[a[0]*b[0],a[1]*b[1],a[0]*b[1],a[1]*b[0]];return [fl(min(...q),D),ce(max(...q),D)]};
const mrat=(a,n,d)=>{if(n<0n)return neg(mrat(a,-n,d));return [fl(a[0]*n,d),ce(a[1]*n,d)]},
inv=a=>{if(a[0]<=0n)throw Error('nonpos');return [fl(D*D,a[1]),ce(D*D,a[0])]},div=(a,b)=>mul(a,inv(b)),
sq=a=>[fl((a[0]>0n?a[0]:a[1]<0n?-a[1]:0n)**2n,D),ce(max(abs(a[0]),abs(a[1]))**2n,D)],
ab=a=>max(abs(a[0]),abs(a[1])),
err=(a,t)=>[a[0]-t,a[1]+t],sgn=a=>a[0]>0n?1:a[1]<0n?-1:0;
const eR=Q(1n,10n**14n)[1];
const gamma=k=>{k=BigInt(k);let t=Q(5n**(k+1n),k+1n),s=z;for(let n=0n;n<560n;n++){s=add(s,n%2n===0n?t:neg(t));t=mrat(t,125n*(3n*n+k+1n),(n+1n)*(3n*n+k+4n))}const tail=Q(3n**125n,3n*8n**125n);return [s[0],s[1]+t[1]+tail[1]]};
const crt=()=>{let n=3n*D**3n/2n,lo=D,hi=2n*D;while(lo+1n<hi){let m=(lo+hi)/2n;if(m**3n<=n)lo=m;else hi=m}return [lo,hi]};
const c=mul(crt(),div(gamma(1),gamma(0)));
function Air(tnum,tden,pureIm){let re=z,im=z,reE=0n,imE=0n;
for(let j=0;j<=1;j++){let t=j?mrat(c,abs(tnum),tden):one;let n=j;
for(;n<=660;n+=3){let phase=(4+ (pureIm?n%4:0)+(j?2:0)+(tnum<0n&&n%2?2:0))%4;
if(phase===0)re=add(re,t);if(phase===2)re=sub(re,t);if(phase===1)im=add(im,t);if(phase===3)im=sub(im,t);
t=mrat(t,abs(tnum)**3n,2n*tden**3n*BigInt(n+3)*BigInt(n+2))}
reE+=2n*t[1];if(pureIm)imE+=2n*t[1];}
return [err(re,reE),err(im,imE)]};
const recip=([r,i])=>{const v=inv(add(sq(r),sq(i)));return [mul(r,v),neg(mul(i,v))]};
const fmta=a=>a.map(x=>Number(x)/Number(D));
if(c[0]<=D/2n||c[1]>=D)throw Error('Airy slope');
for(const v of [1n,-1n])if(Air(v,1n,false)[0][0]<=D/4n)throw Error('real shifts');
let prev=1;for(const v of [4n,6n,8n,9n,11n,12n,13n,14n,16n,17n]){const cur=sgn(Air(-v,1n,false)[0]);if(cur!==-prev)throw Error('brackets');prev=cur;}
// Airy recurrence remainders bounded by two times each first omitted term:
if(32n**3n>=662n*663n)throw Error('geometric ratio');
let fac=[1n];for(let j=1n;j<=164n;j++)fac.push(j*fac[fac.length-1]);let moments=Array.from({length:165},()=>z);
for(let j=0n;j<=512n;j++){let [r,i]=recip(Air(j,16n,true));let u=one;let weight=j===0n?1n:2n;for(let m=0;m<165;m++){let v=[r,i,neg(r),neg(i)][m%4];moments[m]=add(moments[m],mrat(mul(v,u),weight,16n));u=mrat(u,j,16n)}}
let pol=Array.from({length:5},(_,k)=>Array.from({length:161},(_,r)=>mrat(moments[r+k],1n,fac[r])));
const polyval=(a,x)=>{let r=a[160];for(let j=159;j>=0;j--)r=add(mul(r,x),a[j]);return err(r,eR)};
const scale=(a,n)=>mrat(a,BigInt(n),1n);
function evalv(x,der){const A=pol.slice(0,der?5:3).map(row=>polyval(row,x));const ri=inv(A[0]),b=mul(A[1],ri),c=mul(A[2],ri);if(!der)return sub(sq(b),c);const d=mul(A[3],ri),e=mul(A[4],ri),b2=sq(b);return add(add(add(neg(e),scale(mul(b,d),4)),scale(sq(c),3)),sub(scale(sq(b2),6),scale(mul(b2,c),12)))}
const kc=(x,der)=>add(evalv(x,der),evalv(neg(x),der));
const orig=kc(z,false);if(orig[0]<=Q(34051898n,10000000n)[1]||orig[1]>=Q(34051899n,10000000n)[0])throw Error("incorrect origin value");let mind=9999n*D,mindiff=mind,n0=0,n1=0,depthmax=0;for(let j=0n;j<128n;j++){const v=kc([j*D/1024n,(j+1n)*D/1024n],true);if(v[0]<=0n)throw Error("origin convexity "+j);mind=min(mind,v[0]);n0++}
function cover(a,b,depth=0){let k;try{k=kc([a,b],false)}catch(e){if(!String(e).includes('nonpos'))throw e}
if(k&&k[0]>orig[1]){n1++;mindiff=min(mindiff,k[0]-orig[1]);depthmax=Math.max(depthmax,depth);return}if(depth>=20)throw Error("unknown "+String(a)+","+String(b));const m=(a+b)/2n;cover(a,m,depth+1);cover(m,b,depth+1)}
for(let i=1n;i<8n;i++)cover(i*D/8n,(i+1n)*D/8n);
const dec=(v,n=14)=>[fl(v[0]*10n**BigInt(n),D),ce(v[1]*10n**BigInt(n),D)].map(String);
const A=recip(Air(32n,1n,true));let tail=mrat([0n,ab(A[0])+ab(A[1])],2n*37n**10n,5n*32n**5n),alias=Q(2n*32n*(5n+18n**10n)*3n**95n*8n,5n*(8n**96n-3n**96n));
let fa=1n;for(let j=1n;j<=161n;j++)fa*=j;let tr=Q(65n*32n**165n,fa);if(add(add(tail,alias),tr)[1]>=Q(1n,10n**14n)[0])throw Error("excess");
console.log(JSON.stringify({orig_scaled1e14:dec(orig),n0,n1,depthmax,minNear:fmta([mind,mind]),minGap:fmta([mindiff,mindiff]),tail:fmta(tail),alias:fmta(alias),trig:fmta(tr)}));
