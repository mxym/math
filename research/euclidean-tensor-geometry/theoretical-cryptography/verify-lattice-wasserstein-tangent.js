"use strict";
// Generated fixed-support transport and explicit squared-step gap checks.
let exact=0,numerical=0;
function check(ok,msg,num=false){if(!ok)throw new Error(msg);if(num)++numerical;else++exact;}
function quantileCost(p,q,lambda=1){
 let i=0,j=0,a=p[0],b=q[0],cost=0;
 while(i<p.length&&j<q.length){
   const w=Math.min(a,b);cost+=w*lambda*lambda*(i-j)**2;
   a-=w;b-=w;
   if(a===0)a=p[++i];
   if(b===0)b=q[++j];
 }
 return cost;
}
for(let n=2;n<24;++n)for(let seed=0;seed<80;++seed){
 const a=Array.from({length:n},(_,i)=>1000*(1+((seed+3*i*i+17*i)%23)));
 const perturb=Array.from({length:n-1},(_,i)=>(seed*seed+seed*(i+3)+i*i)%31-15);
 perturb.push(-perturb.reduce((x,y)=>x+y,0));
 const b=a.map((v,i)=>v+perturb[i]);
 check(b.every(x=>x>0),"perturbed masses positive");
 const prefix=perturb.reduce((v,x)=>{v.push(x+(v.at(-1)||0));return v;},[]);
 const d=prefix.reduce((s,x)=>s+Math.abs(x),0);
 for(const l of [1,2,3,5])check(quantileCost(a,b,l)===l*l*d,"exact local relays on a line");
}
{
 const p=[10,0,10],q=[9,0,11];
 check(quantileCost(p,q)===4,"a vacant intermediate site cannot relay");
 const c=[10,10,10],d=[9,10,11];
 check(quantileCost(c,d)===2,"positive intermediate site relays the same signed derivative");
}
let halfMin=Infinity,halfAt=0;
function recurse5(k,s,q){
 if(k===5){
   const y=s+2.5, gap=q-1.25+y*(y-1);
   check(2*gap===Math.trunc(2*gap)&&gap>=.5,"rank-five half-coset dual gap");
   if(gap<halfMin){halfMin=gap;halfAt=s;}return;
 }
 for(let j=-3;j<=3;++j)recurse5(k+1,s+j,q+j*j);
}
recurse5(0,0,0);
check(halfMin===.5&&[-1,-2].includes(halfAt),"saturated lower bound on odd-coset step cost");
function Q4(v){const s=v.reduce((a,b)=>a+b,0);return v.reduce((a,b)=>a+b*b,0)+s*s;}
const v=[1,1,1,1,1], w=[-1,1,1,1,1], e=[2,0,0,0,0];
check(w.every((x,i)=>x+e[i]===v[i]),"actual two-step decomposition");
check(Q4(w)+Q4(e)===22,"exact path cost 11/2");
for(let j=3;j<=100;++j){
 const n=j*j, // lambda=1/j
       Rstar2=j+1;
 // Four times j times the lower bound, with R=R2/2.
 function gap(R2){return 2*j*Math.abs(R2-n)-j*n+R2*(R2-2);}
 const r0=Rstar2+((Rstar2-n)&1),r1=r0-2;
 const opt=Math.min(gap(r0),gap(r1));
 for(let R2=-3*n;R2<=3*n;R2+=2)check(gap(R2)>=opt,"growing-rank closed-form gap");
 const r=gap(r0)===opt?r0:r1,k=(n-r)/2;
 const relaxed4j=2*n*(j+1);
 check(k>=0&&k<=n&&opt>0,"gap attained by one half-coset step plus coordinates");
 check((relaxed4j+opt)/relaxed4j<1.5&&1.5-(relaxed4j+opt)/relaxed4j<2/j,"ratio approaches 3/2");
}
function gaussian(s,N){
 const p=Array.from({length:2*N+1},(_,i)=>Math.exp(-.5*((i-N)/s)**2));
 const z=p.reduce((a,b)=>a+b,0);
 return p.map(x=>x/z);
}
for(const s of [.7,1,1.5,2,4,8,16,32,80,160]){
 const N=Math.ceil(10*s)+2,p=gaussian(s,N);
 let m1=0,m2=0,m3=0;
 for(let i=0;i<p.length;++i){const x=Math.abs(i-N);m1+=x*p[i];m2+=x*x*p[i];m3+=x**3*p[i];}
 const tangent=(m3-m1*m2)/s**3;
 const h=1e-5, q=gaussian(s+h,N);
 const direct=quantileCost(p,q)/h;
 check(Math.abs(direct-tangent)<2e-5,"fixed-width derivative via independent quantile coupling",true);
 if(s>=4)check(Math.abs(tangent-Math.sqrt(2/Math.PI))<.4/s**2,"Gaussian width constant on the line",true);
}
console.log(JSON.stringify({exact,numerical}));

